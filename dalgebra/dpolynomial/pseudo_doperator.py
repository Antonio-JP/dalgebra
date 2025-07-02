from __future__ import annotations

r'''
    Module to create pseudo-differential operators.

    EXAMPLES::

        sage: from dalgebra import DifferentialPolynomialRing
        sage: from dalgebra.dpolynomial.pseudo_doperator import PseudoDOperatorRing
        sage: R.<u,v> = DifferentialPolynomialRing(QQ)
        sage: S = PseudoDOperatorRing(R, "D")
        sage: S
        Ring of pseudo-differential operators over Ring of operator polynomials in (u, v) over Differential Ring [[Rational Field], (0,)]
        sage: S.Di^2 * v[1] * S.D^2 * u[0] == u[0]*v[1] - 2*S.Di*(u[0]*v[2]) + S.Di^2*(u[0]*v[3])
        True
'''

# ****************************************************************************
#  Copyright (C) 2025 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.functions.other import binomial
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex, latex_variable_name
from sage.rings.infinity import Infinity as oo
from sage.rings.integer_ring import ZZ
from sage.rings.rational import Rational
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Mapping, Callable
from .dpolynomial import DPolynomialRing_Monoid, DPolynomial
from ..dring import AdditiveMap, DRings

_DRings = DRings.__classcall__(DRings)

#################################################################################
###
### FACTORY FOR PSEUDO DIFFERENTIAL OPERATORS
###
#################################################################################
GLOBAL_BOUND = 10

def PDOChangeBound(bound: int):
    global GLOBAL_BOUND
    if not bound in ZZ or bound < 0:
        raise ValueError(f"The bound must be a non-negative integer, got {bound}.")
    GLOBAL_BOUND = bound

def CheckBound(func):
    from functools import wraps
    @wraps(func)
    def wrapper(self: PseudoDOperator | PseudoDOperator_Ring, *args, **kwds):
        import inspect
        sig = inspect.signature(func)
        if not "bound" in sig.parameters:
            raise TypeError(f"The method {func.__name__} does not accept a 'bound' argument.")
        elif sig.parameters["bound"].default is not None:
            raise TypeError(f"The method {func.__name__} does not accept a default value for 'bound'.")
        value = kwds.pop("bound") if "bound" in kwds else GLOBAL_BOUND
        
        if not value in ZZ or value < 0:
            raise TypeError(f"The method {func.__name__} requires a non-negative integer 'bound' argument to be passed.")
        
        kwds["bound"] = value
        
        return func(self, *args, **kwds)
    return wrapper

#################################################################################
###
### FACTORY FOR PSEUDO DIFFERENTIAL OPERATORS
###
#################################################################################
class PseudoDOperatorRingFactory(UniqueFactory):
    r'''
        Factory to create the ring of pseudo-differential operators.

        This allows to cache the same rings created from different objects. See
        :class:`PseudoDOperator_Ring` for further information on this structure.
    '''
    def create_key(self, base, name: str, **kwds):
        # We check now whether the base ring is valid or not
        if base not in _DRings:
            raise TypeError("The base ring must have operators attached")
        elif base.noperators() != 1 or not base.is_differential():
            raise TypeError("The given ring must e a differential ring with just 1 derivation.")

        if name in (str(v) for v in base.gens()):
            raise TypeError(f"The given name ({name}) already exist in the base ring.")

        # Now the names are appropriate and the base is correct
        return (base, name)

    def create_object(self, _, key) -> PseudoDOperator_Ring:
        base, name = key

        return PseudoDOperator_Ring(base, name)


PseudoDOperatorRing = PseudoDOperatorRingFactory("dalgebra.dpolynomial.pseudo_doperator.PseudoDOperator")


class PseudoDOperator(Element):
    r'''
        Class representing a pseudo-differential operator.

        A pseudo-differential operator is a Laurent series in the operator `D^{-1}`. They act naturally on elements of a differential ring
        by differentiating when applying `D` and integrating when applying `D^{-1}`. This translates into the following commutation rules
        as operators:
        
        * `D \cdot f = f' + f D`, where `f'` is the derivative of `f`.
        * `D^{-1} \cdot f = \sum_{i\geq 0} (-1)^i f^{(i)} D^{-i}`, where `f^{(i)}` is the `i`-th derivative of `f`.

        This implies that the `pseudo-differential operators are non-finite by nature (left multiplication by D^{-1} produces a possibly infinite
        tail of negative orders). This class handles this infinite tail by storing a method that computes (upon request) the coefficients for any given 
        integer. 

        This class has a clear limitation: computations are usually non exact. For example, the traditional zero-checking can only be performed 
        up to some given order. These methods have an optional parameter ``bound`` that allows to specify the order up to which computations are 
        performed. 
    '''
    def __init__(self, parent: PseudoDOperator_Ring, *, 
                 coefficient_map: Callable[[int],Element] | None = None, 
                 coefficients: Collection[Element] | Mapping[int, Element] | None = None,
                 order_bound: int | None = None
    ):
        base = parent.base()
        
        if coefficient_map is not None and coefficients is not None:
            raise ValueError("You can not provide both coefficient_map and coefficients at the same time.")
        elif coefficient_map is None:
            if coefficients is None:
                coefficients = dict()
            elif isinstance(coefficients, (list, tuple)):
                coefficients = {i: c for i, c in enumerate(coefficients) if c != base.zero()}

            ## Casting everything to the base ring
            coefficients = {k: base(c) for (k, c) in coefficients.items() if c != 0}
            self.__finite = True
            self.__min_coeff = min(coefficients) if len(coefficients) > 0 else -oo
            self.__order_bound = max(coefficients) if len(coefficients) > 0 else -oo
            self.__map = lambda k : coefficients[k] if k in coefficients else base.zero()
        else:
            if order_bound is None:
                raise ValueError("You must provide an order bound when using a coefficient_map.")
            self.__finite = None
            self.__min_coeff = -oo
            self.__map = lambda k : base(coefficient_map(k))
            self.__order_bound = order_bound

        self.__min_computed = None
        self.__cache_computed = dict()

        super().__init__(parent)

    ###################################################################################
    ### Property methods
    ###################################################################################
    @CheckBound
    def is_zero(self, *, bound: int | None = None) -> bool | int: #: Checker for the zero element
        r'''
            Checker for the zero element of the ring.

            This method checks whether the element is zero or not. If exact computation are possible, it returns ``True`` or ``False``.
            Otherwise it returns the last checked order for which the element is zero.
        '''
        order = self.order(bound=bound)
        if order == -oo:
            return True
        elif order > -bound:
            return False
        else:
            return -order

    @CheckBound
    def is_identity(self, *, bound: int | None = None) -> bool | int: #: Checker for the one element of the ring
        if self.__finite:
            order = self.order(bound=bound)

            return order == 0 and self[0] == self.parent().base().one() and all(self[k] == self.parent().base().zero() for k in range(-1, self.__min_coeff-1, -1))
        else:
            order = self.order(bound=bound)

            if order == 0:
                if self[0] == self.parent().base().one():
                    if all(self[k] == self.parent().base().zero() for k in range(-1, -bound-1, -1)):
                        return -bound
            return False

    @CheckBound
    def is_monomial(self, *, bound: int | None = None) -> bool | int:
        if self.__finite:
            return self.order() == self.min_coeff()
        else:
            if self.is_zero(bound=bound) == -bound:
                return -bound
            order = self.order(bound=bound)
            if all(self[k] == self.parent().base().zero() for k in range(order-1, -bound-1, -1)):
                return -bound
            return False

    @CheckBound
    def is_differential(self, *, bound: int | None = None) -> bool | int: #: Checker whether the operator is differential or not (i.e., has no pseudo part)
        if self.__finite:
            return self.__min_coeff >= 0
        else:
            if all(self[k] == self.parent().base().zero() for k in range(-1, -bound-1, -1)):
                return -bound
            else:
                return False
            
    @CheckBound
    def is_pseudo(self, *, bound: int | None = None) -> bool | int: #: Checker whether the operator is pseudo-differential or not (i.e., has no differential part)
        order = self.order(bound=bound)
        return order < 0

    def is_finite(self) -> bool:
        r'''
            Method to check whether the pseudo-differential operator is finite or not.
        '''
        return self.__finite

    @CheckBound
    def all_constants(self, *, bound: int | None = None) -> bool | int:
        r'''
            Checks whether the pseudo-differential operator has all constant coefficients.
        '''
        if self.__finite:
            return all(self[k].derivative() == self.parent().base().zero() for k in range(self.__min_coeff, self.order(bound=bound) + 1))
        else:
            order = self.order(bound=bound)
            if order == -bound: # this means the element is zero up to the bound
                return -bound
            else: # order > -bound
                for k in range(order, -bound-1, -1):
                    if self[k].derivative() != self.parent().base().zero():
                        return False
                return -bound

    @CheckBound
    def order(self, *, bound: int | None = None) -> int:
        r'''
            Method to get the order of a pseudo-differential operator.
        '''
        if self.__finite:
            return self.__order_bound
        else:
            for k in range(self.__order_bound, -bound-1, -1):
                if self[k] != self.parent().base().zero():
                    self.__order_bound = k
                    break
            else:
                self.__order_bound = min(-bound, self.__order_bound)

        return self.__order_bound

    def min_coeff(self) -> int:
        if self.__finite:
            return self.__min_coeff
        else:
            return self.__min_computed if self.__min_computed is not None else 0

    def differential_part(self) -> PseudoDOperator:
        r'''Return a :class:`PseudoDOperator` that contains only the differential part of ``self``'''
        ## It is always finite
        diff_part = {k : self[k] for k in range(0, self.order(bound=0) + 1)}
        return self.parent().element_class(self.parent(), coefficients=diff_part)

    def pseudo_part(self) -> PseudoDOperator:
        r'''Return a :class:`PseudoDOperator` that contains only the pseudo-differential part of ``self``'''

        if self.__finite:
            if self.is_zero() is True:
                return self.parent().zero()
            pseudo_part = {k: self[k] for k in range(-1, self.__min_coeff - 1, -1)}
        else:
            order = self.order(bound=0)
            return self.parent().element_class(self.parent(), 
                coefficient_map=lambda k : self[k] if k < 0 else self.parent().base().zero(),
                order_bound=min(-1, order))

        return self.parent().element_class(self.parent(), dict(), self.__negative)

    def cut(self, min_coeff: int) -> PseudoDOperator:
        r'''
            Return a :class:`PseudoDOperator` that contains only the coefficients with order greater than or equal to ``min_coeff``.

            This method returns a new pseudo-differential operator that contains only the coefficients with order greater than or equal to ``min_coeff``.
            If ``min_coeff`` is greater than the minimum coefficient of the operator, it returns the zero operator.

            This method always return a finite pseudo-differential operator, even if the original one is not finite.
        '''
        coeffs = {k : self[k] for k in range(min_coeff, self.order() + 1)}
        return self.parent().element_class(self.parent(), coefficients=coeffs)

    def lie_bracket(self, other: PseudoDOperator) -> PseudoDOperator:
        if not isinstance(other, self.__class__) or other.parent() != self.parent():
            other = self.parent()(other)

        return self*other - other*self

    def __getitem__(self, key: int) -> Element:
        if self.__min_computed is None or key < self.__min_computed:
            self.__min_computed = key
        if not key in self.__cache_computed:
            self.__cache_computed[key] = self.__map(key)
        return self.__cache_computed[key]

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: PseudoDOperator) -> PseudoDOperator:
        ## Adding the positive parts
        if self.is_zero() is True:
            return other
        elif other.is_zero() is True:
            return self
        
        if self.__finite and other.__finite:
            dict_coeff = {k : self[k] + other[k] for k in range(min(self.__min_coeff, other.__min_coeff), max(self.order(), other.order()) + 1)}
            return self.parent().element_class(self.parent(), coefficients=dict_coeff)
        else: # one is not finite
            add_map = lambda k : self[k] + other[k]
            order_bound = max(self.__order_bound, other.__order_bound)
            ## We check some orders to see if there is simple cancellations
            for k in range(10):
                if self[order_bound - k] + other[order_bound - k] != self.parent().base().zero():
                    order_bound -= k
                    break
            else:
                order_bound -= 10
            return self.parent().element_class(self.parent(), coefficient_map=add_map, order_bound=order_bound)

    def __neg__(self) -> PseudoDOperator:
        if self.is_zero() is True:
            return self
        if self.__finite:
            coeffs = {k: -self[k] for k in range(self.__min_coeff, self.order() + 1)}
            return self.parent().element_class(self.parent(), coefficients=coeffs)
        else:
            neg_map = lambda k : -self[k]
            order_bound = self.order()
            
            return self.parent().element_class(self.parent(), coefficient_map=neg_map, order_bound=order_bound)

    def _sub_(self, other: PseudoDOperator) -> PseudoDOperator:
        return self + (-other)

    def _mul_(self, other: PseudoDOperator) -> PseudoDOperator:
        if (self.is_zero() is True) or (other.is_zero() is True):
            return self.parent().zero()
        elif (self.is_identity() is True):
            return other
        elif (other.is_identity() is True):
            return self
        elif self.__finite and other.__finite and self.is_differential():
            dict_coeff = {
                s : sum(
                    self[k]*sum(
                        binomial(k,i)*other[s+i-k].derivative(times=i) for i in range(k+1)
                    ) for k in range(self.order()+1)
                ) 
                for s in range(other.__min_coeff, self.order() + other.order() + 1)
            }
            return self.parent().element_class(self.parent(), coefficients=dict_coeff)
        elif self.__finite and other.__finite and other.all_constants():
            dict_coeff = {
                s : sum(
                    self[s-l]*other[l]
                    for l in range(other.__min_coeff, other.order()+1)
                ) 
                for s in range(other.__min_coeff + self.__min_coeff, self.order() + other.order() + 1)
            }
            return self.parent().element_class(self.parent(), coefficients=dict_coeff)
        else: # the result is not finite
            p = self.order()
            q = other.order()
            a, b = self, other
            map_coeff = lambda s : sum(sum(binomial(s+i-l,i)*a[s+i-l]*b[l].derivative(times=i) for i in range(p+l-s+1)) for l in range(s-p, q+1))
            return self.parent().element_class(self.parent(), coefficient_map=map_coeff, order_bound=p+q)

    @cached_method
    def __invert__(self) -> PseudoDOperator:
        r'''
            Computes the multiplicative inverse of the pseudo-differential operator.
        '''
        if self.is_zero() is False:
            p = self.order()
            lc = ~(self[p]) # lc != 0 --> this checks if the operation can be performed

            ## Checking for finite cases
            if self.is_monomial() is True:
                if lc.derivative() == 0:
                    return self.parent().element_class(self.parent(), coefficients={-p: lc})
                elif p < 0:
                    D = self.parent().gen()
                    return (D**-p)*lc

            from functools import lru_cache

            @lru_cache(maxsize=256)
            def coeff_inverse(k: int) -> Element:
                if k > -p:
                    return self.parent().base().zero()
                elif k == -p:
                    return lc
                s = k + p # s < 0
                num = sum(coeff_inverse(l)*sum(binomial(l, l+k-s)*self[k].derivative(times=l+k-s) for k in range(s-l, p+1)) for l in range(s-p+1, -p+1))
                
                return -num * lc
            
            return self.parent().element_class(self.parent(), coefficient_map=coeff_inverse, order_bound=-p)

        raise ZeroDivisionError(f"Inverse of (possibly) zero element do not exist: {self}.")

    @cached_method
    def __pow__(self, power: int | Rational) -> PseudoDOperator:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            return (~self)**(-power)
        elif power not in ZZ:
            raise ValueError(f"Power {power} is not an integer, only integer powers are allowed in pseudo-differential operators.")
        else:
            a,A = (self**(power//2 + power % 2), self**(power//2))
            return a*A

    @CheckBound
    def __eq__(self, other, *, bound: int | None = None) -> bool:
        if not isinstance(other, self.__class__) or other.parent() != self.parent():
            try:
                other = self.parent()(other)
            except Exception:
                return False

        try:
            return (self - other).is_zero(bound=bound)
        except TypeError:
            return (self - other).is_zero()

    @CheckBound
    def __ne__(self, other, *, bound: int | None = None) -> bool:
        equals = self.__eq__(other, bound=bound)
        if equals is True:
            return False
        elif equals in ZZ:
            return equals
        else:
            return True
        
    ###################################################################################
    @CheckBound
    def __repr__(self, *, bound: int | None = None) -> str:
        if self.is_zero() is True:
            return "0"
        elif self.is_identity() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()
        
        def term_str(order, element):
            el_str = f"({element})" if element != 1 else ""
            op_str = f"{g}" if order == 1 else f"{g}^({order})" if order != 0 else ""

            if len(el_str) == 0 and len(op_str) == 0:
                return "1"
            elif len(el_str) == 0:
                return op_str
            elif len(op_str) == 0:
                return el_str
            else:
                return f"{el_str}*{op_str}"

        if self.__finite:
            ## We print everything
            return " + ".join(term_str(o, self[o]) for o in range(self.order(), self.min_coeff() - 1, -1) if self[o] != 0)
        else:
            ## We print at least 3 terms up to order -bound
            order = self.order()
            min_order = min(-bound, order - 3)

            return " + ".join(term_str(o, self[o]) for o in range(order, min_order - 1, -1) if self[o] != 0) + f" + o({g}^{min_order-1})"

    @CheckBound
    def _latex_(self, *, bound: int | None = None) -> str:
        if self.is_zero():
            return "0"
        elif self.is_identity():
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()

        def term_str(order, element):
            el_str = f"\\left({latex(element)}\\right)" if element != 1 else ""
            op_str = f"{latex_variable_name(g)}^{{{order}}})" if order != 0 else g if order == 1 else ""

            if len(el_str) == 0 and len(op_str) == 0:
                return "1"
            elif len(el_str) == 0:
                return op_str
            elif len(op_str) == 0:
                return el_str
            else:
                return f"{el_str}{op_str}"

        if self.__finite:
            ## We print everything
            return " + ".join(term_str(o, self[o]) for o in range(self.order(), self.__min_coeff - 1, -1) if self[o] != 0)
        else:
            ## We print at least 3 terms up to order -bound
            order = self.order()
            min_order = min(-bound, order - 3)

            return " + ".join(term_str(o, self[o]) for o in range(order, min_order - 1, -1) if self[o] != 0) + f" + \\text{{o}}({g}^{min_order-1})"


class PseudoDOperator_Ring(Parent):
    r'''
        Class for a ring of pseudo-differential operators over a :class:`~dalgebra.dring.DRing`.

        Given a differential ring `(R, \partial)`, where `\partial` is a derivation, we can
        always define the ring of pseudo-differential operators `R\langle partial\rangle` whose elements
        are Laurent series in `\partial^{-1}`.

        Similar to the case of Ore Algebras, this ring of pseudo-differential operators is not commutative, meaning
        that `AB \neq BA`. The commutation rules that define this commutation, are induced by Leibniz derivation rule:

        .. MATH::

            \partial f = f' + f\partial,

        for any element `f \in R`. For the `\partial^{-1}`, we use the only reasonable choice, who leads to an infinite
        tail of negative derivations:

        .. MATH::

            partial^{-1} f = f\partial^{-1} + \partial^{-1} f' \partial^{-1} = f\partial^{-1} - f'\partial^{-2} + f''\partial^{-3} - \ldots

        This make the computation with these objects terribly difficult. Hence we propose here an implementation of a *subring*
        of the pseudo differential operators that include the ring of linear differential operators and allow all possible computations
        that keep the tail as finit eas possible (keeping all computations exact).

        INPUT:

        * ``base``: a differential ring with just one operation.
        * ``name``: name that the differential operator will receive (use mostly for cosmetic reasons).

        TODO: add examples
    '''
    Element = PseudoDOperator

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif isinstance(base, PseudoDOperator_Ring):
            raise TypeError("The base must not be a pseudo-differential operator ring")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.D = self.element_class(self, coefficients=[0, base.one()])
        self.Di = self.element_class(self, coefficients={-1: base.one()})
        self.__operators = [AdditiveMap(self, lambda p : self.D * p)]

        ## Setting up basic conversions
        try:
            self.base().register_conversion(PDOConvertToBase(self))
        except AssertionError: # This conversion was already registered 
            pass


    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        return self.__gens[0]
    
    def gen(self) -> PseudoDOperator:
        r'''
            Return the generator of the ring of pseudo-differential operators.
        '''
        return self.D
    
    def igen(self) -> PseudoDOperator:
        r'''
            Return the inverse generator of the ring of pseudo-differential operators.
        '''
        return self.Di
    
    def ngens(self) -> int:
        r'''
            Return the number of generators of the ring of pseudo-differential operators.
        '''
        return 1
    
    def one(self) -> PseudoDOperator:
        r'''
            Return the identity element of the ring of pseudo-differential operators.
        '''
        return self.element_class(self, coefficients=[self.base().one()])
    
    def zero(self) -> PseudoDOperator:
        r'''
            Return the zero element of the ring of pseudo-differential operators.
        '''
        return self.element_class(self, coefficients=[])
    
    def is_field(self) -> bool:
        r'''
            Check if the ring of ore operators is a field.
            This is always False for ore operators, as they are not fields.
        '''
        return False
    
    def is_integral_domain(self) -> bool:
        r'''
            Check if the ring of ore operators is an integral domain.
            This depends directly from the base ring, since the ore operators are a domain if and only if their coefficients are an integral domain.
        '''
        return self.base().is_integral_domain() 
    
    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        return PDOCoerceFromBase(self)

    def _convert_map_from_(self, other: Parent) -> Morphism:
        if isinstance(other, DPolynomialRing_Monoid):
            try:
                # We make sure the other conversion does exist
                other.register_conversion(PDOConvertToDPolyRing(self, other))
            except AssertionError:
                pass
            return PDOConvertToDPolyRing(self, other)

    def construction(self) -> tuple[PseudoDOperatorFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return PseudoDOperatorFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        raise NotImplementedError("Pseudo differential Operators does not allow a fraction field structure.")

    def change_base(self, R: Parent) -> PseudoDOperator_Ring:
        new_ring = PseudoDOperatorRing(R, self.gen_name())
        ## Creating the coercion map if possible
        try:
            M = PDOCoerceBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Ring of pseudo-differential operators over {self.base()}"

    def _latex_(self):
        return f"{latex(self.base())}\\langle {self.__gens[0]} \\rangle"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        up_bound : int = 0, lower_bound : int = 0,
        *args,**kwds
    ) -> PseudoDOperator:
        r'''
            Creates a random element in this ring.

            This method receives a bound for the degree and order of all the variables
            appearing in the ring and also a sparsity measure to avoid dense polynomials.
            Extra arguments are passed to the random method of the base ring.

            INPUT:

            * ``deg_bound``: total degree bound for the resulting polynomial.
            * ``order_bound``: order bound for the resulting polynomial.
            * ``sparsity``: probability of a coefficient to be zero.
        '''
        raise NotImplementedError("The random element method is not implemented for pseudo-differential operators.")

    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> PseudoDOperator_Ring:
        #!!!!!!!!!!!!!!
        return PseudoDOperatorRing(self.base().add_constants(*new_constants), self.__gens[0])

    def linear_operator_ring(self) -> PseudoDOperator_Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        return self

    def inverse_operation(self, element: PseudoDOperator, operation: int = 0) -> PseudoDOperator:
        if element not in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if operation != 0:
            raise ValueError(f"The given operation({operation}) is not valid")

        try:
            return self.Di * element
        except Exception:
            raise NotImplementedError(f"The multiplication of {self.__gens[0]}^(-1) * {element} can not be computed.")


class PseudoDOperatorFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DPolynomialRing_Monoid`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see
          the input ``names`` in :class:`DPolynomialRing_Monoid`)
    '''
    def __init__(self, name: str):
        self.__operator_name = name
        super().__init__(_DRings,_DRings)
        self.rank = 13 # just above DPolyRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        return PseudoDOperatorRing(x,self.__operator_name)

    def _repr_(self):
        return f"PseudoDOperators(*,{self.__operator_name})"

    def __eq__(self, other):
        if other.__class__ == self.__class__:
            return self.__operator_name == other.__operator_name


class PDOCoerceFromBase(Morphism):
    def __init__(self, codomain: PseudoDOperator_Ring):
        if not isinstance(codomain, PseudoDOperator_Ring):
            raise TypeError("The codomain must be a pseudo-differential operator ring")
        
        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> PseudoDOperator:
        return self.codomain().element_class(self.codomain(), coefficients=[element])


class PDOConvertToBase(Morphism):
    def __init__(self, domain: PseudoDOperator_Ring):
        if not isinstance(domain, PseudoDOperator_Ring):
            raise TypeError("The domain must be a pseudo-differential operator ring")

        super().__init__(domain, domain.base())

    def _call_(self, element: PseudoDOperator) -> Element:
        if element.is_zero() is True or element.order(bound=1) == 0:
            return self.codomain()(element[0])
        

class PDOCoerceBetweenBases(Morphism):
    def __init__(self, domain: PseudoDOperator_Ring, codomain: PseudoDOperator_Ring, map: Morphism):
        if not isinstance(domain, PseudoDOperator_Ring):
            raise TypeError("The domain must be a pseudo-differential operator ring")
        if not isinstance(codomain, PseudoDOperator_Ring):
            raise TypeError("The codomain must be a pseudo-differential operator ring")
        if not map.domain() == domain.base() or not map.codomain() == codomain.base():
            raise ValueError("Error in the format for the morphism")

        self.base_map = map

        super().__init__(domain, codomain)

    def _call_(self, element: PseudoDOperator) -> PseudoDOperator:
        if element.is_finite():
            order = element.order()
            min_coeff = element.min_coeff()

            coeffs = {k: element[k] for k in range(min_coeff, order + 1)}

            return self.codomain().element_class(self.codomain(), coefficients=coeffs)
        else: # infinite case
            return self.codomain().element_class(self.codomain(), 
                                                 coefficient_map=element._PseudoDOperator__map, 
                                                 order_bound=element.order())


class PDOConvertFromDPolyRing(Morphism):
    def __init__(self, domain: DPolynomialRing_Monoid, codomain: PseudoDOperator_Ring, gen: str | None = None):
        if not isinstance(domain, DPolynomialRing_Monoid):
            raise TypeError("The domain must be a differential polynomial ring")
        if not isinstance(codomain, PseudoDOperator_Ring):
            raise TypeError("The codomain must be a pseudo-differential operator ring")
        
        self.__gen = domain.gen(gen) if gen is not None else domain.gens()[-1]

        base = domain.remove_variables(gen)
        if base != codomain.base():
            raise ValueError("The base rings of the domain and codomain must be the same")
        
        super().__init__(domain, codomain)

    def _call_(self, element: DPolynomial) -> PseudoDOperator:
        z = self.__gen # the dpoly generator

        if not element.is_linear((z,)):
            raise ValueError("The element must be a linear differential polynomial in the generator of the domain")
        coeffs = [element.coefficient_full(z[i]) for i in range(element.order(z)+1)]
        return self.codomain().element_class(self.codomain(), coefficients=coeffs)


class PDOConvertToDPolyRing(Morphism):
    def __init__(self, domain: PseudoDOperator_Ring, codomain: DPolynomialRing_Monoid, gen: str | None = None):
        if not isinstance(domain, PseudoDOperator_Ring):
            raise TypeError("The domain must be a pseudo-differential operator ring")
        if not isinstance(codomain, DPolynomialRing_Monoid):
            raise TypeError("The codomain must be a differential polynomial ring")

        self.__gen = codomain.gen(gen) if gen is not None else codomain.gens()[-1]
        base = codomain.remove_variables(gen)

        if base != domain.base():
            raise ValueError("The base rings of the domain and codomain must be the same")

        super().__init__(domain, codomain)

    def _call_(self, element: PseudoDOperator) -> DPolynomial:
        if not element.is_finite():
            raise ValueError("The element must be finite to convert it to a differential polynomial")
        if element.min_coeff() < 0:
            raise ValueError("The element must have non-negative coefficients to convert it to a differential polynomial")
        z = self.__gen
        return sum(element[k] * z[k] for k in range(element.min_coeff(), element.order() + 1))