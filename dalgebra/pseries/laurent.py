from __future__ import annotations

r'''
    Module to create univariate formal Laurent power series over a given differential field.

    TODO: Add examples and more detailed explanation of the structure.        

    TODO: For laurent

    ::IGNORE AUDIT::
'''

# ****************************************************************************
#  Copyright (C) 2026 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

import logging

from enum import Enum

from functools import lru_cache

from sage.categories.commutative_algebras import CommutativeAlgebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.matrix.constructor import matrix
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex, latex_variable_name
from sage.rings.infinity import Infinity as oo
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.rings.rational import Rational
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Mapping, Callable
from ..dring import AdditiveMap, DRings, DifferentialRing, MorphismToLaurent
from ..dpolynomial.dpolynomial import DPolynomial

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)

logger = logging.getLogger(__name__)

#################################################################################
###
### BOUNDS MANAGEMENT FOR LAURENT DIFFERENTIAL FIELDS
###
#################################################################################
LS_GLOBAL_BOUND = 20


def LSChangeBound(bound: int):
    r'''
        Changes the global bound for computations in formal Laurent series.

        ::NO EXAMPLE::
    '''
    global LS_GLOBAL_BOUND
    if bound not in ZZ or bound < 3:
        raise ValueError(f"The bound must be a non-negative integer, got {bound}.")
    LS_GLOBAL_BOUND = bound


def CheckBound(func):
    r'''
        Wrapper to check the bound argument.

        This is a decorator to check that the method has a bound argument, that it is set and call properly. This 
        simplifies and unifies the check of this type of argument which appears naturally throughout the module.

        ::NO EXAMPLE::
    '''
    from functools import wraps

    @wraps(func)
    def wrapper(self: LSeries_Element | LSeries_Ring, *args, **kwds):
        import inspect
        sig = inspect.signature(func)
        if "bound" not in sig.parameters:
            raise TypeError(f"The method {func.__name__} does not accept a 'bound' argument.")
        elif sig.parameters["bound"].default is not None:
            raise TypeError(f"The method {func.__name__} does not accept a default value for 'bound'.")
        value = kwds.pop("bound") if "bound" in kwds else LS_GLOBAL_BOUND

        if value not in ZZ or value < 0:
            raise TypeError(f"The method {func.__name__} requires a non-negative integer 'bound' argument to be passed.")

        kwds["bound"] = value

        return func(self, *args, **kwds)
    return wrapper


#################################################################################
###
### FACTORY FOR LAURENT DIFFERENTIAL FIELDS
###
#################################################################################
class LSeries_RingFactory(UniqueFactory):
    r'''
        Factory to create the ring of Laurent series over a differential field.

        This allows to cache the same rings created from different objects. See
        :class:`LSeries_Ring` for further information on this structure.
    '''
    def create_key(self, base, name: str = None, **kwds):
        r'''
            See :func:`UniqueFactory.create_key` for more information.

            ::NO EXAMPLE::
        '''
        if base not in _Fields:
            raise TypeError("The base ring must be a field")
        # We check now whether the base ring is valid or not
        if base not in _DRings:
            base = DifferentialRing(base) # automatically add the zero derivative

        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The given ring must be a differential ring with just 1 derivation.")

        if name is None and "names" in kwds:
            if len(kwds["names"]) != 1:
                raise ValueError("You must provide exactly one name for the generator of the formal power series ring.")
            name = kwds["names"][0]
        
        if name is None:
            raise TypeError("You must provide a name for the generator of the formal power series ring.")
        elif name in (str(v) for v in base.gens()):
            raise TypeError(f"The given name ({name}) already exist in the base ring.")

        # Now the names are appropriate and the base is correct
        return (base, name)

    def create_object(self, _, key) -> LSeries_Ring:
        r'''
            See :func:`UniqueFactory.create_object` for more information.

            ::NO EXAMPLE::
        '''
        base, name = key

        return LSeries_Ring(base, name)


LaurentSeries = LSeries_RingFactory("dalgebra.pseries.lseries.LSeries_Element")


class LSeries_Element(Element):
    r'''
        Class representing a formal laurent series.

        A formal laurent series is a formal sum over a given variable with coefficients in a field tat will be considered as constants of the form

        .. MATH::

            f(x) = \sum_{i = n}^{\infty} a_i x^i,

        where `n \in \mathbb{Z}`. 
        
        These objects are non-finite by nature (elements tend to have infinite tails). This class handles this infinite tail 
        by storing a method that computes (upon request) the coefficients for any given integer.

        This class has a clear limitation: computations are usually non exact. For example, the traditional zero-checking can only be performed
        up to some given order. These methods have an optional parameter ``bound`` that allows to specify the order up to which computations are
        performed.

        We allow three different ways to create a formal laurent series:
        1. By providing a ``coefficient_map``, which is a callable that receives an integer and returns the corresponding coefficient. This is the most generic way to create a formal laurent series. We never have a criteria for zero testing.
        2. By providing a finite list or map of elements as ``coefficients``. This creates a finite formal laurent polynomial, and all computations are exact. 
        3. TODO: By providing a differential polynomial in one variable with coefficients in the constant field. This is interpret as a differential algebraic equation that the formal laurent series must satisfy. We require for this input a set of initial conditions that determines the formal power series uniquely. This is the most complex way to create a formal power series, but it allow for zero testing while keeping the tail infinite.
    '''
    TYPES = Enum('Type', [("default",0), ("polynomial", 1), ("dalgebraic", 2)])

    def __init__(self, parent: LSeries_Ring, *,
                 coefficient_map: Callable[[int],Element] | None = None, order: int | None = None,
                 coefficients: Collection[Element] | Mapping[int, Element] | None = None,
                 differential_equation: DPolynomial | None = None, initial_conditions: Collection[Element] | Mapping[int, Element] | None = None,
    ):
        base = parent.base()

        default = coefficient_map is not None and order is not None
        polynomial = coefficients is not None
        dalgebraic = differential_equation is not None and initial_conditions is not None

        if not any((default, polynomial, dalgebraic)):
            raise TypeError("You must provide at least one of the following arguments: coefficient_map, coefficients, differential_equation and initial_conditions.")
        elif sum((default, polynomial, dalgebraic)) > 1:
            raise TypeError("You can only provide one of the following arguments: coefficient_map, coefficients, differential_equation and initial_conditions.")
        
        if default:
            # We set the type of the power series
            self.__type = self.TYPES.default
            
            # We store the components for this series
            self.__map = coefficient_map
            self.__order = order
            self.__poly = None
            self.__dalgebraic = None
        elif polynomial:
            self.__type = self.TYPES.polynomial

            if not isinstance(coefficients, Mapping):
                self.__poly = {i: base(c) for (i,c) in enumerate(coefficients) if c != base.zero()}
            else:
                self.__poly = {k: base(v) for k, v in coefficients.items() if base(v) != base.zero()}
            self.__order = min(self.__poly) if len(self.__poly) > 0 else oo
            self.__map = None
            self.__dalgebraic = None
        else: # dalgebraic
            raise NotImplementedError("Differential algebraic formal laurent series are not yet implemented.")

        ## We create a cache for computed elements
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
        if self.__type == self.TYPES.default:
            if any(self[k] != self.parent().base().zero() for k in range(min(self.order(),0), bound+1)):
                return False
            return bound
        elif self.__type == self.TYPES.polynomial:
            return self.order() == oo
        else: # dalgebraic
            raise NotImplementedError("Zero checking for differential algebraic formal laurent series is not yet implemented.")

    @CheckBound
    def is_one(self, *, bound: int | None = None) -> bool | int: 
        r'''
            Checker for the identity element.

            See :func:`is_zero` for more information on the output of this type of methods.
        '''
        return (self - self.parent().one()).is_zero(bound=bound)
    
    def is_unit(self) -> bool:
        r'''
            Checker for whether the element is a unit or not.

            Laurent series forma a field, hence all non-zero elements are units.
        '''
        return (self.is_zero() is False)

    @CheckBound
    def order(self, *, bound: int | None = None) -> int: # Gets degree of first non-zero element
        r'''
            Method to get the order of a formal power series.
        '''
        if self.__type == self.TYPES.default:
            for i in range(self.__order, bound+1):
               if self[i] != 0:
                   self.__order = i # we update the data for the order
                   return i
            return bound
        elif self.__type == self.TYPES.polynomial:
            return self.__order # computed on initialization
        else: # dalgebraic
            raise NotImplementedError("Order computation for differential algebraic formal laurent series is not yet implemented.")
        
    def degree(self) -> int:
        r'''
            Computes the degree of a polynomial in the Laurent series ring.

            We define the degree of a Laurent series only for polynomials (i.e., finite series). For a polynomial, the degree is the maximum integer such that the coefficient of the generator to that power is non-zero. For non-polynomial series, this method raises an error.
        '''
        if not self.__type == self.TYPES.polynomial:
            raise TypeError("Degree is only defined for finite formal laurent series.")
        return max(self.__poly) if len(self.__poly) > 0 else -oo

    def type(self) -> LSeries_Element.TYPES:
        r'''
            Method to get the type of formal power series.
        '''
        return self.__type

    def is_finite(self) -> bool:
        r'''
            Method to check whether the formal power series is finite or not.
        '''
        return self.__type == self.TYPES.polynomial
    
    @CheckBound
    def is_monomial(self, *, bound: int | None = None) -> bool | int:
        r'''
            Checks whether an element is a monomial (a series with only one non-zero term) or not.

            IMPORTANT: Zero is NOT a monomial

            Since we can only check this information up to a given order, the output will be an integer with the terms checked if we cannot be sure, ``True`` if it is a monomial, or ``False`` if it is not.

            EXAMPLES::

                sage: from dalgebra.pseries.laurent import LaurentSeries
                sage: R = LaurentSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = 3*x**2
                sage: f.is_monomial()
                True
                sage: f = x**2 + 2*x + 1
                sage: f.is_monomial()
                False
                sage: f = R.zero()
                sage: f.is_monomial()
                False
                sage: f = x**10*(~(1-x)) # x^10 + x^11 + x^12 + ...
                sage: f.is_monomial(bound=9)
                9
        '''
        zero = self.is_zero(bound=bound+1)
        if zero == bound+1:
            return bound+1
        return (self - self.trailing_term()).is_zero(bound=bound)

    def truncate(self, order: int) -> LSeries_Element:
        r'''
            Return a :class:`LSeries_Element` that contains only the coefficients with degree at most than or equal to ``order``.

            This method always return a finite formal power series, even if the original one is not finite.
        '''
        coeffs = {k : self[k] for k in range(min(self.order(),0), order+1)}
        return self.parent().element_class(self.parent(), coefficients=coeffs)

    def polynomial(self) -> Element:
        r'''
            EXAMPLES::

                sage: from dalgebra.pseries.laurent import LaurentSeries
                sage: R = LaurentSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = x**2 + 2*x + 1
                sage: P = R.poly_ring()
                sage: X = P.gen()
                sage: f.polynomial() == X**2 + 2*X + 1
                True
                sage: f = ~(1-x) # 1/(1-x) = 1 + x + x^2 + ...
                sage: f.truncate(5).polynomial()
                1 + x + x^2 + x^3 + x^4 + x^5
        '''
        if self.__type == self.TYPES.polynomial and self.order() >= 0:
            return self.parent().poly_ring()(self)
        raise TypeError("The element is not a polynomial.")
    
    def rational_function(self) -> Element:
        r'''
            EXAMPLES::

                sage: from dalgebra.pseries.laurent import LaurentSeries
                sage: R = LaurentSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = ~x - 1 # (1/x) - 1 = (1 - x)/x
                sage: T = R.rat_field()
                sage: X = T.gen()
                sage: f.rational_function() == (1 - X)/X
                True
        '''
        if self.__type == self.TYPES.polynomial:
            return self.parent().rat_field()(self)
        raise TypeError("The element is not a Laurent polynomial.")

    def equation(self) -> DPolynomial:
        r'''
            Gets the differential equation that defines the element. (Not always possible)
        '''
        raise NotImplementedError("Differential algebraic formal laurent series are not yet implemented.")

    @CheckBound
    def trailing_coefficient(self, *, bound: int | None = None) -> Element:
        r'''
            Method to get the trailing coefficient of a formal Laurent series.

            The trailing coefficient is the coefficient of the monomial with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.
        '''
        order = self.order(bound=bound+1)
        if order == bound+1:
            return self.parent().base().zero()
        else:
            return self[order]

    @CheckBound
    def trailing_term(self, *, bound: int | None = None) -> LSeries_Element:
        r'''
            Method to get the trailing term of a formal Laurent series.

            The trailing term is the monomial with its coefficient with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.
        '''
        order = self.order(bound=bound+1)
        if order == bound+1:
            return self.parent().zero()
        else:
            return self.parent().element_class(self.parent(), coefficients={order: self[order]})

    def gen_mult(self, n: int) -> LSeries_Element:
        r'''
            Multiplies the formal Laurent series by the generator to the power of ``n``.

            This is equivalent to shifting all coefficients by ``n`` positions.
        '''
        if n == 0:
            return self
        elif self.__type == self.TYPES.polynomial:
            return self.parent().element_class(self.parent(), coefficients={k + n: c for k, c in self.__poly.items()})
        elif self.__type == self.TYPES.dalgebraic:
            raise NotImplementedError("Multiplication by the generator for differential algebraic formal laurent series is not yet implemented.")
        else: # default
            return self.parent().element_class(self.parent(), coefficient_map=lambda k: self[k - n], order=self.__order + n)

    @CheckBound
    def pseries_split(self, *, bound: int | None = None) -> tuple[int, LSeries_Element]:
        r'''
            Splits the formal Laurent series into the product of a power of the generator and a formal power series with non-zero constant term.

            This is a method that may not be exact, hence, if we can not compute fully the power of the generator, we return the last computed order.
        '''
        order = self.order(bound=bound)
        return (order, self.gen_mult(-order))

    def __getitem__(self, key: int) -> Element:
        if isinstance(key, slice):
            return [self[i] for i in range(key.start or 0, key.stop or oo, key.step or 1)]
        elif key not in self.__cache_computed:
            if self.__type == self.TYPES.default:
                if key < self.__order:
                    self.__cache_computed[key] = self.parent().base().zero()
                self.__cache_computed[key] = self.parent().base()(self.__map(key))
            elif self.__type == self.TYPES.polynomial:
                self.__cache_computed[key] = self.__poly.get(key, self.parent().base().zero())
            else: # dalgebraic
                raise NotImplementedError("Differential algebraic formal laurent series are not yet implemented.")
            
        return self.__cache_computed[key]
    
    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Element._add_` for further information.

            ::NO EXAMPLE::
        '''
        ## Checking for trivial cases
        if self.is_zero() is True:
            return other
        elif other.is_zero() is True:
            return self
        
        if any(el.__type == self.TYPES.default for el in (self, other)):
            # at least one is default -> we change to default
            add_map = lambda k : self[k] + other[k]
            return self.parent().element_class(self.parent(), coefficient_map=add_map, order=min(self.__order, other.__order))
        elif self.__type == self.TYPES.polynomial and other.__type == self.TYPES.polynomial: 
            # both are polynomials
            out = self.__poly.copy()
            for k, v in other.__poly.items():
                if k in out:
                    out[k] += v
                else:
                    out[k] = v
            return self.parent().element_class(self.parent(), coefficients=out)
        else: # at least one is dalgebraic
            raise NotImplementedError("Addition of differential algebraic formal laurent series is not yet implemented.")

    def __neg__(self) -> LSeries_Element:
        if self.is_zero() is True:
            return self
        if self.__type == self.TYPES.polynomial:
            # Finite case -> It remains a finite
            coeffs = {k: -self[k] for k in self.__poly}
            return self.parent().element_class(self.parent(), coefficients=coeffs)
        elif self.__type == self.TYPES.dalgebraic:
            raise NotImplementedError("Negation of differential algebraic formal laurent series is not yet implemented.")
        else:
            neg_map = lambda k : -self[k]
            
            return self.parent().element_class(self.parent(), coefficient_map=neg_map, order=self.__order)

    def _sub_(self, other: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Element._sub_` for further information.

            ::NO EXAMPLE::
        '''
        return self + (-other)

    def _mul_(self, other: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Element._mul` for further information.

            ::NO EXAMPLE::
        '''
        ## Multiplication with trivial/simpler cases
        if (self.is_zero() is True) or (other.is_zero() is True): # multiplication by a true zero
            return self.parent().zero()
        elif (self.is_one() is True): # multiplication when self is one
            return other
        elif (other.is_one() is True): # multiplication when other is one
            return self
        elif self in self.parent().base(): # scalar product (self)
            scalar = self.parent().base()(self)
            if other.__type == self.TYPES.polynomial:
                return self.parent().element_class(self.parent(), coefficients={k: scalar * c for k, c in other.__poly.items()})
            elif other.__type == self.TYPES.dalgebraic:
                raise NotImplementedError("Multiplication of differential algebraic formal laurent series is not yet implemented.")
            else: # default
                return self.parent().element_class(self.parent(), coefficient_map=lambda k: scalar * other[k], order=other.order())
        elif other in self.parent().base(): # scalar product (other)
            return other * self
        elif self.is_monomial() is True: # multiplication by monomial (self)
            order = self.order() # this computation is now exact
            return self[order] * other.gen_mult(order)
        elif other.is_monomial() is True: # multiplication by monomial (other)
            return other * self

        ## Multiplication when none is trivial
        if any(el.__type == self.TYPES.default for el in (self, other)):
            # at least one is default
            ## we update the best possible the orders
            t = self.order()
            s = other.order()
            mul_map = lambda k : sum(self[i]*other[k-i] for i in range(t, k-s+1))
            return self.parent().element_class(self.parent(), coefficient_map=mul_map, order=t+s)
        elif self.__type == self.TYPES.polynomial and other.__type == self.TYPES.polynomial: 
            # both finite case --> it remains finite
            t, ps = self.pseries_split()
            s, qs = other.pseries_split()

            ## this is a finite Laurent series
            poly_part: LSeries_Element = self.parent()(ps.polynomial()*qs.polynomial())
            ## we shift as necessary by t+s
            return self.parent().element_class(self.parent(), coefficients={k + t + s: c for k, c in poly_part.__poly.items()})
        else: # at least one is dalgebraic
            raise NotImplementedError("Multiplication of differential algebraic formal laurent series is not yet implemented.")

    def _div_(self, other: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Element._div_` for further information.

            ::NO EXAMPLE::
        '''
        ## full division and floor division coincide in fields
        return self // other

    def _floordiv_(self, other: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Element._floordiv_` for further information.

            ::NO EXAMPLE::
        '''
        ## division is split into inversion and a multiplication
        return self * (~other)     
    
    @cached_method
    def __invert__(self) -> LSeries_Element:
        r'''
            Computes the multiplicative inverse of the formal power series.
        '''
        if self.is_zero() is True:
            raise ZeroDivisionError(f"Inverse of zero element do not exist.")
        elif self.is_monomial() is True:
            order = self.order() # this computation is now exact
            return self.parent().element_class(self.parent(), coefficients={-order: ~self[order]})
        
        order, ps = self.pseries_split()
        if ps[0] == 0:
            raise ZeroDivisionError(f"Could not say if an element is zero or not.")
        
        @lru_cache(maxsize=256)
        def inverse_coeffs(k: int) -> Element:
            if k == 0:
                return 1 / self[0]
            else:
                num = sum(self[k-i]*inverse_coeffs(i) for i in range(0, k))
                denom = -inverse_coeffs(0)
                return num * denom
            
        ## Inverse of the formal power series
        ps_inv = self.parent().element_class(self.parent(), coefficient_map=inverse_coeffs, order=0)
        return ps_inv.gen_mult(-order)        

    @cached_method
    def __pow__(self, power: int | Rational) -> LSeries_Element:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            return (~self)**(-power)
        elif power not in ZZ:
            if power not in QQ:
                raise ValueError(f"Power {power} is not a rational number, only rational powers are allowed in pseudo-differential operators.")
            n = power.numerator()
            m = power.denominator()
            
            if n == 1:
                order, ps = self.pseries_split()
                if order % m != 0:
                    raise ValueError(f"The order of the formal power series ({order}) is not divisible by the denominator of the power ({m}).")
                a0 = ps[0]
                b0 = a0**power # this checks if the operation can be done
                a_inv = ~ps # this also checks if the operation can be done
                goal_parent = pushout(b0.parent(), self.parent()) # this is usually self.parent()

                @lru_cache(maxsize=256)
                def coeff_root(t: int) -> Element:
                    if t == 0:
                        return b0
                    result = goal_parent.base().zero()
                    for j in range(t):
                        to_add = goal_parent.base().zero()
                        for k in range(0, t-j):
                            to_add += a_inv[k]*sum((ps[i+1] for i in range(t-j-k)), goal_parent.base().zero())
                        result += coeff_root(j) * to_add
                    return result

                return self.parent().element_class(self.parent(), coefficient_map=coeff_root, order=0).gen_mult(order // m)
            else:
                return (self**n)**(QQ((1,m)))
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
        elif equals is False:
            return True
        return equals

    def __hash__(self) -> int:
        return hash(self.__repr__(bound=100))
    
    def __call__(self, **kwds) -> Element:
        if self.__type == self.TYPES.polynomial:
            new_poly = {k: el(**kwds) for (k,el) in self.__poly.items()}
            return self.parent().element_class(self.parent(),coefficients=new_poly)
        elif self.__type == self.TYPES.default:
            new_func = lambda n : self[n](**kwds)
            return self.parent().element_class(self.parent(), coefficient_map=new_func, order=self.order())
        else:
            raise ValueError("Impossible type for a Laurent series")

    ###################################################################################
    @CheckBound
    def __repr__(self, *, bound: int | None = None) -> str:
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()

        def operator_repr(order:int) -> str:
            if order == 0:
                return "1"
            elif order == 1:
                return f"{g}"
            elif order < 0:
                return f"{g}^({order})"
            else:
                return f"{g}^{order}"

        def term_str(order:int, element:Element, first:bool=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""

            op_str = operator_repr(order)
            ## If the element is 1, we just return the monomial
            if element in (1, -1):
                if element == -1:
                    element = -element
                    sign = " - " if not first else "-"
                else:
                    sign = " + " if not first else ""
                
                output = f"{sign}{op_str}"
            else: # element is something != 1
                if str(element)[0] == "-":
                    sign = " - " if not first else "-"
                    el_str = str(-element)
                else:
                    sign = " + " if not first else ""
                    el_str = str(element)

                if any(char in el_str for char in ("+", "-", " ")): # case with several terms
                    el_str = f"({el_str})"

                join = "*" if all(len(part) > 0 for part in (el_str, op_str)) else ""
                output = f"{sign}{el_str}{join}{op_str}"
            return output
                    
        if self.__type == self.TYPES.polynomial:
            ## We print everything
            ## polynomial that is not zero: it has a finite order
            order = self.order()
            return term_str(order, self[order],True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, max(self.__poly)+1) 
                if self[o] != 0
            ) 
        else:
            order = self.order(bound=bound+1)
            
            if order == bound+1:
                return f"O({term_str(bound+1,1,True)})"
            
            return term_str(order, self[order], True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, bound+1) 
                if self[o] != 0
            ) + (f" + O({term_str(bound+1,1,True)})")

    @CheckBound
    def _latex_(self, *, bound: int | None = None) -> str:
        r'''
            Computes a LaTeX string to represent the formal Laurent series.

            ::NO EXAMPLE::
        '''
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()

        def operator_str(order):
            if order == 0:
                return "1"
            elif order == 1:
                return f"{latex_variable_name(g)}"
            else:
                return f"{latex_variable_name(g)}^{{{order}}}"
            
        def term_str(order, element, first=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""
            ## If the element is 1, we just return the monomial
            if element == 1:
                output = (" + " if not first else "") + operator_str(order)
            elif element == -1:
                output = (" - " if not first else "") + operator_str(order)
            else: # element is something != 1
                op_str = operator_str(order)
                if str(element)[0] == "-":
                    sign = " - " if not first else "-"
                    element = -element
                else:
                    sign = " + " if not first else ""

                if any(char in str(element) for char in ("+", "/", "*", "-", " ")): # case with several terms
                    el_str = f"\\left({latex(element)}\\right)"
                else:
                    el_str = latex(element)

                output = f"{sign}{el_str}{op_str}"
            return output

        if self.__type == self.TYPES.polynomial:
            ## We print everything
            ## polynomial that is not zero: it has a finite order
            order = self.order()
            return term_str(order, self[order],True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, max(self.__poly)+1) 
                if self[o] != 0
            ) 
        else:
            ## We print at least 3 terms up to order -bound
            order = self.order(bound=bound+1)
            if order == bound+1:
                return f"\\text{{O}}({term_str(bound+1,1,True)})"

            return term_str(order, self[order], True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, bound+1) 
                if self[o] != 0
            ) + (f" + \\text{{O}}({term_str(bound+1,1,True)})")


class LSeries_Ring(Parent):
    r'''
        Class for a field of Laurent series over a :class:`~dalgebra.dring.DRing`.

        Given a field `F`, we can always define the field of Laurent series `F((x))` whose elements
        are formal series in a new variable `x` starting from a negative exponent. Here we can extend 
        the derivation in the field `F` naturally.

        INPUT:

        * ``base``: a field with one derivative.
        * ``name``: name that the variable `x` will have.

        TODO: add examples
    '''
    Element = LSeries_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]: 
        r'''
            Method to generate the appropriate list of categories for ``self``

            ::NO EXAMPLE::    
        '''
        return [_DRings, CommutativeAlgebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif isinstance(base, LSeries_Ring):
            raise TypeError("The base must not be a formal power series ring")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")
        elif base.constant_ring() != base:
            raise TypeError("The base must be a differential ring with trivial constants")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.__operators = [self.__build_derivation()]
        self.__gen = self.element_class(self, coefficients={1: self.base().one()})
        self.__poly_ring = PolynomialRing(base.to_sage(), name)
        self.__rat_field = self.__poly_ring.fraction_field()

        ## Setting up basic conversions
        try:
            self.base().register_conversion(LSConvertToBase(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(LSCoerceFromPoly(self))
            self.poly_ring().register_conversion(LSConvertToPoly(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(LSCoerceFromRational(self))
            self.rat_field().register_conversion(LSConvertToRational(self))
        except AssertionError: # This conversion was already registered
            pass
        
    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        r'''
            Return the string for representing the generator of the field of laurent series.
        '''
        return self.__gens[0]

    def gen(self) -> LSeries_Element:
        r'''
            Return the generator of the field of laurent series.
        '''
        return self.__gen
    
    def gens(self) -> tuple[LSeries_Element]:
        r'''
            Return the generators of the field of laurent series.
        '''
        return (self.__gen,)

    def ngens(self) -> int:
        r'''
            Return the number of generators of the field of laurent series.
        '''
        return 1

    def one(self) -> LSeries_Element:
        r'''
            Return the identity element of the field of laurent series.
        '''
        return self.element_class(self, coefficients={0:self.base().one()})

    def zero(self) -> LSeries_Element:
        r'''
            Return the zero element of the field of laurent series.
        '''
        return self.element_class(self, coefficients=dict())

    def is_field(self, proof: bool = True) -> bool:
        r'''
            Check if the field of laurent series is a field.
            This is always True.
        '''
        return True

    def is_integral_domain(self, proof: bool = True) -> bool:
        r'''
            Check if the field of laurent series is an integral domain.
            This is, by definition, True
        '''
        return True

    def poly_ring(self) -> Parent:
        r'''
            Return the polynomial ring associated to this field of formal laurent series
        '''
        return self.__poly_ring
    
    def rat_field(self) -> Parent:
        r'''
            Return the field of rational functions associated to this field of formal laurent series.
        '''
        return self.__rat_field

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        r'''
            See :func:`Parent._coerce_map_from_base_ring` for further information.

            ::NO EXAMPLE::
        '''
        return LSCoerceFromBase(self)

    def construction(self) -> tuple[LaurentSeriesFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return LaurentSeriesFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        r'''
            See :func:`Parent.fraction_field` for further information.

            ::NO EXAMPLE::
        '''
        return self

    def change_base(self, R: Parent) -> LSeries_Ring:
        r'''
            Method to change the base field for considering the series.

            This method takes into consideration the coercions between the old and the new base to create the appropriate coercion maps between the old and new Laurent series rings.
        '''
        new_ring = LaurentSeries(R, self.gen_name())
        ## Creating the coercion map if possible
        try:
            M = LSCoerceBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Formal Laurent Series Ring in {self.__gens[0]} over {self.base()}"

    def _latex_(self):
        r'''
            Computes a LaTeX representation for this field of Laurent series.

            ::NO EXAMPLE::
        '''
        return f"{latex(self.base())}\\left(\\left({self.__gens[0]}\\right)\\right)"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        up_bound : int = 0, lower_bound : int = 0,
        *args,**kwds
    ) -> LSeries_Element:
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
        return self.element_class(self, coefficients={k: self.base().random_element(*args, **kwds) for k in range(lower_bound, up_bound+1)})

    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[AdditiveMap]:
        r'''
            See :func:`DRings.ParentMethods.operators` for further information.

            ::NO EXAMPLE::
        '''
        return self.__operators

    def operator_types(self) -> tuple[str]:
        r'''
            See :func:`DRings.ParentMethods.operator_types` for further information.

            ::NO EXAMPLE::
        '''
        return self.base().operator_types()

    def constant_ring(self, _: int = 0) -> Parent:
        r'''
            See :func:`DRings.ParentMethods.constant_ring` for further information.

            ::NO EXAMPLE::
        '''
        return self.base()

    def add_constants(self, *new_constants: str) -> LSeries_Ring:
        r'''
            See :func:`DRings.ParentMethods.add_constants` for further information.

            ::NO EXAMPLE::
        '''
        return LaurentSeries(self.base().add_constants(*new_constants), self.__gens[0])

    def _laurent_morphism(self, imgs, constant=None, set_default=False) -> MorphismToLaurent:
        r'''
            Internal implementation for :func:`DRings.ParentMethods.laurent_morphism`.

            ::NO EXAMPLE::
        '''
        base_morph = self.base().laurent_morphism(imgs, constant=constant, set_default=set_default)
        return LSeriesLaurentMorphism(self, base_morph.codomain(), base_morph)

    def linear_operator_ring(self):
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.

            ::NO EXAMPLE::
        '''
        raise NotImplementedError("Linear operator ring over Formal Laurent Series not yet implemented")

    def inverse_operation(self, element: LSeries_Element, operation: int = 0) -> LSeries_Element:
        r'''
            See :func:`DRings.ParentMethods.inverse_operation` for further information.

            ::NO EXAMPLE::
        '''
        raise NotImplementedError("Integration over Laurent Series with non-constant coefficients not yet implemented")

    def __build_derivation(self) -> AdditiveMap:
        r'''
            Internal method to build the derivation of the field of laurent series.

            ::NO EXAMPLE::
        '''
        def derivation_map(element: LSeries_Element) -> LSeries_Element:
            if element.type() == element.TYPES.polynomial:
                order = element.order() # exact value
                out_dict = {order-1: element[order]*order}
                for k in range(order, element.degree()+1):
                    out_dict[k] = element[k].derivative() + element[k+1]*(k+1)
                return self.element_class(self, coefficients=out_dict)
            elif element.type() == element.TYPES.dalgebraic:
                raise NotImplementedError("Derivation of differential algebraic formal laurent series not yet implemented.")
            else:
                return self.element_class(self, coefficient_map=lambda k: (k+1)*element[k+1] + element[k].derivative(), order=element.order()-1)

        return AdditiveMap(self, derivation_map)
    
    @CheckBound
    def system_for_constant_solutions(self, system, homogeneous: bool = True, bound: int = None):
        r'''
            Method that extends a linear system for computing constant solutions.

            Given a linear system `(A|b)` over a field `F`, we can look for a set of
            constant solutions in `C \subset F`. This method provides (when possible)
            an extended system `(\tilde{A}|\tilde{b})` such that every constant
            solution of the original system is a solution for the new system and vice-versa.

            INPUT:

            * ``system``: a matrix containing the system `(A|b)`.

            OUTPUT:

            A new matrix with coefficients in `C` fulfilling the desired condition,
            and a list of enumerated monomials indicating the origin of each new equation.
        '''
        if homogeneous is False:
            raise NotImplementedError("The non-homogeneous case is not yet implemented.")
        
        logger.debug(f"[SFCS] Extending system for constant solutions (Laurent series)")
        # For a system of Laurent series to have a constant solution, then all the systems induced for each order
        # must have the same constant solution. Hence, we need to extend the system with the equations given by 
        # the condition of being a solution for each order. 
        system = [[self(element) for element in row] for row in system]
        ## Matrix of orders
        orders = [[el.order() for el in row] for row in system]
        mo = min(min(o for o in row) for row in orders)
        nrows = len(system)
        ncols = -1 if nrows == 0 else len(system[0])

        logger.debug(f"[SFCS] Computing the system for each order")
        systems = []
        co = mo
        ck = matrix(self.constant_ring(), 1, ncols).right_kernel()

        equals = 0

        while equals < bound and ck.dimension() > 0:
            ## We compute the next system
            systems.append(matrix([[el[co] for el in row] for row in system]))
            ## We compute and compare its solution with the previous one
            nk = systems[-1].right_kernel()
            rk = ck.intersection(nk)

            if rk.dimension() == ck.dimension(): # they coincide, we count
                equals += 1
            else:
                equals = 0
            
            ## Updating variables for the next iteration
            ck = rk
            co += 1

        ## We have either that many systems had the same solution or the dimension of the solution is zero
        if ck.dimension() == 0: ## Unique solution: all zeros -> we return the identity matrix
            logger.debug(f"[SFCS] Unique solution found after checking {equals} systems, returning identity matrix")
            return matrix(self.constant_ring(), nrows, ncols).identity_matrix(), [(0,()) for _ in range(nrows)]
        
        ## Now we had a solution space, we build a matrix with that solution space as kernel.
        M = ck.matrix().right_kernel_matrix()
        raise RuntimeError
        return M, [(0,()) for _ in range(M.nrows())]  

class LaurentSeriesFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`LSeries_Ring`.

        This class represents the functor `F: R \mapsto R((x))`.
        The name of the variable must be given to the functor and, then
        this can take any differential field ring and create the corresponding field of laurent
        series.

        INPUT:

        * ``name``: name of the variable that the functor will add
    '''
    def __init__(self, name: str):
        self.__gen_name = name
        super().__init__(_DRings,_DRings)
        self.rank = 13 # just above DPolyRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        r'''
            See :func:`ConstructionFunctor._apply_functor` for further information.

            ::NO EXAMPLE::
        '''
        return LaurentSeries(x,self.__gen_name)

    def _repr_(self):
        r'''
            Return a str representing the functor.

            ::NO EXAMPLE::
        '''
        return f"LaurentSeries(*,{self.__gen_name})"

    def __eq__(self, other):
        if other.__class__ == self.__class__:
            return self.__gen_name == other.__gen_name
        return False


class LSeriesLaurentMorphism(MorphismToLaurent):
    r'''
        Laurent morphism class associated with :class:`LSeries_Ring`.
    '''
    def __init__(self, domain: LSeries_Ring, codomain: LSeries_Ring, base_map: Morphism):
        super().__init__(domain, codomain, base_map)

    def _call_(self, element: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        # Here we assume the element is in self.domain()
        if element.type() == LSeries_Element.TYPES.polynomial:
            coeffs = {k: self.base_map(element[k]) for k in element._LSeries_Element__poly}
            return self.codomain().element_class(self.codomain(), coefficients=coeffs)
        elif element.type() == LSeries_Element.TYPES.dalgebraic:
            raise NotImplementedError("Coercion of differential algebraic formal laurent series is not yet implemented.")
        else: # default case
            ## Coercion is performed outside the method:
            return self.codomain().element_class(self.codomain(), coefficient_map=element._LSeries_Element__map, order=element.order())


class LSCoerceFromBase(Morphism):
    r'''
        Coercion morphism from the field of coefficients to the Laurent series ring.
    '''
    def __init__(self, codomain: LSeries_Ring):
        if not isinstance(codomain, LSeries_Ring):
            raise TypeError("The codomain must be a formal Laurent series ring")

        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> LSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        return self.codomain().element_class(self.codomain(), coefficients={0:element})


class LSConvertToBase(Morphism):
    r'''
        Conversion morphism from the Laurent series ring to its field of coefficients.
    '''
    def __init__(self, domain: LSeries_Ring):
        if not isinstance(domain, LSeries_Ring):
            raise TypeError("The domain must be a formal Laurent series ring")

        super().__init__(domain, domain.base())

    def _call_(self, element: LSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if (element - element[0]).is_zero() is True:
            return self.codomain()(element[0])
        else:
            raise TypeError("Impossible to convert the formal Laurent series to the base ring, as it has non-zero higher order terms.")


class LSCoerceBetweenBases(Morphism):
    r'''
        Coercion morphism between Laurent series fields with different base ring.
    '''
    def __init__(self, domain: LSeries_Ring, codomain: LSeries_Ring, map: Morphism):
        if not isinstance(domain, LSeries_Ring):
            raise TypeError("The domain must be a formal Laurent series ring")
        if not isinstance(codomain, LSeries_Ring):
            raise TypeError("The codomain must be a formal Laurent series ring")
        if not map.domain() == domain.base() or not map.codomain() == codomain.base():
            raise ValueError("Error in the format for the morphism")

        self.base_map = map

        super().__init__(domain, codomain)

    def _call_(self, element: LSeries_Element) -> LSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.type() == LSeries_Element.TYPES.polynomial:
            return self.codomain().element_class(self.codomain(),
                                                 coefficients={k: self.base_map(element[k]) for k in element._LSeries_Element__poly})
        elif element.type() == LSeries_Element.TYPES.dalgebraic:
            raise NotImplementedError("Coercion of differential algebraic formal laurent series between different bases is not yet implemented.")
        else: # default case
            new_map = lambda k: self.base_map(element[k])
            return self.codomain().element_class(self.codomain(),
                                                 coefficient_map=new_map, order=element.order())


class LSCoerceFromPoly(Morphism):
    r'''
        Coercion morphism from the polynomial ring naturally embedded in the Laurent series ring to the Laurent series ring.
    '''
    def __init__(self, codomain: LSeries_Ring):
        if not isinstance(codomain, LSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        domain = codomain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: Element) -> DPolynomial:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        # element is a univariate polynomial
        return self.codomain().element_class(self.codomain(),
                                             coefficients={k: element[k] for k in range(element.degree()+1)})


class LSConvertToPoly(Morphism):
    r'''
        Conversion morphism from the Laurent series ring to the polynomial ring that is naturally embedded into the Laurent series
    '''
    def __init__(self, domain: LSeries_Ring):
        if not isinstance(domain, LSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: LSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.type() != LSeries_Element.TYPES.polynomial:
            raise ValueError("The element must be finite to convert it to a polynomial")
        elif element.order() < 0:
            raise ValueError("The element must be a polynomial (no negative orders) to convert it to a polynomial")
        
        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(element[k]) * x**k for k in element._LSeries_Element__poly)


class LSCoerceFromRational(Morphism):
    r'''
        Coercion morphism from the field of rational functions naturally embedded in the Laurent series ring to the Laurent series ring.
    '''
    def __init__(self, codomain: LSeries_Ring):
        if not isinstance(codomain, LSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")

        super().__init__(codomain.rat_field(), codomain)

    def _call_(self, element: Element) -> DPolynomial:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        num = self.codomain().poly_ring()(element.numerator())
        den = self.codomain().poly_ring()(element.denominator())

        return num / den
    

class LSConvertToRational(Morphism):
    r'''
        Conversion morphism from the Laurent series ring to the field of rational functions that is naturally embedded into the Laurent series.
    '''
    def __init__(self, domain: LSeries_Ring):
        if not isinstance(domain, LSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.rat_field()
        super().__init__(domain, codomain)

    def _call_(self, element: LSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.type() != LSeries_Element.TYPES.polynomial:
            raise ValueError("The element must be finite to convert it to a rational function")
        
        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(element[k]) * x**k for k in element._LSeries_Element__poly)
 
