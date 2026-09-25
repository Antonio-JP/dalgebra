from __future__ import annotations

r'''
    Module to create univariate formal Puiseux series over a given differential field.

    A formal Puiseux series is a generalization of a formal Laurent series where fractional
    (rational) powers of the generator are allowed. Concretely, for a ramification index `e \in \mathbb{Z}_{>0}`,
    an element of this ring has the form

    .. MATH::

        f(x) = \sum_{n \geq o} a_n x^{n/e},

    where `o \in \mathbb{Z}` and `a_n` are elements of the base differential field. Different elements of the same
    ring may use different ramification indices: the whole ring is (conceptually) the union `\bigcup_{e} F((x^{1/e}))`.

    TODO (puiseux): Add examples and more detailed explanation of the structure.

    TODO (puiseux): implement Puiseux series not only for a differential field but also for a difference field.
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

from sage.arith.functions import lcm
from sage.arith.misc import GCD as gcd
from sage.categories.commutative_algebras import CommutativeAlgebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
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
from ..dring import AdditiveMap, DRings, DifferentialRing

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)

logger = logging.getLogger(__name__)

#################################################################################
###
### BOUNDS MANAGEMENT FOR PUISEUX DIFFERENTIAL FIELDS
###
#################################################################################
PS_GLOBAL_BOUND = 20


def PSChangeBound(bound: int):
    r'''
        Changes the global bound for computations in formal Puiseux series.

        ::NO EXAMPLE::
    '''
    global PS_GLOBAL_BOUND
    if bound not in ZZ or bound < 3:
        raise ValueError(f"The bound must be a non-negative integer, got {bound}.")
    PS_GLOBAL_BOUND = bound


def CheckBound(func):
    r'''
        Wrapper to check the bound argument.

        This is a decorator to check that the method has a bound argument, that it is set and call properly. This
        simplifies and unifies the check of this type of argument which appears naturally throughout the module.

        ::NO EXAMPLE::
    '''
    from functools import wraps

    @wraps(func)
    def wrapper(self: PuiseuxSeries_Element | PuiseuxSeries_Ring, *args, **kwds):
        import inspect
        sig = inspect.signature(func)
        if "bound" not in sig.parameters:
            raise TypeError(f"The method {func.__name__} does not accept a 'bound' argument.")
        elif sig.parameters["bound"].default is not None:
            raise TypeError(f"The method {func.__name__} does not accept a default value for 'bound'.")
        value = kwds.pop("bound") if "bound" in kwds else PS_GLOBAL_BOUND

        if value not in ZZ or value < 0:
            raise TypeError(f"The method {func.__name__} requires a non-negative integer 'bound' argument to be passed.")

        kwds["bound"] = value

        return func(self, *args, **kwds)
    return wrapper

def rat_range(start, end=None, step=None):
    r'''
        Generate a range of rational numbers. It follows the same conventions as the Python ``range`` function.

        ::NO EXAMPLE::
    '''
    step = QQ(1) if step is None else QQ(step)
    start, end = (QQ(start), QQ(end)) if end is not None else (QQ(0), QQ(start))
    current = start
    check = (lambda x: x < end) if step > 0 else (lambda x: x > end)
    while check(current):
        yield current
        current += step

#################################################################################
###
### FACTORY FOR PUISEUX DIFFERENTIAL FIELDS
###
#################################################################################
class PuiseuxSeriesFactory(UniqueFactory):
    r'''
        Factory to create the ring of Puiseux series over a differential field.

        This allows to cache the same rings created from different objects. See
        :class:`PuiseuxSeries_Ring` for further information on this structure.
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
        elif base.constant_ring() != base:
            raise TypeError("The base must be a differential ring with trivial constants")

        if name is None and "names" in kwds:
            if len(kwds["names"]) != 1:
                raise ValueError("You must provide exactly one name for the generator of the formal Puiseux series ring.")
            name = kwds["names"][0]

        if name is None:
            raise TypeError("You must provide a name for the generator of the formal Puiseux series ring.")
        elif name in (str(v) for v in base.gens()):
            raise TypeError(f"The given name ({name}) already exist in the base ring.")

        # Now the names are appropriate and the base is correct
        return (base, name)

    def create_object(self, _, key) -> PuiseuxSeries_Ring:
        r'''
            See :func:`UniqueFactory.create_object` for more information.

            ::NO EXAMPLE::
        '''
        base, name = key

        return PuiseuxSeries_Ring(base, name)


PuiseuxSeries = PuiseuxSeriesFactory("dalgebra.dextension.puiseux.PuiseuxSeries_Ring")


class PuiseuxSeries_Element(Element):
    r'''
        Class representing a formal Puiseux series.

        A formal Puiseux series is a formal sum over a fractional power of a given variable with coefficients in a
        field that will be considered as constants of the form

        .. MATH::

            f(x) = \sum_{n = o}^{\infty} a_n x^{n/e},

        where `o \in \mathbb{Z}` and `e \in \mathbb{Z}_{>0}` is the *ramification index* of the element (i.e., the
        denominator that is common to every exponent appearing in the series). Different elements of the same ring
        may have different ramification indices; arithmetic operations automatically bring both operands to a
        common ramification (the lcm of both) before combining them.

        We allow four different ways to create a formal Puiseux series:

        1. By providing a ``coefficient_map``, which is a callable that receives an integer `n` (the numerator at
           the element's own ramification) and returns the corresponding coefficient `a_n`. This is the most
           generic way to create a formal Puiseux series. We never have a criteria for zero testing.
        2. By providing a finite list or map of elements as ``coefficients`` (again indexed by the integer
           numerator `n`). This creates a finite formal Puiseux polynomial, and all computations are exact.
        3. By providing two Puiseux series (as ``numerator`` and ``denominator``) that are finite (i.e., Puiseux polynomials). 
           The resulting series is the quotient of the two, and all computations are exact.
        4. TODO (puiseux): By providing a differential polynomial in one variable with coefficients in the
           constant field, together with a set of initial conditions.
    '''
    TYPES = Enum('Type', [("default",0), ("polynomial", 1), ("rational", 2), ("dalgebraic", 3)])

    def __init__(self, parent: PuiseuxSeries_Ring, *,
                 ramification: int = None,
                 coefficient_map: Callable[[Rational],Element] | None = None, order: Rational | None = None,
                 coefficients: Collection[Element] | Mapping[Rational, Element] | None = None,
                 numerator: PuiseuxSeries_Element | None = None, denominator: PuiseuxSeries_Element | None = None,
                 differential_equation = None, initial_conditions: Collection[Element] | Mapping[Rational, Element] | None = None,
                 _reduce: bool = False,
    ):
        base = parent.base()

        if ramification not in ZZ or ramification <= 0:
            raise ValueError(f"The ramification index must be a positive integer, got {ramification}.")
        ramification = ZZ(ramification)

        default = ramification is not None and coefficient_map is not None and order is not None
        polynomial = coefficients is not None
        quotient = numerator is not None and denominator is not None
        dalgebraic = ramification is not None and differential_equation is not None and initial_conditions is not None

        if not any((default, polynomial, quotient, dalgebraic)):
            raise TypeError("You must provide at least one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).")
        elif sum((default, polynomial, quotient, dalgebraic)) > 1:
            raise TypeError("You can only provide one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).")

        if default or dalgebraic: # we make sure ramification makes sense
            if ramification not in ZZ or ramification <= 0:
                raise ValueError(f"The ramification index must be a positive integer, got {ramification}.")

        if default:
            self.__type = self.TYPES.default
            self.__map = coefficient_map
            self.__order = QQ(order)
            self.__polydict = None
            self.__numerator = self
            self.__denominator = self.parent().one()
            self.__dalgebraic = None
            self.__ramification = ramification
        elif polynomial:
            ## We process the argument "coefficients"
            if not isinstance(coefficients, Mapping):
                poly = {QQ(i): base(c) for (i,c) in enumerate(coefficients) if base(c) != base.zero()}
            else:
                poly = {QQ(k): base(v) for k, v in coefficients.items() if base(v) != base.zero()}

            self.__type = self.TYPES.polynomial
            self.__polydict = poly
            self.__map = lambda q : self.__polydict.get(q, base.zero())
            self.__numerator = self
            self.__denominator = self.parent().one()
            self.__order = min(poly) if len(poly) > 0 else oo
            self.__dalgebraic = None
            self.__ramification = lcm(k.denominator() for k in poly) if len(poly) > 0 else ZZ(1)
        elif quotient:
            numerator, denominator = self.parent()(numerator), self.parent()(denominator)
            #if any(element.type() != self.TYPES.polynomial for element in (numerator, denominator)):
            #    raise TypeError(f"The numerator and denominator must be finite formal Puiseux series (i.e., polynomials). Got {numerator.type()} and {denominator.type()}.")
            # TODO (series): check all uses of numerator and denominator are valid for non-polynomial cases.

            self.__type = self.TYPES.rational
            self.__numerator = numerator
            self.__denominator = denominator
            if _reduce:
                self.reduce_rational()

            self.__map = (numerator * ~denominator).__map
            self.__polydict = None
            self.__order = numerator.order() - denominator.order() # this is an exact computation
            self.__dalgebraic = None
            self.__ramification = lcm(numerator.ramification(), denominator.ramification())

        else: # dalgebraic
            raise NotImplementedError("Differential algebraic formal Puiseux series are not yet implemented.")

        ## We create a cache for computed elements
        self.__cache_computed: Mapping[Rational, Element] = dict()

        super().__init__(parent)
    
    ###################################################################################
    ### Ramification handling
    ###################################################################################
    def ramification(self) -> int:
        r'''
            Return the ramification index of ``self``, i.e., the denominator common to every exponent in the series.
        '''
        return self.__ramification

    ###################################################################################
    ### Private methods (working with the internal integer numerator)
    ###################################################################################
    def _coeff(self, n: Rational) -> Element:
        r'''
            Return the coefficient of the term `x^{n}`. The number `n` may be rational.

            ::NO EXAMPLE::
        '''
        if n not in self.__cache_computed:
            ## We check the ramification
            n = QQ(n)
            p,q = n.numerator(), n.denominator()
            if p*self.ramification() % q != 0: # this index is not in the ramification, hence, a zero is returned
                self.__cache_computed[n] = self.parent().base().zero() 
            elif n < self.order(): # this index is below the order, then we return zero
                self.__cache_computed[n] = self.parent().base().zero()
            else: # otherwise, we return the output of the map
                self.__cache_computed[n] = self.__map(n)

        return self.__cache_computed[n]

    @CheckBound
    def order(self, *, bound: int | None = None) -> int:
        r'''
            Return the lowest exponent `n` with `a_n \neq 0` (or ``bound`` if this cannot be resolved).

            ::NO EXAMPLE::
        '''
        if self.type() == self.TYPES.default:
            # Here we only know that all terms smaller than self.__order are zero.
            # We check the following terms until the bound
            for n in rat_range(self.__order, bound+1/self.ramification(), 1/self.ramification()):
                if self._coeff(n) != self.parent().base().zero():
                    self.__order = n # we update the data for the order
                    return n
            return bound
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational):
            return self.__order # computed on initialization
        else: # dalgebraic
            raise NotImplementedError("Order computation for differential algebraic formal Puiseux series is not yet implemented.")

    def degree(self) -> int:
        r'''
            Return the highest exponent `n` with `a_n \neq 0` (only defined for finite series).

            ::NO EXAMPLE::
        '''
        if not self.type() == self.TYPES.polynomial:
            raise TypeError("Degree is only defined for finite formal Puiseux series.")
        return max(self.__polydict) if len(self.__polydict) > 0 else -oo

    def numerator(self) -> PuiseuxSeries_Element:
        r'''
            Return the numerator of a formal Puiseux series.

            It is defined generically, but we only return something different than ``self`` if 
            it is a rational Puiseux series.

            ::NO EXAMPLE::
        '''
        if self.type() != self.TYPES.rational:
            return self
        return self.__numerator

    def denominator(self) -> PuiseuxSeries_Element:
        r'''
            Return the denominator of a formal Puiseux series.

            It is defined generically, but we only return something different than ``1`` if 
            it is a rational Puiseux series.

            ::NO EXAMPLE::
        '''
        if self.type() != self.TYPES.rational:
            return self.parent().one()
        return self.__denominator
    
    def gen_mult(self, n: Rational) -> PuiseuxSeries_Element:
        r'''
            Multiply ``self`` by the generator raised to the power ``n`` (i.e., shift all internal keys by ``n``).

            ::NO EXAMPLE::
        '''
        n = QQ(n)
        if n == 0:
            return self
        elif self.type() == self.TYPES.polynomial:
            return self.parent().element_class(self.parent(),
                coefficients={k + n: c for k, c in self.__polydict.items()}, ramification=self.ramification())
        elif self.type() == self.TYPES.rational:
            return self.parent().element_class(self.parent(),
                numerator=self.__numerator.gen_mult(n), denominator=self.__denominator)
        elif self.type() == self.TYPES.dalgebraic:
            raise NotImplementedError("Multiplication by the generator for differential algebraic formal Puiseux series is not yet implemented.")
        else: # default
            return self.parent().element_class(self.parent(),
                coefficient_map=lambda k: self._coeff(k - n), order=self.__order + n, 
                ramification=lcm(self.ramification(), n.denominator()))

    @CheckBound
    def _split_num(self, *, bound: int | None = None) -> tuple[int, PuiseuxSeries_Element]:
        r'''
            Splits ``self`` into the numerator order and the (same ramification) series with that order removed.

            ::NO EXAMPLE::
        '''
        order = self._order_num(bound=bound)
        return (order, self._shift_num(-order))

    ###################################################################################
    ### Public property methods (working with the actual rational exponent)
    ###################################################################################
    @CheckBound
    def is_zero(self, *, bound: int | None = None) -> bool | int: #: Checker for the zero element
        r'''
            Checker for the zero element of the ring.

            This method checks whether the element is zero or not. If exact computation are possible, it returns ``True`` or ``False``.
            Otherwise it returns the last checked order for which the element is zero.
        '''
        if self.type() == self.TYPES.default:
            if any(
                self._coeff(k) != self.parent().base().zero() 
                for k in rat_range(self.order(bound=bound), bound+1/self.ramification(), 1/self.ramification())
            ):
                return False
            return bound
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational):
            return self.order() == oo
        else: # dalgebraic
            raise NotImplementedError("Zero checking for differential algebraic formal Puiseux series is not yet implemented.")

    @CheckBound
    def is_one(self, *, bound: int | None = None) -> bool | int:
        r'''
            Checker for the identity element.

            See :func:`is_zero` for more information on the output of this type of methods.
        '''
        return (self - self.parent().one()).is_zero(bound=bound)

    @CheckBound
    def is_unit(self, *, bound: int | None = None) -> bool:
        r'''
            Checker for whether the element is a unit or not.

            Puiseux series form a field, hence all non-zero elements are units.
        '''
        return (self.is_zero(bound=bound) is False)

    def type(self) -> PuiseuxSeries_Element.TYPES:
        r'''
            Method to get the type of formal power series.
        '''
        return self.__type

    def is_finite(self) -> bool: ## TODO (series) Check the use of the method `is_finite`
        r'''
            Method to check whether the formal power series is finite or not.
        '''
        return self.type() in (self.TYPES.polynomial, self.TYPES.rational)

    @CheckBound
    def is_monomial(self, *, bound: int | None = None) -> bool | int:
        r'''
            Checks whether an element is a monomial (a series with only one non-zero term) or not.

            IMPORTANT: Zero is NOT a monomial

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = 3*x**2
                sage: f.is_monomial()
                True
                sage: f = x**2 + 2*x + 1
                sage: f.is_monomial()
                False
                sage: f = x**(1/2)
                sage: f.is_monomial()
                True
        '''
        if self.type() == self.TYPES.polynomial:
            return len(self.__polydict) == 1
        elif self.type() == self.TYPES.rational:
            return self.is_monomial(bound=bound) and self.denominator().is_monomial(bound=bound)
        else:
            zero = self.is_zero(bound=bound+1)
            if zero == bound+1:
                return bound+1
            return (self - self.trailing_term()).is_zero(bound=bound)        

    def truncate(self, order: Rational | int) -> PuiseuxSeries_Element:
        r'''
            Return a :class:`PuiseuxSeries_Element` that contains only the coefficients with exponent at most ``order``.

            This method always returns a polynomial formal Puiseux series, even if the original one is not polynomial.
        '''
        coeffs = {k: self[k] for k in rat_range(self.order(), QQ(order)+1/self.ramification(), 1/self.ramification())}
        return self.parent().element_class(self.parent(), coefficients=coeffs)

    def polynomial(self) -> Element:
        r'''
            Converts (if possible) a Puiseux series into a polynomial. It requires three different conditions:
            * the ramification to be 1,
            * the element to be of polynomial type,
            * the order must be non-negative.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = x**2 + 2*x + 1
                sage: P = R.poly_ring()
                sage: X = P.gen()
                sage: f.polynomial() == X**2 + 2*X + 1
                True

            TODO (series): add examples that raises some error.
        '''
        if self.ramification() != 1:
            raise TypeError("Only Puiseux series with trivial ramification (i.e., formal Laurent series) can be converted to a polynomial.")
        elif self.type() != self.TYPES.polynomial:
            raise TypeError("The element is not a polynomial.")
        elif self.order() < 0:
            raise TypeError("The element is not a polynomial (it has negative order).")

        var = self.parent().poly_ring()(self.parent().variable_name())
        return sum(coeff * var**k for (k,coeff) in self.__polydict.items())

    def rational_function(self) -> Element:
        r'''
            Converts (if possible) a Puiseux series into a rational function. It requires two different conditions:
            * the ramification to be 1,
            * both numerator and denominator to be polynomials.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = ~x - 1 # (1/x) - 1 = (1 - x)/x
                sage: T = R.rat_field()
                sage: X = T.gen()
                sage: f.rational_function() == (1 - X)/X
                True
                
            TODO (series): add examples that raises some error.
        '''
        ## The method polynomial checks the conditions for both numerator and denominator
        return self.__numerator.polynomial() / self.__denominator.polynomial()

    def equation(self):
        r'''
            Gets the differential equation that defines the element. (Not always possible)
        '''
        raise NotImplementedError("Differential algebraic formal Puiseux series are not yet implemented.")

    @CheckBound
    def trailing_coefficient(self, *, bound: int | None = None) -> Element:
        r'''
            Method to get the trailing coefficient of a formal Puiseux series.

            The trailing coefficient is the coefficient of the monomial with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.
        '''
        order = self._order_num(bound=bound+1)
        if order == bound+1:
            return self.parent().base().zero()
        else:
            return self[order]

    @CheckBound
    def trailing_term(self, *, bound: int | None = None) -> PuiseuxSeries_Element:
        r'''
            Method to get the trailing term of a formal Puiseux series.

            The trailing term is the monomial with its coefficient with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.
        '''
        order = self._order_num(bound=bound+1)
        if order == bound+1:
            return self.parent().zero()
        else:
            return self.parent().element_class(self.parent(), coefficients={order: self[order]})

    @CheckBound
    def pseries_split(self, *, bound: int | None = None) -> tuple[Rational | int, PuiseuxSeries_Element]:
        r'''
            Splits the formal Puiseux series into the product of a power of the generator and a formal power series with non-zero constant term.

            This is a method that may not be exact, hence, if we can not compute fully the power of the generator, we return the last computed order.
        '''
        order = self.order(bound=bound)
        return (order, self.gen_mult(-order))

    def __getitem__(self, key: Rational | int) -> Element:
        if isinstance(key, slice):
            start = QQ(key.start) if key.start is not None else QQ(0)
            stop = key.stop if key.stop is not None else oo
            step = QQ(key.step) if key.step is not None else QQ(1)

            if stop == oo:
                raise ValueError(f"Infinite slice requested. Impossible to compute.")

            return [self[i] for i in rat_range(start, stop, step)]

        exponent = QQ(key)
        return self._coeff(exponent)

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._add_` for further information.

            ::NO EXAMPLE::
        '''
        ## Checking for trivial cases
        if self.is_zero() is True:
            return other
        elif other.is_zero() is True:
            return self

        E = lcm(self.ramification(), other.ramification())
        s = self._rescaled_to(E)
        o = other._rescaled_to(E)

        if any(el.type() == self.TYPES.default for el in (self, other)):
            # at least one is default -> we change to default
            add_map = lambda k : s._coeff(k) + o._coeff(k)
            return self.parent().element_class(
                self.parent(), 
                coefficient_map=add_map, 
                order=min(self.order(), other.order()), 
                ramification=lcm(self.ramification(), other.ramification()))
        elif self.type() == self.TYPES.polynomial and other.type() == self.TYPES.polynomial:
            # both are polynomials -> we can add in the keys of the dict
            new_dict = self.__polydict.copy()
            for k,v in other.__polydict.items():
                new_dict[k] = new_dict[k] + v if k in new_dict else v
            return self.parent().element_class(self.parent(), coefficients=new_dict)
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational) and other.type() in (self.TYPES.polynomial, self.TYPES.rational):
            # both are rational -> we can compute rationally, hoping for good behavior
            new_num = self.numerator() * other.denominator() + other.numerator() * self.denominator()
            new_den = self.denominator() * other.denominator()
            return self.parent().element_class(self.parent(), numerator=new_num, denominator=new_den)
        else: # at least one is dalgebraic
            raise NotImplementedError("Addition of differential algebraic formal Puiseux series is not yet implemented.")

    def __neg__(self) -> PuiseuxSeries_Element:
        if self.is_zero() is True:
            return self
        if self.type() == self.TYPES.polynomial:
            coeffs = {k: -c for k, c in self.__polydict.items()}
            return self.parent().element_class(self.parent(), coefficients=coeffs, ramification=self.ramification())
        elif self.type() == self.TYPES.rational:
            return self.parent().element_class(self.parent(), numerator=-self.__numerator, denominator=self.__denominator)
        elif self.type() == self.TYPES.dalgebraic:
            raise NotImplementedError("Negation of differential algebraic formal Puiseux series is not yet implemented.")
        else:
            return self.parent().element_class(self.parent(), coefficient_map=lambda k : -self._coeff(k), order=self.__order, ramification=self.ramification())

    def _sub_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._sub_` for further information.

            ::NO EXAMPLE::
        '''
        return self + (-other)

    def _mul_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
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
        elif self in self.parent().base() and other in self.parent().base(): # multiplication of scalars
            return self.parent()(self.parent().base()(self) * self.parent().base()(other))
        elif self in self.parent().base(): # scalar product (self)
            scalar = self.parent().base()(self)
            if other.type() == self.TYPES.polynomial:
                return self.parent().element_class(self.parent(), coefficients={k: scalar * c for k, c in other.__polydict.items()}, ramification=other.ramification())
            elif other.type() == self.TYPES.rational:
                return self.parent().element_class(self.parent(), numerator=scalar * other.__numerator, denominator=other.__denominator)
            elif other.type() == self.TYPES.dalgebraic:
                raise NotImplementedError("Multiplication of differential algebraic formal Puiseux series is not yet implemented.")
            else: # default
                return self.parent().element_class(self.parent(), coefficient_map=lambda k: scalar * other._coeff(k), order=other.order(), ramification=other.ramification())
        elif other in self.parent().base(): # scalar product (other)
            return other * self
        elif self.is_monomial() is True: # multiplication by monomial (self)
            order = self.order() # this computation is now exact
            return self[order] * other.gen_mult(order)
        elif other.is_monomial() is True: # multiplication by monomial (other)
            return other * self
        elif any(el.type() == self.TYPES.default for el in (self, other)): # multiplication when at least one is default
            E = lcm(self.ramification(), other.ramification())
            t = self.order()
            s = other.order()
            mul_map = lambda k : sum(self[i]*other[k-i] for i in rat_range(t, k+1/E, 1/self.ramification()))
            return self.parent().element_class(self.parent(), coefficient_map=mul_map, order=t+s, ramification=E)
        elif self.type() == self.TYPES.polynomial and other.type() == self.TYPES.polynomial: # multiplication of polynomials
            out = dict()
            for k1, c1 in self.__polydict.items():
                for k2, c2 in other.__polydict.items():
                    exp = k1 + k2
                    out[exp] = out[exp]+c1*c2 if exp in out else c1*c2
            return self.parent().element_class(self.parent(), coefficients=out)
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational) and other.type() in (self.TYPES.polynomial, self.TYPES.rational): # multiplication of rationals
            new_num = self.numerator() * other.numerator()
            new_den = self.denominator() * other.denominator()
            return self.parent().element_class(self.parent(), numerator=new_num, denominator=new_den)
        else: # at least one is dalgebraic and none is default
            raise NotImplementedError("Multiplication of differential algebraic formal Puiseux series is not yet implemented.")

    def _div_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._div_` for further information.

            ::NO EXAMPLE::
        '''
        ## full division and floor division coincide in fields
        return self // other

    def _floordiv_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._floordiv_` for further information.

            ::NO EXAMPLE::
        '''
        ## Division is done via the `rational` type of series
        if self.is_zero() is True:
            return self.parent().zero()
        elif other.is_zero() is True:
            raise ZeroDivisionError(f"Division by zero element is not allowed.")
        elif other in self.parent().base(): # simple scalar division
            scalar = (~self.parent().base()(other))
            return scalar * self
        else:
            ## default case (we keep track of numerator and denominator)
            new_num = self.numerator() * other.denominator()
            new_den = self.denominator() * other.numerator()
            return self.parent().element_class(self.parent(), numerator=new_num, denominator=new_den)

    @cached_method
    def __invert__(self) -> PuiseuxSeries_Element:
        r'''
            Computes the multiplicative inverse of the formal Puiseux series as a series

            This is important to distinguish between this method and :func:`__floordiv__`, which 
            keeps the rational structure for simpler computations. This computes the series
            expansion as a map, and creates a default type of series (except when a polynomial type can be obtained).
        '''
        if self.is_zero() is True:
            raise ZeroDivisionError(f"Inverse of zero element do not exist.")
        elif self.is_monomial() is True: # the only case where exact computation can be performed
            n0 = self.order() # this computation is now exact
            return self.parent().element_class(self.parent(), coefficients={-n0: ~self[n0]})

        E = self.ramification()
        order = self.order()

        if self[order] == 0: # we can not compute inverse: this seems the zero series
            raise ZeroDivisionError(f"Could not say if an element is zero or not.")

        to_div = ~self[order]
        @lru_cache(maxsize=256)
        def inverse_coeffs(k: Rational) -> Element:
            L = E*QQ(k) + order
            if L not in ZZ or L < 0:
                return self.parent().base().zero()
            elif L == 0:
                return to_div
            else: # L is a positive integer and we can compute the coefficient recursively
                return -to_div * sum(self[order + i/E] * inverse_coeffs(k-i/E) for i in range(1, L+1))

        return self.parent().element_class(self.parent(), coefficient_map=inverse_coeffs, order=-order, ramification=E)

    @cached_method
    def __pow__(self, power: int | Rational) -> PuiseuxSeries_Element:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            return self.parent().one() / (self)**(-power)
        elif power not in ZZ:
            if power not in QQ:
                raise ValueError(f"Power {power} is not a rational number, only rational powers are allowed in pseudo-differential operators.")
            power = QQ(power)
            n = power.numerator()
            m = power.denominator()

            if n == 1: # n-root case
                if self.is_zero() is True:
                    return self.parent().zero()
                elif self.is_zero() is not False:
                    raise ValueError(f"Could not say if an element is zero or not.")

                ## We use the following formula: if g(x) = f(x)^{1/m}, then we have that
                ## g'(x) = 1/m * g(x) / f(x) * f'(x), which provides a recursive formula for the coefficients of g(x).
                ## Namely, if we look for the coefficient of x^{k/m-1} of g'(x), we get (k/m) * g_{k/m}
                ## On the other hand, we get a formula for the same coefficient of the right hand side formula which only uses
                ## coefficients of g(x) up to order (k-1)/m.                 
                order = self.order() # order `d` of f(x)
                e = self.ramification() # ramification of f(x)
                inv = ~self # inverse power series: order is `-d` and its ramification is still `e`
                b_0 = self[order]**(QQ((1,m))) # the coefficient of g(x) at order `d/m` is b_0 = a_d^{1/m}

                # we compute the parent where the output will live
                out_parent = pushout(self.parent(), b_0.parent())

                ## g(x) = f(x)^{1/m} has order `d/m` and ramification `e*m`
                g_order = order / m
                g_ramification = e * m
                @lru_cache(maxsize=256)
                def root_coeffs(k: Rational) -> Element:
                    if k < order / m or (k.numerator()*g_ramification) % k.denominator() != 0:
                        # low order or out of ramification case
                        return self.parent().base().zero()
                    elif k == order / m:
                        return b_0
                    else:
                        kn = k.numerator()*g_ramification // k.denominator() # exact division
                        output = e/kn
                        to_mult = out_parent.base().zero()
                        for i in rat_range(g_order, k - 1 + 1/g_ramification, 1/g_ramification):
                            to_add = out_parent.base().zero()
                            for j in rat_range(order, order + k - i + 1/e, 1/e):
                                to_add += (j+1) * self[j+1] * inv[k - i - j]
                            to_mult += root_coeffs(i)*to_add
                        output *= to_mult
                        return output
                return self.parent().element_class(
                    self.parent(), 
                    coefficient_map=root_coeffs, 
                    order=g_order, 
                    ramification=g_ramification
                )
            else: # general case
                return (self**n)**(QQ((1,m)))
        else: # divide-and-conquer strategy
            a,A = (self**(power//2 + power % 2), self**(power//2))
            return a*A

    ## TODO Go on here

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
        if self.type() == self.TYPES.polynomial:
            new_poly = {k: el(**kwds) for (k,el) in self.__polydict.items()}
            return self.parent().element_class(self.parent(), coefficients=new_poly, ramification=self.ramification())
        elif self.type() == self.TYPES.default:
            new_func = lambda n : self._coeff(n)(**kwds)
            return self.parent().element_class(self.parent(), coefficient_map=new_func, order=self.__order, ramification=self.ramification())
        else:
            raise ValueError("Impossible type for a Puiseux series")

    def reduce_rational(self) -> None:
        r'''
            Method that reduces as much as possible a quotient of Puiseux series.    

            IMPORTANT: this method can only access and change the attributes ``__numerator`` and ``__denominator`` of the object.
        '''
        if self.type() != self.TYPES.rational:
            return self # nothing to be done without a denominator
        else:
            raise NotImplementedError("Reduction of rational Puiseux series is not yet implemented.")

    ###################################################################################
    @CheckBound
    def __repr__(self, *, bound: int | None = None) -> str:
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()
        e = self.ramification()

        def operator_repr(n: int) -> str:
            exponent = QQ((n, e))
            if exponent == 0:
                return "1"
            elif exponent == 1:
                return f"{g}"
            else:
                return f"{g}^({exponent})"

        def term_str(n: int, element:Element, first:bool=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""

            op_str = operator_repr(n)
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

                if op_str == "1": # constant term: no need to append the (trivial) monomial
                    output = f"{sign}{el_str}"
                else:
                    join = "*" if all(len(part) > 0 for part in (el_str, op_str)) else ""
                    output = f"{sign}{el_str}{join}{op_str}"
            return output

        if self.type() == self.TYPES.polynomial:
            ## We print everything
            ## polynomial that is not zero: it has a finite order
            order = self._order_num()
            return term_str(order, self._coeff(order),True) + "".join(
                term_str(k, self._coeff(k))
                for k in range(order+1, max(self.__polydict)+1)
                if self._coeff(k) != 0
            )
        else:
            order = self._order_num(bound=bound+1)

            if order == bound+1:
                return f"O({operator_repr(bound+1)})"

            return term_str(order, self._coeff(order), True) + "".join(
                term_str(k, self._coeff(k))
                for k in range(order+1, bound+1)
                if self._coeff(k) != 0
            ) + (f" + O({operator_repr(bound+1)})")

    @CheckBound
    def _latex_(self, *, bound: int | None = None) -> str:
        r'''
            Computes a LaTeX string to represent the formal Puiseux series.

            ::NO EXAMPLE::
        '''
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()
        e = self.ramification()

        def operator_str(n: int):
            exponent = QQ((n, e))
            if exponent == 0:
                return "1"
            elif exponent == 1:
                return f"{latex_variable_name(g)}"
            else:
                return f"{latex_variable_name(g)}^{{{latex(exponent)}}}"

        def term_str(n, element, first=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""
            ## If the element is 1, we just return the monomial
            if element == 1:
                output = (" + " if not first else "") + operator_str(n)
            elif element == -1:
                output = (" - " if not first else "") + operator_str(n)
            else: # element is something != 1
                op_str = operator_str(n)
                if str(element)[0] == "-":
                    sign = " - " if not first else "-"
                    element = -element
                else:
                    sign = " + " if not first else ""

                if any(char in str(element) for char in ("+", "/", "*", "-", " ")): # case with several terms
                    el_str = f"\\left({latex(element)}\\right)"
                else:
                    el_str = latex(element)

                output = f"{sign}{el_str}" if op_str == "1" else f"{sign}{el_str}{op_str}"
            return output

        if self.type() == self.TYPES.polynomial:
            ## We print everything
            ## polynomial that is not zero: it has a finite order
            order = self._order_num()
            return term_str(order, self._coeff(order),True) + "".join(
                term_str(k, self._coeff(k))
                for k in range(order+1, max(self.__polydict)+1)
                if self._coeff(k) != 0
            )
        else:
            ## We print at least 3 terms up to order -bound
            order = self._order_num(bound=bound+1)
            if order == bound+1:
                return f"\\text{{O}}({operator_str(bound+1)})"

            return term_str(order, self._coeff(order), True) + "".join(
                term_str(k, self._coeff(k))
                for k in range(order+1, bound+1)
                if self._coeff(k) != 0
            ) + (f" + \\text{{O}}({operator_str(bound+1)})")


class PuiseuxSeries_Ring(Parent):
    r'''
        Class for a field of Puiseux series over a :class:`~dalgebra.dring.DRing`.

        Given a field `F`, this ring represents the union `\bigcup_{e > 0} F((x^{1/e}))` of Laurent series fields
        in fractional powers of a new variable `x`. Elements carry their own ramification index; the derivation of
        `F` is extended naturally to `x` via the chain rule `d(x^{n/e}) = (n/e) x^{(n-e)/e}`.

        INPUT:

        * ``base``: a field with one derivative.
        * ``name``: name that the variable `x` will have.

        TODO (puiseux): add examples
    '''
    Element = PuiseuxSeries_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        r'''
            Method to generate the appropriate list of categories for ``self``

            ::NO EXAMPLE::
        '''
        return [_DRings, CommutativeAlgebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif isinstance(base, PuiseuxSeries_Ring):
            raise TypeError("The base must not be a formal Puiseux series ring")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")
        elif base.constant_ring() != base:
            raise TypeError("The base must be a differential ring with trivial constants")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.__operators = [self.__build_derivation()]
        self.__gen = self.element_class(self, ramification=1, coefficients={1: self.base().one()})
        self.__poly_ring = PolynomialRing(base.to_sage(), name)
        self.__rat_field = self.__poly_ring.fraction_field()

        ## Setting up basic conversions
        try:
            self.base().register_conversion(PSConvertToBase(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(PSCoerceFromPoly(self))
            self.poly_ring().register_conversion(PSConvertToPoly(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(PSCoerceFromRational(self))
            self.rat_field().register_conversion(PSConvertToRational(self))
        except AssertionError: # This conversion was already registered
            pass

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        r'''
            Return the string for representing the generator of the field of Puiseux series.
        '''
        return self.__gens[0]

    def gen(self) -> PuiseuxSeries_Element:
        r'''
            Return the generator of the field of Puiseux series.
        '''
        return self.__gen

    def gens(self) -> tuple[PuiseuxSeries_Element]:
        r'''
            Return the generators of the field of Puiseux series.
        '''
        return (self.__gen,)

    def ngens(self) -> int:
        r'''
            Return the number of generators of the field of Puiseux series.
        '''
        return 1

    def one(self) -> PuiseuxSeries_Element:
        r'''
            Return the identity element of the field of Puiseux series.
        '''
        return self.element_class(self, ramification=1, coefficients={0:self.base().one()})

    def zero(self) -> PuiseuxSeries_Element:
        r'''
            Return the zero element of the field of Puiseux series.
        '''
        return self.element_class(self, ramification=1, coefficients=dict())

    def is_field(self, proof: bool = True) -> bool:
        r'''
            Check if the field of Puiseux series is a field.
            This is always True.
        '''
        return True

    def is_integral_domain(self, proof: bool = True) -> bool:
        r'''
            Check if the field of Puiseux series is an integral domain.
            This is, by definition, True
        '''
        return True

    def poly_ring(self) -> Parent:
        r'''
            Return the polynomial ring associated to this field of formal Puiseux series (at trivial ramification).
        '''
        return self.__poly_ring

    def rat_field(self) -> Parent:
        r'''
            Return the field of rational functions associated to this field of formal Puiseux series (at trivial ramification).
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
        return PSCoerceFromBase(self)

    def construction(self) -> tuple[PuiseuxSeriesFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return PuiseuxSeriesFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        r'''
            See :func:`Parent.fraction_field` for further information.

            ::NO EXAMPLE::
        '''
        return self

    def change_base(self, R: Parent) -> PuiseuxSeries_Ring:
        r'''
            Method to change the base field for considering the series.

            This method takes into consideration the coercions between the old and the new base to create the appropriate coercion maps between the old and new Puiseux series rings.
        '''
        new_ring = PuiseuxSeries(R, self.gen_name())
        ## Creating the coercion map if possible
        try:
            M = PSCoerceBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Formal Puiseux Series Ring in {self.__gens[0]} over {self.base()}"

    def _latex_(self):
        r'''
            Computes a LaTeX representation for this field of Puiseux series.

            ::NO EXAMPLE::
        '''
        return f"{latex(self.base())}\\left(\\left({self.__gens[0]}^{{1/\\infty}}\\right)\\right)"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        up_bound : int = 0, lower_bound : int = 0, ramification: int = 1,
        *args,**kwds
    ) -> PuiseuxSeries_Element:
        r'''
            Creates a random element in this ring.

            This method receives a bound for the degree and order of the numerator (at the requested
            ``ramification``) and also extra arguments passed to the random method of the base ring.

            INPUT:

            * ``up_bound``: upper bound (numerator) for the resulting Puiseux polynomial.
            * ``lower_bound``: lower bound (numerator) for the resulting Puiseux polynomial.
            * ``ramification``: ramification index to be used for the random element.
        '''
        return self.element_class(self, ramification=ramification,
            coefficients={k: self.base().random_element(*args, **kwds) for k in range(lower_bound, up_bound+1)})

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

    def add_constants(self, *new_constants: str) -> PuiseuxSeries_Ring:
        r'''
            See :func:`DRings.ParentMethods.add_constants` for further information.

            ::NO EXAMPLE::
        '''
        return PuiseuxSeries(self.base().add_constants(*new_constants), self.__gens[0])

    def linear_operator_ring(self):
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            ::NO EXAMPLE::
        '''
        raise NotImplementedError("Linear operator ring over Formal Puiseux Series not yet implemented")

    def inverse_operation(self, element: PuiseuxSeries_Element, operation: int = 0) -> PuiseuxSeries_Element:
        r'''
            See :func:`DRings.ParentMethods.inverse_operation` for further information.

            ::NO EXAMPLE::
        '''
        raise NotImplementedError("Integration over Puiseux Series with non-constant coefficients not yet implemented")

    def __build_derivation(self) -> AdditiveMap:
        r'''
            Internal method to build the derivation of the field of Puiseux series.

            The chain rule gives `d(x^{n/e}) = (n/e) x^{(n-e)/e}` for a term with (internal) numerator `n` at
            ramification `e`.

            ::NO EXAMPLE::
        '''
        def derivation_map(element: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
            if element.is_zero() is True:
                return self.zero()
            e = element.ramification()
            if element.type() == element.TYPES.polynomial:
                order = element._order_num()
                degree = element._degree_num()
                out_dict = {order - e: QQ((order, e)) * element._coeff(order)}
                for k in range(order, degree+1):
                    out_dict[k] = out_dict.get(k, self.base().zero()) + element._coeff(k).derivative() + QQ((k+e, e))*element._coeff(k+e)
                return self.element_class(self, coefficients=out_dict, ramification=e)
            elif element.type() == element.TYPES.dalgebraic:
                raise NotImplementedError("Derivation of differential algebraic formal Puiseux series not yet implemented.")
            else:
                return self.element_class(self,
                    coefficient_map=lambda k: QQ((k+e, e))*element._coeff(k+e) + element._coeff(k).derivative(),
                    order=element._order_num()-e, ramification=e)

        return AdditiveMap(self, derivation_map)


class PuiseuxSeriesFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`PuiseuxSeries_Ring`.

        This class represents the functor `F: R \mapsto \bigcup_{e>0} R((x^{1/e}))`.
        The name of the variable must be given to the functor and, then
        this can take any differential field ring and create the corresponding field of Puiseux
        series.

        INPUT:

        * ``name``: name of the variable that the functor will add
    '''
    def __init__(self, name: str):
        self.__gen_name = name
        super().__init__(_DRings,_DRings)
        self.rank = 14 # just above LaurentSeriesFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        r'''
            See :func:`ConstructionFunctor._apply_functor` for further information.

            ::NO EXAMPLE::
        '''
        return PuiseuxSeries(x,self.__gen_name)

    def _repr_(self):
        r'''
            Return a str representing the functor.

            ::NO EXAMPLE::
        '''
        return f"PuiseuxSeries(*,{self.__gen_name})"

    def __eq__(self, other):
        if other.__class__ == self.__class__:
            return self.__gen_name == other.__gen_name
        return False


class PSCoerceFromBase(Morphism):
    r'''
        Coercion morphism from the field of coefficients to the Puiseux series ring.
    '''
    def __init__(self, codomain: PuiseuxSeries_Ring):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The codomain must be a formal Puiseux series ring")

        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        return self.codomain().element_class(self.codomain(), coefficients={0:element}, ramification=1)


class PSConvertToBase(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to its field of coefficients.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal Puiseux series ring")

        super().__init__(domain, domain.base())

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if (element - element[0]).is_zero() is True:
            return self.codomain()(element[0])
        else:
            raise TypeError("Impossible to convert the formal Puiseux series to the base ring, as it has non-zero higher order terms.")


class PSCoerceBetweenBases(Morphism):
    r'''
        Coercion morphism between Puiseux series fields with different base ring.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring, codomain: PuiseuxSeries_Ring, map: Morphism):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal Puiseux series ring")
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The codomain must be a formal Puiseux series ring")
        if not map.domain() == domain.base() or not map.codomain() == codomain.base():
            raise ValueError("Error in the format for the morphism")

        self.base_map = map

        super().__init__(domain, codomain)

    def _call_(self, element: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.type() == PuiseuxSeries_Element.TYPES.polynomial:
            return self.codomain().element_class(self.codomain(),
                                                 coefficients={k: self.base_map(v) for k, v in element._items()}, ramification=element.ramification())
        elif element.type() == PuiseuxSeries_Element.TYPES.dalgebraic:
            raise NotImplementedError("Coercion of differential algebraic formal Puiseux series between different bases is not yet implemented.")
        else: # default case
            new_map = lambda k: self.base_map(element._coeff(k))
            return self.codomain().element_class(self.codomain(),
                                                 coefficient_map=new_map, order=element._order_num(), ramification=element.ramification())


class PSCoerceFromPoly(Morphism):
    r'''
        Coercion morphism from the polynomial ring naturally embedded (at trivial ramification) in the Puiseux series ring.
    '''
    def __init__(self, codomain: PuiseuxSeries_Ring):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        domain = codomain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        # element is a univariate polynomial
        return self.codomain().element_class(self.codomain(),
                                             coefficients={k: element[k] for k in range(element.degree()+1)}, ramification=1)


class PSConvertToPoly(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to the polynomial ring that is naturally embedded (at trivial ramification) into it.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.ramification() != 1:
            raise ValueError("The element must have trivial ramification to convert it to a polynomial")
        elif element.type() != PuiseuxSeries_Element.TYPES.polynomial:
            raise ValueError("The element must be finite to convert it to a polynomial")
        elif element.order() < 0:
            raise ValueError("The element must be a polynomial (no negative orders) to convert it to a polynomial")

        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(v) * x**k for k, v in element._items())


class PSCoerceFromRational(Morphism):
    r'''
        Coercion morphism from the field of rational functions naturally embedded (at trivial ramification) in the Puiseux series ring.
    '''
    def __init__(self, codomain: PuiseuxSeries_Ring):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")

        super().__init__(codomain.rat_field(), codomain)

    def _call_(self, element: Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        num = self.codomain()(self.codomain().poly_ring()(element.numerator()))
        den = self.codomain()(self.codomain().poly_ring()(element.denominator()))

        return num / den


class PSConvertToRational(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to the field of rational functions that is naturally embedded (at trivial ramification) into it.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.rat_field()
        super().__init__(domain, codomain)

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.ramification() != 1:
            raise ValueError("The element must have trivial ramification to convert it to a rational function")
        elif element.type() != PuiseuxSeries_Element.TYPES.polynomial:
            raise ValueError("The element must be finite to convert it to a rational function")

        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(v) * x**k for k, v in element._items())
