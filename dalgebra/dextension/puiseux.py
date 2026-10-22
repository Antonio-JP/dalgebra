from __future__ import annotations

r'''
    Module to create univariate formal Puiseux series over a given differential field.

    A formal Puiseux series is a generalization of a formal Laurent series where fractional
    (rational) powers of the generator are allowed. Concretely, for a ramification index `e\in\mathbb{N}`, an element of this ring has the form

    .. MATH::

        f(x) = \sum_{n \geq o} a_n x^{n/e},

    where `o \in \mathbb{Z}` and `a_n` are elements of the base differential field. Different elements of the same
    ring may use different ramification indices: the whole ring is (conceptually) the union `\bigcup_{e} F((x^{1/e}))`.

    EXAMPLES::

        sage: from dalgebra import *
        sage: R = PuiseuxSeries(QQ, "x")
        sage: x = R.gen()
        sage: v = (~(1-x))**(1/3)
        sage: v.derivative() == (1/3)*v**4
        20

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
from sage.categories.pushout import pushout, ConstructionFunctor
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex, latex_variable_name
from sage.rings.infinity import Infinity as oo
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.puiseux_series_ring_element import PuiseuxSeries as PuiseuxSeriesElement
from sage.rings.puiseux_series_ring import PuiseuxSeriesRing
from sage.rings.rational_field import QQ
from sage.rings.rational import Rational
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Mapping, Callable
from ..dring import AdditiveMap, DerivationMap, DRings, DifferentialRing, IntegrationError

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

        EXAMPLES::

            sage: import dalgebra.dextension.puiseux as puiseux
            sage: old_bound = puiseux.PS_GLOBAL_BOUND
            sage: puiseux.PSChangeBound(4)
            sage: puiseux.PS_GLOBAL_BOUND
            4
            sage: puiseux.PSChangeBound(old_bound)
            sage: puiseux.PSChangeBound(2)
            Traceback (most recent call last):
            ...
            ValueError: The bound must be a non-negative integer, got 2.
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

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import CheckBound
            sage: @CheckBound
            ....: def _bounded(_, *, bound=None):
            ....:     return bound
            sage: _bounded(None, bound=4)
            4
            sage: _bounded(None, bound=-1)
            Traceback (most recent call last):
            ...
            TypeError: The method _bounded requires a non-negative integer 'bound' argument to be passed.
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

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import rat_range
            sage: list(rat_range(3))
            [0, 1, 2]
            sage: list(rat_range(3, 0, -QQ((1, 2))))
            [3, 5/2, 2, 3/2, 1, 1/2]
            sage: list(rat_range(2, 2))
            []
            sage: list(rat_range(0, 3, 0))
            Traceback (most recent call last):
            ...
            ValueError: rat_range() arg 3 must not be zero
    '''
    step = QQ(1) if step is None else QQ(step)
    if step == 0:
        raise ValueError("rat_range() arg 3 must not be zero")
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

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: PuiseuxSeries(QQ, 'x') is PuiseuxSeries(QQ, 'x')
                True
                sage: PuiseuxSeries(QQ, names=('x', 'y'))
                Traceback (most recent call last):
                ...
                ValueError: You must provide exactly one name for the generator of the formal Puiseux series ring.
                sage: PuiseuxSeries(ZZ, 'x')
                Traceback (most recent call last):
                ...
                TypeError: The base ring must be a field
                sage: PuiseuxSeries(QQ)
                Traceback (most recent call last):
                ...
                TypeError: You must provide a name for the generator of the formal Puiseux series ring.
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

        The interface to get a coefficient of the series is through the ``__getitem__`` method, which receives a rational number `n` and returns the coefficient `a_n` of the term `x^{n}`. If the term does not exist in the series, it returns zero.

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

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import PuiseuxSeries
            sage: R = PuiseuxSeries(QQ, 'x')
            sage: f = R.element_class(R, coefficients={QQ((-1, 2)): 2, 1: 3})
            sage: (f[QQ((-1, 2))], f[0], f.order(), f.degree(), f.ramification())
            (2, 0, -1/2, 1, 2)
            sage: f.is_finite()
            True
            sage: R.element_class(R)
            Traceback (most recent call last):
            ...
            TypeError: You must provide at least one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).
            sage: R.element_class(R, coefficients={}, ramification=1, coefficient_map=lambda _: 0, order=0)
            Traceback (most recent call last):
            ...
            TypeError: You can only provide one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).
            sage: R.element_class(R, ramification=0, coefficient_map=lambda _: 0, order=0)
            Traceback (most recent call last):
            ...
            ValueError: The ramification index must be a positive integer, got 0.
    '''
    TYPES = Enum('Type', [("default",0), ("polynomial", 1), ("rational", 2), ("dalgebraic", 3)])

    def __init__(self, parent: PuiseuxSeries_Ring, *,
                 ramification: int = None,
                 coefficient_map: Callable[[Rational],Element] | None = None, order: Rational | None = None,
                 coefficients: Collection[Element] | Mapping[Rational, Element] | None = None,
                 numerator: PuiseuxSeries_Element | None = None, denominator: PuiseuxSeries_Element | None = None,
                 differential_equation = None, initial_conditions: Collection[Element | tuple[Rational, Element]] | None = None, map : PSCoerceFromDRing | None = None,
                 _reduce: bool = False, _one = False
    ):
        base = parent.base()

        default = ramification is not None and coefficient_map is not None and order is not None
        polynomial = coefficients is not None
        quotient = numerator is not None and denominator is not None
        dalgebraic = differential_equation is not None and initial_conditions is not None and map is not None

        if not any((default, polynomial, quotient, dalgebraic)):
            raise TypeError("You must provide at least one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).")
        elif sum((default, polynomial, quotient, dalgebraic)) > 1:
            raise TypeError("You can only provide one of the following arguments: coefficient_map, coefficients, (numerator and denominator), or (differential_equation and initial_conditions).")

        if default or dalgebraic: # we make sure ramification makes sense
            if ramification not in ZZ or ramification <= 0:
                raise ValueError(f"The ramification index must be a positive integer, got {ramification}.")
            ramification = ZZ(ramification)

        super().__init__(parent)

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
            self.__denominator = self if _one else self.parent().one()
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
            self.__type = self.TYPES.dalgebraic
            self.__numerator = self
            self.__denominator = self.parent().one()
            self.__map = self.__dalgebraic_coeff
            self.__polydict = dict()
            self.__dalgebraic = (differential_equation, initial_conditions, map, 0)

            ## We compute the order and ramification of the series
            self.__order = None
            self.__ramification = None
            self.order() # this will change the value of __order to the correct one
            self[differential_equation.order() + self.__order] # this will compute coefficients of the series at least until the given order
            if self.__dalgebraic[-1] != len(self.__dalgebraic[-2]):
                logger.error("Not all initial conditions have been used. This is an unexpected behavior. Please check the initial conditions provided.")

        ## We create a cache for computed elements
        self.__cache_computed: Mapping[Rational, Element] = dict()
    
    ###################################################################################
    ### Ramification handling
    ###################################################################################
    def ramification(self) -> int:
        r'''
            Return the ramification index of ``self``, i.e., the denominator common to every exponent in the series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: (R.gen()**QQ((1, 2))).ramification()
                2
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
            p, q = n.numerator(), n.denominator()
            if p*self.ramification() % q != 0: # this index is not in the ramification, hence, a zero is returned
                self.__cache_computed[n] = self.parent().base().zero() 
            elif n < self.order(): # this index is below the order, then we return zero
                self.__cache_computed[n] = self.parent().base().zero()
            else: # otherwise, we return the output of the map
                self.__cache_computed[n] = self.parent().base()(self.__map(n))

        return self.__cache_computed[n]

    def __dalgebraic_coeff(self, n: Rational) -> Element:
        r'''
            Internal method to extend first the coefficient map for differential algebraic formal Puiseux series, and then return an element.
        '''
        if not self.type() == self.TYPES.dalgebraic:
            raise TypeError(f"The method __dalgebraic_coeff is only defined for differential algebraic formal Puiseux series, got {self.type()}.")
        if len(self.__polydict) == 0 or max(self.__polydict) < n: # more coefficients are needed
            self.__dalgebraic_compute_until(n)

        return self.__polydict.get(n, self.parent().base().zero())

    def __dalgebraic_compute_until(self, n: Rational):
        r'''
            Internal method to compute the coefficients of a differential algebraic formal Puiseux series until a given order.
        '''
        if not self.type() == self.TYPES.dalgebraic:
            raise TypeError(f"The method __dalgebraic_compute_until is only defined for differential algebraic formal Puiseux series, got {self.type()}.")

        if len(self.__polydict) == 0: # no element has been computed yet
            raise ValueError(f"Requested element of the series without computing the order first. Please call the order() method first to compute the order of the series.")

        while len(self.__polydict) == 0 or max(self.__polydict) < n:
            ## Here we build the next coefficient of our series. 
            ## We get the truncated series with all computed elements
            t = self.parent().gens()[0]
            y_0 = sum(self.__polydict[k]*t**k for k in self.__polydict)
            p = max(self.__polydict) # desired order must be bigger than this

            ## We now take Y = y_0 + h, with ord(h) > p. Hence
            ## P(Y) = P(y_0) + L_{y_0}(h) + R(h) where the terms of R(h) are of higher order.
            ## Since we want Y to be a solution, then analyzing the lowest order term of 
            ## P(y_0) + L_{y_0}(h) we can find the next coefficient of h, which is the next coefficient of Y.
            equ, ics, map, count = self.__dalgebraic
            gen = equ.infinite_variables()[0] # we assume the differential equation is in one variable
            P_y = equ(**{gen.variable_name(): y_0}) # this will compute P(y_0)
            if P_y.is_zero() is True:
                self.__polydict[oo] = self.parent().base().zero() # nothing else to compute
                return
            
            ## We need to compute further
            from ..dpolynomial.dpolynomial import DifferentialPolynomialRing
            L = [equ.partial(gen[i])(**{gen.variable_name(): y_0}) for i in range(equ.order() + 1)] 
            # L has coefficients for a linear differential equation -> we would like to consider its indicial polynomial
            R = DifferentialPolynomialRing(L[0].parent(), gen.variable_name())
            gen_l = R.gens()[0]
            new_equ = P_y + sum(L[i]*gen_l[i] for i in range(len(L))) # this is the linear differential operator P_{y_0} + L_{y_0}(h)
            new_map = new_equ.parent().base().puiseux_morphism() # this is always trivial, since coefficients are already Puiseux series.
            ## The lowest order term can be obtained as usual
            order, coeff, used_condition = self.first_term_of_solution(new_equ, ics[count], new_map)
            if order <= p:
                raise ValueError(f"The next order {order} of the series is not big enough (>{p}). This is an unexpected behavior.")

            self.__ramification = lcm(self.__ramification, QQ(order).denominator())
            self.__polydict[order] = coeff
            count = count + 1 if used_condition else count
            self.__dalgebraic = (equ, ics, map, count)
        return

    @CheckBound
    def order(self, *, bound: int | None = None) -> int:
        r'''
            Return the lowest exponent `n` with `a_n \neq 0` (or ``bound`` if this cannot be resolved).

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = R.element_class(R, ramification=2, order=0,
                ....:     coefficient_map=lambda n: 7 if n == 2 else 0)
                sage: (f[QQ((1, 2))], f[2], f.order(bound=1), f.order(bound=3))
                (0, 7, 1, 2)
        '''
        if self.type() == self.TYPES.default:
            # Here we only know that all terms smaller than self.__order are zero.
            # We check the following terms until the bound
            for n in rat_range(self.__order, bound+1/self.ramification(), 1/self.ramification()):
                if self.__map(n) != self.parent().base().zero():
                    self.__order = n # we update the data for the order
                    return n
            return bound
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational):
            return self.__order # computed on initialization
        else: # dalgebraic
            if self.__order is None:
                # Computing the order for a differential algebraic formal Puiseux series using the Newton polygon
                equ, ics, map, count = self.__dalgebraic
                order, coeff, used_condition = self.first_term_of_solution(equ, ics[count], map)
                self.__order = order
                self.__ramification = QQ(order).denominator()
                self.__polydict[order] = coeff
                count = count + 1 if used_condition else count
                self.__dalgebraic = (equ, ics, map, count)
            else:
                return self.__order

    @staticmethod
    def first_term_of_solution(equ, ics, map) -> tuple[Rational, Element, bool]:
        r'''
            Return the first term of a solution of a differential algebraic equation given a condition.
        '''
        gen = equ.infinite_variables()[0] # we assume the differential equation is in one variable
        P, incl_charpoly = equ.newton_polygon(gen, map) # this computes the polygon plus candidates to orders
        used_condition = False

        if len(incl_charpoly) == 0:
            raise ValueError(f"The differential equation {equ} does not have a valid initial condition to compute the order of the series.")
        elif len(incl_charpoly) == 1: # only one option for the order, we check the characteristic polynomial for options on the initial condition
            order, charpoly = incl_charpoly

            if charpoly.degree() == 0: 
                raise ValueError(f"[IMPOSSIBLE] The characteristic polynomial {charpoly} for the order {order} is constant, hence, no valid condition can be found")
            elif charpoly.degree() == 1: # unique term, initial conditions are not consumed
                coeff = -charpoly[0]/charpoly[1]
            else: # we have to check the initial conditions
                if isinstance(ics, (list,tuple)): # the initial condition was given with (`d`, `c`)
                    if ics[0] != order:
                        raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found UNIQUE order {order} from the Newton polygon.\n\t- Requested order {ics[0]} from the initial condition.")
                    elif charpoly(ics[1]) != 0:
                        raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found UNIQUE order {order} from the Newton polygon.\n\t- Characteristic polynomial {charpoly} evaluated at {ics[1]} is not zero.\n\t- Try givin one of the roots: {charpoly.roots()}.")
                else: # the initial condition was given with just `c`
                    if charpoly(ics) != 0:
                        raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found UNIQUE order {order} from the Newton polygon.\n\t- Data given only by the coefficient.\n\t - Characteristic polynomial {charpoly} evaluated at {ics} is not zero.\n\t- Try givin one of the roots: {charpoly.roots()}.")
                    
                coeff = ics[1] if isinstance(ics, (list,tuple)) else ics
                used_condition = True # we have used one initial condition
        else: # options for orders are several -> we need to check if the information is correct
            incl_charpoly = dict(incl_charpoly) # we convert to a dictionary for easier access
            if not isinstance(ics, (list,tuple)):
                raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found MULTIPLE options for the order from the Newton polygon.\n\t- Initial condition must be given as a pair (order, coefficient).")
            elif ics[0] not in incl_charpoly:
                raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found MULTIPLE options for the order from the Newton polygon: {list(incl_charpoly.keys())}.\n\t- Initial condition given {ics} do not match a valid order in the list of options.")
            elif incl_charpoly[ics[0]](ics[1]) != 0:
                raise ValueError(f"Initial condition {ics} for {equ} is not compatible.\n\t- Found MULTIPLE options for the order from the Newton polygon: {list(incl_charpoly.keys())}.\n\t- The order given matches one of the possible orders.\n\t- Characteristic polynomial {incl_charpoly[ics[0]]} evaluated at {ics[1]} is not zero.\n\t- Try givin one of the roots: {incl_charpoly[ics[0]].roots()}.")
            else: # everything is correct, we set the order and the coefficient
                order = ics[0]
                coeff = ics[1]
                used_condition = True
        return order, coeff, used_condition

    def degree(self) -> int:
        r'''
            Return the highest exponent `n` with `a_n \neq 0` (only defined for finite series).

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R.element_class(R, coefficients={QQ((-1, 2)): 2, 1: 3}).degree()
                1
                sage: R.zero().degree()
                -Infinity
                sage: (1/(1 - R.gen())).degree()
                Traceback (most recent call last):
                ...
                TypeError: Degree is only defined for finite formal Puiseux series.
        '''
        if not self.type() == self.TYPES.polynomial:
            raise TypeError("Degree is only defined for finite formal Puiseux series.")
        return max(self.__polydict) if len(self.__polydict) > 0 else -oo

    def numerator(self) -> PuiseuxSeries_Element:
        r'''
            Return the numerator of a formal Puiseux series.

            It is defined generically, but we only return something different than ``self`` if 
            it is a rational Puiseux series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: q = x/(1 - x)
                sage: (q.numerator(), q.denominator()) == (x, 1 - x)
                True
                sage: (x + 1).numerator() == x + 1
                True
        '''
        if self.type() != self.TYPES.rational:
            return self
        return self.__numerator

    def denominator(self) -> PuiseuxSeries_Element:
        r'''
            Return the denominator of a formal Puiseux series.

            It is defined generically, but we only return something different than ``1`` if 
            it is a rational Puiseux series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: (x/(1 - x)).denominator() == 1 - x
                True
                sage: (x + 1).denominator().is_one()
                True
        '''
        if self.type() != self.TYPES.rational:
            return self.parent().one()
        return self.__denominator
    
    def gen_mult(self, n: Rational) -> PuiseuxSeries_Element:
        r'''
            Multiply ``self`` by the generator raised to the power ``n`` (i.e., shift all internal keys by ``n``).

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: p = 2*x**QQ((-1, 2)) + 3 + x
                sage: p.gen_mult(QQ((1, 2))) == 2 + 3*x**QQ((1, 2)) + x**QQ((3, 2))
                True
                sage: f = ~(1 - x)
                sage: f.gen_mult(2)[2:6]
                [1, 1, 1, 1]
                sage: (x/(1 - x)).gen_mult(1)[1:4]
                [0, 1, 1]
        '''
        n = QQ(n)
        if n == 0:
            return self
        elif self.type() == self.TYPES.polynomial:
            return self.parent().element_class(self.parent(),
                coefficients={k + n: c for k, c in self.__polydict.items()})
        elif self.type() == self.TYPES.rational:
            return self.parent().element_class(self.parent(),
                numerator=self.__numerator.gen_mult(n), denominator=self.__denominator)
        else: # default
            if self.type() == self.TYPES.dalgebraic:
                logger.warning(f"[dalgebraic] Multiplication by generator falls back into default type of series.")
            return self.parent().element_class(self.parent(),
                coefficient_map=lambda k: self[k - n], order=self.__order + n, 
                ramification=lcm(self.ramification(), n.denominator()))

    ###################################################################################
    ### Public property methods (working with the actual rational exponent)
    ###################################################################################
    @CheckBound
    def is_zero(self, *, bound: int | None = None) -> bool | int: #: Checker for the zero element
        r'''
            Checker for the zero element of the ring.

            This method checks whether the element is zero or not. If exact computation are possible, it returns ``True`` or ``False``.
            Otherwise it returns the last checked order for which the element is zero.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R.zero().is_zero()
                True
                sage: f = R.element_class(R, ramification=2, order=0,
                ....:     coefficient_map=lambda n: 7 if n == 2 else 0)
                sage: f.is_zero(bound=1)
                1
        '''
        if self.type() == self.TYPES.default:
            if any(
                self[k] != self.parent().base().zero() 
                for k in rat_range(self.order(bound=bound), bound+1/self.ramification(), 1/self.ramification())
            ):
                return False
            return bound
        elif self.type() in (self.TYPES.polynomial, self.TYPES.rational):
            return self.order() == oo
        else: # dalgebraic
            equ, ics, map, count = self.__dalgebraic
            gen = equ.infinite_variables()[0] # we assume the differential equation is in one variable
            if not equ(**{gen.variable_name(): 0}) == 0:
                return False
            
            P, incl_charpoly = equ.newton_polygon(equ.infinite_variables()[0], map)
            incl_charpoly = dict(incl_charpoly)
            M = max(incl_charpoly) # maximal order of a solution
            self[M+1] # guarantees we have computed until this term
            return any(el != 0 for el in self.__polydict.values())

    @CheckBound
    def is_one(self, *, bound: int | None = None) -> bool | int:
        r'''
            Checker for the identity element.

            See :func:`is_zero` for more information on the output of this type of methods.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: PuiseuxSeries(QQ, 'x').one().is_one()
                True
        '''
        if self.type() in (self.TYPES.default, self.TYPES.rational, self.TYPES.dalgebraic):
            return (self - self.parent().one()).is_zero(bound=bound)
        elif self.type() == self.TYPES.polynomial:
            return len(self.__polydict) == 1 and self[0] == self.parent().base().one()
        else:
            raise NotImplementedError("One-checking for differential algebraic formal Puiseux series is not yet implemented.")

    @CheckBound
    def is_unit(self, *, bound: int | None = None) -> bool:
        r'''
            Checker for whether the element is a unit or not.

            Puiseux series form a field, hence all non-zero elements are units.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: (2*R.gen()).is_unit(), R.zero().is_unit()
                (True, False)
        '''
        return (self.is_zero(bound=bound) is False)

    def type(self) -> PuiseuxSeries_Element.TYPES:
        r'''
            Method to get the type of formal power series.
        '''
        return self.__type

    def is_finite(self) -> bool: ## TODO (series) Check the use of the method `is_finite`
        r'''
            Method to check whether the formal power series is finitely represented or not.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: ((1 + x).is_finite(), (x/(1 - x)).is_finite(), (~(1 - x)).is_finite())
                (True, True, False)
        '''
        if self.type() == self.TYPES.polynomial:
            return True
        elif self.type() == self.TYPES.rational:
            return self.__numerator.is_finite() and self.__denominator.is_finite()
        else:
            return False

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
                sage: R.zero().is_monomial()
                False
                sage: (x/(2*x)).is_monomial()
                True
        '''
        if self.type() == self.TYPES.polynomial:
            return len(self.__polydict) == 1
        elif self.type() == self.TYPES.rational:
            return self.numerator().is_monomial(bound=bound) and self.denominator().is_monomial(bound=bound)
        elif self.type() == self.TYPES.dalgebraic:
            # we have computed several terms and oo is added if we found a finite solution
            return oo in self.__polydict and len(v for v in self.__polydict.values() if v != 0) == 1
        else:
            zero = self.is_zero(bound=bound+1)
            if zero == bound+1:
                return bound+1
            return (self - self.trailing_term()).is_zero(bound=bound)        

    def truncate(self, order: Rational | int) -> PuiseuxSeries_Element:
        r'''
            Return a :class:`PuiseuxSeries_Element` that contains only the coefficients with exponent at most ``order``.

            This method always returns a polynomial formal Puiseux series, even if the original one is not polynomial.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: p = R.element_class(R, coefficients={QQ((-1, 2)): 2, 0: 3, 1: 1})
                sage: p[QQ((-1, 2)):QQ((3, 2)):QQ((1, 2))]
                [2, 3, 0, 1]
                sage: p.truncate(0) == 2*x**QQ((-1, 2)) + 3
                True
                sage: (~(1 - x)).truncate(3) == 1 + x + x**2 + x**3
                True
        '''
        coeffs = {k: self[k] for k in rat_range(self.order(), QQ(order)+1/self.ramification(), 1/self.ramification())}
        return self.parent().element_class(self.parent(), coefficients=coeffs)

    def polynomial(self, ramification: int = 1) -> Element:
        r'''
            Converts (if possible) a Puiseux series into a polynomial. It requires three different conditions:
            * the requested `ramification` must be a multiple of the actual ramification,
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
                sage: P = R.poly_ring(ramification=2)
                sage: X = P.gen()
                sage: f.polynomial(2) == X**4 + 2*X**2 + 1
                True
                sage: (x**QQ((1, 2)) + 1).polynomial(2) == R.poly_ring(2).gen() + 1
                True
                sage: R.zero().polynomial() == R.poly_ring().zero()
                True
                sage: (x**-1).polynomial()
                Traceback (most recent call last):
                ...
                TypeError: The element is not a polynomial.
                sage: R.element_class(R, coefficients={-1: 1}).polynomial()
                Traceback (most recent call last):
                ...
                TypeError: The element is not a polynomial (it has negative order).
                sage: (~(1 - x)).polynomial()
                Traceback (most recent call last):
                ...
                TypeError: The element is not a polynomial.
                sage: (x**QQ((1, 2))).polynomial()
                Traceback (most recent call last):
                ...
                TypeError: The desired ramification does not divide the actual ramification.

            TODO (series): add examples that raises some error.
        '''
        return self.parent().poly_ring(ramification)(self) # the coercion system will take care of this

    def rational_function(self, ramification: int = 1) -> Element:
        r'''
            Converts (if possible) a Puiseux series into a rational function. It requires two different conditions:
            * the requested `ramification` must be a multiple of the actual ramification,
            * both numerator and denominator to be of finite type.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: f = ~x - 1 # (1/x) - 1 = (1 - x)/x
                sage: T = R.rat_field()
                sage: X = T.gen()
                sage: f.rational_function() == (1 - X)/X
                True
                sage: R.gen()/(2*R.gen()) == QQ((1, 2))
                True
                sage: R.zero().rational_function() == T.zero()
                True
                
            TODO (series): add examples that raises some error.
        '''
        return self.parent().rat_field(ramification)(self)

    def equation(self):
        r'''
            Gets the differential equation that defines the element. (Not always possible)

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries

            TODO (series): add examples
        '''
        if self.type() != self.TYPES.dalgebraic:
            return None # if not explcit, we return None
        else:
            return self.__dalgebraic[0] # we return the differential equation

    def equation_map(self):
        r'''
            Gets the map for the coefficients of the differential equation that defines the element. (Not always possible)

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries

            TODO (series): add examples
        '''
        if self.type() != self.TYPES.dalgebraic:
            return None # if not explcit, we return None
        else:
            return self.__dalgebraic[2] # we return the map of the differential equation
        
    @CheckBound
    def trailing_coefficient(self, *, bound: int | None = None) -> Element:
        r'''
            Method to get the trailing coefficient of a formal Puiseux series.

            The trailing coefficient is the coefficient of the monomial with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = R.element_class(R, ramification=2, order=0,
                ....:     coefficient_map=lambda n: 7 if n == 2 else 0)
                sage: f.trailing_coefficient(bound=1), f.trailing_coefficient(bound=3)
                (0, 7)
        '''
        order = self.order(bound=bound+1)
        if order == bound+1:
            return self.parent().base().zero()
        else:
            return self[order]

    @CheckBound
    def trailing_term(self, *, bound: int | None = None) -> PuiseuxSeries_Element:
        r'''
            Method to get the trailing term of a formal Puiseux series.

            The trailing term is the monomial with its coefficient with lowest degree. When we do not find any non-zero coefficient up to the given ``bound``, we return 0.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = R.element_class(R, ramification=2, order=0,
                ....:     coefficient_map=lambda n: 7 if n == 2 else 0)
                sage: f.trailing_term(bound=3) == 7*R.gen()**2
                True
        '''
        order = self.order(bound=bound+1)
        if order == bound+1:
            return self.parent().zero()
        else:
            return self.parent().element_class(self.parent(), coefficients={order: self[order]})

    @CheckBound
    def pseries_split(self, *, bound: int | None = None) -> tuple[Rational | int, PuiseuxSeries_Element]:
        r'''
            Splits the formal Puiseux series into the product of a power of the generator and a formal power series with non-zero constant term.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: p = 2*x**QQ((-1, 2)) + 3 + x
                sage: order, unit = p.pseries_split()
                sage: order, unit[0]
                (-1/2, 2)
                sage: q = x/(1 - x)
                sage: order, unit = q.pseries_split()
                sage: order, unit[0:4]
                (1, [1, 1, 1, 1])
                sage: order, unit = (~(1 - x)).pseries_split()
                sage: (order, unit[0])
                (0, 1)

            This is a method that may not be exact, hence, if we can not compute fully the power of the generator, we return the last computed order.
        '''
        order = self.order(bound=bound)
        return (order, self.gen_mult(-order))

    def __getitem__(self, key: Rational | int) -> Element:
        r'''
            Return the coefficient of an exponent or a finite list of coefficients.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = R.element_class(R, coefficients={QQ((-1, 2)): 2, 0: 3, 1: 1})
                sage: f[QQ((-1, 2)):QQ((3, 2)):QQ((1, 2))]
                [2, 3, 0, 1]
        '''
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

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: r = x**QQ((1, 2))
                sage: r + x == x + r
                True
                sage: (r + x).ramification()
                2
                sage: ((r + x) + (~(1 - x)))[0:4] == ((~(1 - x)) + (r + x))[0:4]
                True
        '''
        ## Checking for trivial cases
        if self.is_zero() is True:
            return other
        elif other.is_zero() is True:
            return self

        E = lcm(self.ramification(), other.ramification())

        if any(el.type() in (self.TYPES.default, self.TYPES.dalgebraic) for el in (self, other)):
            if any(el.type() == self.TYPES.dalgebraic for el in (self, other)):
                logger.warning(f"[dalgebraic] Addition of differential algebraic formal Puiseux series falls back into default type of series.")
                # TODO (series): implement addition of dalgebraic series using differential elimination.
            # at least one is default -> we change to default
            add_map = lambda k : self[k] + other[k]
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

    def __neg__(self) -> PuiseuxSeries_Element:
        r'''
            Return the additive inverse of this series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: -((1 + x)/(1 - x)) == (-1 - x)/(1 - x)
                True
                sage: (-~(1 - x))[0:4]
                [-1, -1, -1, -1]
        '''
        if self.is_zero() is True:
            return self
        if self.type() == self.TYPES.polynomial:
            coeffs = {k: -c for k, c in self.__polydict.items()}
            return self.parent().element_class(self.parent(), coefficients=coeffs)
        elif self.type() == self.TYPES.rational:
            return self.parent().element_class(self.parent(), numerator=-self.__numerator, denominator=self.__denominator)
        elif self.type() == self.TYPES.dalgebraic:
            equ, ics, map, count = self.__dalgebraic
            gen = equ.infinite_variables()[0] # we assume the differential equation is in one variable
            new_equ = equ(**{gen.variable_name(): -gen[0]}) # we negate the variable in the differential equation
            new_ics = tuple(-ic if not isinstance(ic, (list,tuple)) else (ic[0], -ic[1]) for ic in ics) # we negate the initial conditions

            return self.parent().algebraic_element(new_equ, *new_ics, map=map)
        else:
            return self.parent().element_class(self.parent(), coefficient_map=lambda k : -self[k], order=self.__order, ramification=self.ramification())

    def _sub_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._sub_` for further information.

            ::NO EXAMPLE::
        '''
        return self + (-other)

    def _mul_(self, other: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Element._mul` for further information.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: r = x**QQ((1, 2))
                sage: (r + x)*(r - x) == x - x**2
                True
                sage: 2*(r + x) == 2*r + 2*x
                True
                sage: f = ~(1 - x)
                sage: (f*f)[0:5]
                [1, 2, 3, 4, 5]
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
                return self.parent().element_class(self.parent(), coefficients={k: scalar * c for k, c in other.__polydict.items()})
            elif other.type() == self.TYPES.rational:
                return self.parent().element_class(self.parent(), numerator=scalar * other.__numerator, denominator=other.__denominator)
            elif other.type() == self.TYPES.dalgebraic:
                equ, ics, map, count = other.__dalgebraic
                gen = equ.infinite_variables()[0] # we assume the differential equation is in one variable
                new_equ = equ(**{gen.variable_name(): gen[0]/scalar}) #
                new_ics = tuple(scalar*ic if not isinstance(ic, (list,tuple)) else (ic[0], scalar*ic[1]) for ic in ics) # we scale the initial conditions
                raise NotImplementedError("Multiplication of differential algebraic formal Puiseux series is not yet implemented.")
            else: # default
                return self.parent().element_class(self.parent(), coefficient_map=lambda k: scalar * other[k], order=other.order(), ramification=other.ramification())
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

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: q = x/(1 - x)
                sage: q.type() == q.TYPES.rational
                True
                sage: q.numerator().is_finite() and q.denominator().is_finite()
                True
                sage: q.rational_function() == R.rat_field().gen()/(1 - R.rat_field().gen())
                True
                sage: x/(2*x) == QQ((1, 2))
                True
                sage: x/R.zero()
                Traceback (most recent call last):
                ...
                ZeroDivisionError: Division by zero element is not allowed.
                sage: R.zero()/R.zero()
                Traceback (most recent call last):
                ...
                ZeroDivisionError: Division by zero element is not allowed.
        '''
        ## Division is done via the `rational` type of series
        if other.is_zero() is True:
            raise ZeroDivisionError(f"Division by zero element is not allowed.")
        elif self.is_zero() is True:
            return self.parent().zero()
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

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: inverse = ~(1 - R.gen())
                sage: inverse[0:5]
                [1, 1, 1, 1, 1]
                sage: ~R.zero()
                Traceback (most recent call last):
                ...
                ZeroDivisionError: Inverse of zero element do not exist.
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
        r'''
            Raise a Puiseux series to an integer or rational power.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: root = (1 - x)**QQ((1, 3))
                sage: root[0], root[1]
                (1, -1/3)
                sage: (root**3)[0:4]
                [1, -1, 0, 0]
                sage: ((1 - x)**QQ((2, 3)))[0:3]
                [1, -2/3, -1/9]
                sage: (x**QQ((1, 2)))**2 == x
                True
        '''
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

                if self.is_monomial() is True: # the only case where exact computation can be performed
                    o = self.order()
                    c = self[o]
                    return self.parent().element_class(self.parent(), coefficients={o/m: c**(1/m)})

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

    @CheckBound
    def __eq__(self, other, *, bound: int | None = None) -> bool:
        r'''
            Compare series, returning a precision bound when equality is unresolved.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: (1 + x) == (x + 1)
                True
                sage: f = ~(1 - x)
                sage: f.__eq__(1 + x, bound=1)
                1
                sage: f == 1 + x
                False
        '''
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
        r'''
            Compare series for inequality, preserving unresolved precision bounds.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: (1 + x) != (x + 1)
                False
                sage: (~(1 - x)).__ne__(1 + x, bound=1)
                1
        '''
        equals = self.__eq__(other, bound=bound)
        if equals is True:
            return False
        elif equals is False:
            return True
        return equals

    def __hash__(self) -> int:
        r'''
            Return a hash based on the bounded series representation.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = R.element_class(R, coefficients={0: 2, 1: 3})
                sage: hash(f) == hash(f)
                True
        '''
        return hash(self.__repr__(bound=100))

    def __call__(self, **kwds) -> Element:
        r'''
            Evaluate the coefficients of the series.

            Calling without substitutions leaves each representation unchanged.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: p = 1 + x
                sage: p() is p
                True
                sage: q = x/(1 - x)
                sage: q() is q
                True
                sage: f = ~(1 - x)
                sage: f() is f
                True
        '''
        if not kwds:
            return self
        if self.type() == self.TYPES.polynomial:
            new_poly = {k: el(**kwds) for (k,el) in self.__polydict.items()}
            return self.parent().element_class(self.parent(), coefficients=new_poly)
        elif self.type() == self.TYPES.rational:
            new_num = self.__numerator(**kwds)
            new_den = self.__denominator(**kwds)
            return self.parent().element_class(self.parent(), numerator=new_num, denominator=new_den)
        elif self.type() == self.TYPES.dalgebraic:
            equ, ics, map, count = self.__dalgebraic
            new_equ = equ(**kwds) # inner evaluation of the equation
            new_ics = tuple(ic(**kwds) if not isinstance(ic, (list,tuple)) else (ic[0], ic[1](**kwds)) for ic in ics) # inner evaluation of the initial conditions
            return self.parent().algebraic_element(new_equ, *new_ics, map=map)
        elif self.type() == self.TYPES.default:
            new_func = lambda n : self[n](**kwds)
            return self.parent().element_class(self.parent(), coefficient_map=new_func, order=self.order(), ramification=self.ramification())
        else:
            raise ValueError("Impossible type for a Puiseux series")

    def reduce_rational(self) -> None:
        r'''
            Method that reduces as much as possible a quotient of Puiseux series.    

            This method tries to reduce the numerator and denominator of a rational Puiseux series. Depending
            on the type of its numerator and denominator, it will perform different actions:
            * If both are finite, it will compute the rational expression and reduce it to its simplest form.
              This is based on SageMath reduction of rational functions.
            * If at least one of them is not finite, it will return a "normalized" version where the denominator
              has order 0.

            IMPORTANT:
              1. This method can only access the parent, type and current values of numerator and denominator.
            Then, it can only change the attributes ``__numerator`` and ``__denominator`` of the object.
              2. This method does not return anything, it modifies the object in place.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                                sage: p = 1 + x
                                sage: p.reduce_rational()
                                sage: p.type() == p.TYPES.polynomial
                                True

                        Common factors cancel for polynomial components:

                sage: q = R.element_class(R, numerator=x - x**2, denominator=1 - x)
                sage: q.reduce_rational()
                sage: q.rational_function() == R.rat_field().gen()
                True

            Rational numerator and denominator components are reduced as well:

                sage: n = x/(1 - x)
                sage: d = x/(1 + x)
                sage: q = R.element_class(R, numerator=n, denominator=d)
                sage: q.reduce_rational()
                sage: X = R.rat_field().gen()
                sage: q.rational_function() == (1 + X)/(1 - X)
                True

            A zero numerator is normalized to ``0/1``:

                sage: q = R.element_class(R, numerator=R.zero(), denominator=1 + x)
                sage: q.reduce_rational()
                sage: q.numerator().is_zero(), q.denominator().is_one()
                (True, True)

            For default series components, the denominator's leading power is moved into the numerator:

                sage: n = R.element_class(R, ramification=1, order=0,
                ....:     coefficient_map=lambda e: 1 if e == 0 else 0)
                sage: d = R.element_class(R, ramification=1, order=2,
                ....:     coefficient_map=lambda e: 3 if e == 2 else 0)
                sage: q = R.element_class(R, numerator=n, denominator=d)
                sage: q.reduce_rational()
                sage: q.numerator().order(), q.denominator().order()
                (-2, 0)
                sage: q.numerator()[-2], q.denominator()[0]
                (1, 3)
        '''
        if self.type() != self.TYPES.rational:
            return # nothing to be done without a denominator
        else:
            n, d = self.__numerator, self.__denominator

            if n.is_zero() is True:
                self.__numerator = n.parent().zero()
                self.__denominator = d.parent().one()
                return
            
            ## We try the case where both are finite represented
            try:
                ramification = lcm(n.ramification(), d.ramification())
                n = n.rational_function(ramification)
                d = d.rational_function(ramification)
                quot = n / d # this should simplify the rational expression
                self.__numerator = self.parent()(quot.numerator())
                self.__denominator = self.parent()(quot.denominator())
                return
            except TypeError: # one of the is not finite
                ## We simplify the power of the generator
                n_order, n_series = n.pseries_split()
                d_order, d_series = d.pseries_split()

                self.__numerator = n_series.gen_mult(n_order - d_order)
                self.__denominator = d_series
                return

    ###################################################################################
    @CheckBound
    def __repr__(self, *, bound: int | None = None) -> str:
        r'''
            Return the series representation through ``bound``.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = ~(1 - R.gen())
                sage: 'O(x^(4))' in f.__repr__(bound=3)
                True
        '''
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()
        e = self.ramification()

        def variable_repr(exponent: Rational) -> str:
            if exponent == 0:
                return "1"
            elif exponent == 1:
                return f"{g}"
            else:
                return f"{g}^({exponent})"

        def term_str(exponent: Rational, element:Element, first:bool=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""

            op_str = variable_repr(exponent)
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
            order = self.order()
            return term_str(order, self[order],True) + "".join(
                term_str(k, self[k])
                for k in sorted(self.__polydict.keys())[1:]
                if self[k] != 0
            )
        else:
            order = self.order(bound=bound+1)

            if order == bound+1/e:
                return f"O({variable_repr(bound+1/e)})"

            return term_str(order, self[order], True) + "".join(
                term_str(k, self[k])
                for k in rat_range(order+1/e, bound+1/e, 1/e)
                if self[k] != 0
            ) + (f" + O({variable_repr(bound+1)})")

    @CheckBound
    def _latex_(self, *, bound: int | None = None) -> str:
        r'''
            Computes a LaTeX string to represent the formal Puiseux series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = 1 + R.gen()**QQ((1, 2))
                sage: f._latex_() != ''
                True
                sage: r'\text{O}' in (~(1 - R.gen()))._latex_(bound=3)
                True
        '''
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()
        e = self.ramification()

        def variable_str(exponent: Rational):
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
                output = (" + " if not first else "") + variable_str(n)
            elif element == -1:
                output = (" - " if not first else "") + variable_str(n)
            else: # element is something != 1
                op_str = variable_str(n)
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
            order = self.order()
            return term_str(order, self[order],True) + "".join(
                term_str(k, self[k])
                for k in sorted(self.__polydict.keys())[1:]
                if self[k] != 0
            )
        else:
            ## We print at least 3 terms up to order -bound
            order = self.order(bound=bound+1)
            if order == bound+1:
                return f"\\text{{O}}({variable_str(bound+1)})"

            return term_str(order, self[order], True) + "".join(
                term_str(k, self[k])
                for k in range(order+1, bound+1)
                if self[k] != 0
            ) + (f" + \\text{{O}}({variable_str(bound+1)})")

    def to_sage(self) -> PuiseuxSeriesElement:
        r'''
            Convert this element to Sage's Puiseux series representation.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = 1 + R.gen()**QQ((1, 2))
                sage: sage_f = f.to_sage()
                sage: sage_f[0], sage_f[QQ((1, 2))]
                (1, 1)
                sage: R(sage_f) == f
                True
                sage: R.zero().to_sage() == R.to_sage().zero()
                True
                sage: f = ~(1 - R.gen())
                sage: sage_f = f.to_sage()
                sage: (sage_f.prec(), sage_f[0], sage_f[1])
                (21, 1, 1)
                sage: R(R.to_sage()(1).add_bigoh(3))
                Traceback (most recent call last):
                ...
                ValueError: A finite-precision Sage Puiseux series cannot be reconstructed exactly.
        '''
        return self.parent().to_sage()(self)

class PuiseuxSeries_Ring(Parent):
    r'''
        Class for a field of Puiseux series over a :class:`~dalgebra.dring.DRing`.

        Given a field `F`, this ring represents the union `\bigcup_{e > 0} F((x^{1/e}))` of Laurent series fields
        in fractional powers of a new variable `x`. Elements carry their own ramification index; the derivation of
        `F` is extended naturally to `x` via the chain rule `d(x^{n/e}) = (n/e) x^{(n-e)/e}`.

        INPUT:

        * ``base``: a field with one derivative.
        * ``name``: name that the variable `x` will have.

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import PuiseuxSeries, PuiseuxSeries_Ring
            sage: R = PuiseuxSeries(QQ, 'x')
            sage: PuiseuxSeries(QQ, 'x') is R
            True
            sage: (R.gen(), R.gens(), R.ngens(), R.gen_name(), R.variable_name(), R.variable_name(3))
            (x, (x,), 1, 'x', 'x', 'x_3')
            sage: (R.zero().is_zero(), R.one().is_one(), R.is_field(), R.is_integral_domain())
            (True, True, True, True)
            sage: (R.fraction_field() is R, R.constant_ring() is R.base(), R.operator_types(), R.noperators())
            (True, True, ('derivation',), 1)
            sage: R.gen().derivative() == 1
            True
            sage: (R.gen()**QQ((3, 2))).derivative() == QQ((3, 2))*R.gen()**QQ((1, 2))
            True
            sage: functor, base = R.construction()
            sage: base is R.base() and functor(base) is R
            True
            sage: R.change_base(QQ) is R
            True
            sage: f = R.random_element(-2, 3, ramification=2, density=1)
            sage: f.is_finite() and all(QQ(-1) <= k <= QQ((3, 2)) for k in f._PuiseuxSeries_Element__polydict)
            True
            sage: PuiseuxSeries_Ring(ZZ, 'x')
            Traceback (most recent call last):
            ...
            TypeError: The base must be a ring with operators

        TODO (puiseux): (1) add possibility to create a Puiseux series ring with a non-trivial constant ring (i.e. a differential field with non-trivial constants)
        TODO (puiseux): (2) add possibility to create a Puiseux series ring with a non-trivial derivation (i.e. the generator is not derived to 1).
        TODO (puiseux): (3) add possibility to create multivariate Puiseux series rings (i.e. several generators with several derivations)
    '''
    Element = PuiseuxSeries_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        r'''
            Method to generate the appropriate list of categories for ``self``

            ::NO EXAMPLE::
        '''
        return [_DRings, CommutativeAlgebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        ## TODO (puiseux): (2) we need more arguments for defining the derivative of the generator
        ## TODO (puiseux): (3) we need to change name for names in order to have multivariate Puiseux series rings
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif isinstance(base, PuiseuxSeries_Ring):
            raise TypeError("The base must not be a formal Puiseux series ring")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")
        elif base.constant_ring() != base:
            ## TODO (puiseux): (1) we need to allow non-trivial constant rings, but this is not yet implemented
            raise TypeError("The base must be a differential ring with trivial constants")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.__operators = [self.__build_derivation()] ## TODO (puiseux): (2)
        self.__gen = self.element_class(self, coefficients={1: self.base().one()})
        self.__poly_rings = dict()
        self.poly_ring(ramification=1) # we create the basic (ramification 1) polynomial ring

        ## Setting up basic conversions
        ## Puiseux series ring -> Base ring of coefficients (constants) (this is a conversion)
        try:
            self.base().register_conversion(PSConvertToBase(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.to_sage().register_coercion(PSCoerceToSage(self))
            self.register_conversion(PSConvertFromSage(self))
        except AssertionError: # This coercion/conversion was already registered
            pass

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        r'''
            Return the string for representing the generator of the field of Puiseux series.
            TODO (puiseux): (3)
        '''
        return self.__gens[0]

    def variable_name(self, ramification: int = None) -> str:
        r'''
            Return the string for representing the name of the variable of the field of Puiseux series. 

            It has the optional case that it will return the name for the ramification variable (for finite Puiseux series)
            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R.variable_name(), R.variable_name(3)
                ('x', 'x_3')
                sage: R.variable_name(0)
                Traceback (most recent call last):
                ...
                ValueError: Ramification 0 must be a positive integer.
        '''
        output = self.gen_name()
        if ramification is not None:
            if ramification not in ZZ or ramification <= 0:
                raise ValueError(f"Ramification {ramification} must be a positive integer.")
            return f"{output}_{ramification}"
        return output

    def gen(self, index: int = 0) -> PuiseuxSeries_Element:
        r'''
            Return the generator of the field of Puiseux series.
            TODO (puiseux): (3)
        '''
        return self.gens()[index]

    def gens(self) -> tuple[PuiseuxSeries_Element]:
        r'''
            Return the generators of the field of Puiseux series.
            TODO (puiseux): (3)
        '''
        return (self.__gen,)

    def ngens(self) -> int:
        r'''
            Return the number of generators of the field of Puiseux series.
            TODO (puiseux): (3)
        '''
        return 1

    def one(self) -> PuiseuxSeries_Element:
        r'''
            Return the identity element of the field of Puiseux series.
        '''
        return self.element_class(self, coefficients={0:self.base().one()}, _one=True)

    def zero(self) -> PuiseuxSeries_Element:
        r'''
            Return the zero element of the field of Puiseux series.
        '''
        return self.element_class(self, coefficients=dict())

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

    def poly_ring(self, ramification: int = 1) -> Parent:
        r'''
            Return the polynomial ring associated to this field of formal Puiseux series with the specified ramification.
            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: P = R.poly_ring(2)
                sage: P.gen().variable_name()
                'x_2'
                sage: R(P.gen() + 1) == x**QQ((1, 2)) + 1
                True
                sage: P(x**QQ((1, 2)) + 1) == P.gen() + 1
                True
        '''
        if ramification not in self.__poly_rings:
            self.__poly_rings[ramification] = PolynomialRing(self.base().to_sage(), self.variable_name(ramification = None if ramification == 1 else ramification))

            ## we add coercion and conversion for this ring and its field of fractions
            ## poly ring -> Puiseux series ring (this is a coercion)
            try:
                self.register_coercion(PSCoerceFromPoly(self.__poly_rings[ramification], self, ramification=ramification))
            except AssertionError: # This coercion was already registered
                pass
            ## Puiseux series ring -> poly ring (this is a conversion)
            try:
                self.__poly_rings[ramification].register_conversion(PSConvertToPoly(self, self.__poly_rings[ramification], ramification=ramification))
                self.__poly_rings[ramification].fraction_field().register_conversion(PSConvertToRational(self, ramification=ramification))
            except AssertionError: # This conversion was already registered
                pass

        return self.__poly_rings[ramification]

    def rat_field(self, ramification: int = 1) -> Parent:
        r'''
            Return the field of rational functions associated to this field of formal Puiseux series with the specified ramification.
            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: x = R.gen()
                sage: T = R.rat_field(2)
                sage: T(x**QQ((1, 2)) + 1) == T.gen() + 1
                True
                sage: R.rat_field() is R.poly_ring().fraction_field()
                True
        '''
        return self.poly_ring(ramification=ramification).fraction_field()

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        r'''
            See :func:`Parent._coerce_map_from_base_ring` for further information.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R(7)[0]
                7
                sage: R.base()(R(7)) == 7
                True
        '''
        return PSCoerceFromBase(self)

    def construction(self) -> tuple[PuiseuxSeriesFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: functor, base = R.construction()
                sage: base is R.base() and functor(base) is R
                True
        '''
        return PuiseuxSeriesFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        r'''
            See :func:`Parent.fraction_field` for further information.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R.fraction_field() is R
                True
        '''
        return self

    def change_base(self, R: Parent) -> PuiseuxSeries_Ring:
        r'''
            Method to change the base field for considering the series.

            This method takes into consideration the coercions between the old and the new base to create the appropriate coercion maps between the old and new Puiseux series rings.

            EXAMPLES::

                sage: from sage.all import PolynomialRing
                sage: from dalgebra.dring import DifferentialRing
                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: K = PolynomialRing(QQ, 't').fraction_field()
                sage: Kd = DifferentialRing(K, lambda f: 0)
                sage: S = R.change_base(Kd)
                sage: p = R.element_class(R, coefficients={0: 2, 1: 1})
                sage: q = R.gen()/(1 - R.gen())
                sage: f = ~(1 - R.gen())
                sage: S(p)[0], S(q)[0:3], S(f)[0:3]
                (2, [0, 1, 1], [1, 1, 1])
        '''
        new_ring = PuiseuxSeries(R, self.gen_name())
        if new_ring is self:
            return self
        ## Creating the coercion map if possible
        try:
            M = PSCoerceBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    def to_sage(self) -> PuiseuxSeriesRing:
        r'''
            Return the corresponding Sage ring for this field of Puiseux series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: R.to_sage().base_ring() is QQ
                True
        '''
        return PuiseuxSeriesRing(self.base().to_sage(), self.gen_name())
    
    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Formal Puiseux Series Ring in {self.__gens[0]} over {self.base()}"

    def _latex_(self):
        r'''
            Computes a LaTeX representation for this field of Puiseux series.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: 'x' in R._latex_()
                True
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
        from random import random
        density = kwds.get("density", 0.5)
        return self.element_class(self, ramification=ramification,
            coefficients={k: self.base().random_element(*args, **kwds) 
                          for k in range(lower_bound, up_bound+1) if random() < density
                          }
        )

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

    def constant_ring(self, operation: int = 0) -> Parent:
        r'''
            See :func:`DRings.ParentMethods.constant_ring` for further information.

            ::NO EXAMPLE::
        '''
        return self.base().constant_ring(operation)

    def add_constants(self, *new_constants: str) -> PuiseuxSeries_Ring:
        r'''
            See :func:`DRings.ParentMethods.add_constants` for further information.

            ::NO EXAMPLE::
        '''
        ## TODO (puiseux): detected error in this method.
        return self.change_base(self.base().add_constants(*new_constants)) # this guarantees coercion

    def linear_operator_ring(self):
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: PuiseuxSeries(QQ, 'x').linear_operator_ring()
                Traceback (most recent call last):
                ...
                NotImplementedError: Linear operator ring over Formal Puiseux Series not yet implemented
        '''
        raise NotImplementedError("Linear operator ring over Formal Puiseux Series not yet implemented")

    def inverse_operation(self, element: PuiseuxSeries_Element, _: int = 0) -> PuiseuxSeries_Element:
        r'''
            See :func:`DRings.ParentMethods.inverse_operation` for further information.

            EXAMPLES::

                sage: from dalgebra.dextension.puiseux import PuiseuxSeries
                sage: R = PuiseuxSeries(QQ, 'x')
                sage: f = 4*R.gen()**QQ((1, 2))
                sage: f.integrate().derivative() == f
                True
                sage: x = R.gen()
                sage: p = 3*x**QQ((3, 2)) + 2*x**QQ((-1, 2))
                sage: p.derivative() == QQ((9, 2))*x**QQ((1, 2)) - x**QQ((-3, 2))
                True
                sage: q = x/(1 - x)
                sage: q.derivative().rational_function() == 1/(1 - R.rat_field().gen())**2
                True
                sage: from dalgebra.dring import IntegrationError
                sage: (x**-1).integrate()
                Traceback (most recent call last):
                ...
                IntegrationError: Puiseux series with a term in x^-1 can not be integrated.

            TODO (puiseux): (2), (3)
        '''
        ## Coefficients are all constants, hence integrating is simply shifting coefficients by rational numbers and 
        ## adding 1 to exponents. Only difficult case: if the order -1 is in the series.
        if element.is_zero() is True:
            return self.zero()
        elif element.type() == element.TYPES.polynomial:
            if -1 in element._PuiseuxSeries_Element__polydict:
                raise IntegrationError(f"Puiseux series with a term in x^{-1} can not be integrated.")
            out_dict = {k + 1: element[k] / QQ(k + 1) for k in element._PuiseuxSeries_Element__polydict}
            
            return self.element_class(self, coefficients=out_dict)
        elif element.type() == element.TYPES.dalgebraic:
            equ, ics, map, _ = element._PuiseuxSeries_Element__dalgebraic
            gen = equ.infinite_variables()[0] # we assume the equation comes with only one d-variable
            new_equ = equ(**{gen.variable_name(): gen[1]})
            ics = tuple(ic if not isinstance(ic, (list,tuple)) else (ic[0]+1, ic[1]) for ic in ics)
            return self.algebraic_element(new_equ, *ics, map=map)
        else: # other cases: we create a default series by defining its elements
            if element[-1] != 0:
                raise IntegrationError(f"Puiseux series with a term in x^{-1} can not be integrated.")
            out_map = lambda k: element[k-1] / QQ(k) if k != 0 else self.base().zero()
            return self.element_class(self, coefficient_map=out_map, order=element.order()+1, ramification=element.ramification())

    def algebraic_element(self, equation: Element, *conditions: tuple[Rational, Element], map: PSCoerceFromDRing = None) -> PuiseuxSeries_Element:
        r'''
            Method to compute a d-algebraic element in ``self``.

            This method computes a Puiseux series solution to a differential polynomial equation with some initial conditions.
            This method follows an integral approach, meaning that it will report a detailed error if the conditions are not 
            properly given, with suggestions for the user.

            The idea behind this is the following: given a differential polynomial `P(y) = 0`, of order `d` that is linear 
            in its highest order term, we can write it as `y^{(d)} = f(x, y, y', ..., y^{(d-1)})`, for a rational function `f`.
            This allows naturally to compute the coefficients of the Puiseux series solutions recursively, since the element
            `n/e+d` can be written in terms of the previous terms. Hence, knowing the initial conditions up to order `d-1` is 
            enough to compute as many coefficients as we want.

            The main difficulty here is to check whether the equation has solutions with lower orders and how to check which 
            conditions are forced, which are flexible and which are impossible. To work with this, we divide this method in two
            steps:

            1. Compute with the Newton Polygon plus the Fréchet derivative of the equation the coefficients until order `d-1`.
            2. Compute recursively the coefficients of the solution using the recursive formula given by the equation.

            It is only in step 1 where we need the initial conditions. Initial conditions has the following format: `(d, c)` where
            `d` is a rational number and `c` is an element of the base field. When we check the possible orders of a solution, we may get 
            several candidates as the slopes of the faces of the Newton polygon. Then, its characteristic polynomial provides an algebraic
            equation for the actual element to be in that order.

            Hence, the initial condition `(d,c)` will be picked among the different options. We have the following cases:
            * If there is no choice for the order (i.e., it must be of a fixed order) we allow `d` to be not given (i.e., the input is 
              `c` instead of `(d,c)`). But if it is actually given and a choice in the initial condition is available, we will check the value is correct.
            * Once we are done with the order, we will compute the characteristic polynomial. If the polynomial has 1 valid option, we assume 
              only one initial condition works, hence we simply compute it a move forward.
            * Another option is that the polynomial has degree greater than 1, i.e., several options are possible. Here we check the condition 
              is valid (i.e., satisfies the algebraic condition).
            * Otherwise, the polynomial is zero and the initial condition is fully free. In this case, the value of `c` will determine which 
              coefficient we set for the given order.
            It is in this process where the integral approach of the algorithm raises: if we detect an error here, we indicate what went wrong,
            and we will provide the user the possibility of fixing the input by suggesting a change in the input ``conditions``.
        '''
        ## We check the input of the equation
        from ..dpolynomial.dpolynomial import DPolynomial
        if not isinstance(equation, DPolynomial):
            raise TypeError("The equation must be a differential polynomial over the base ring.")
        elif len(equation.infinite_variables()) > 0:
            raise TypeError("The equation must be a differential polynomial over the base ring, not over the Puiseux series ring.")
        elif equation.parent().noperators() != 1:
            raise TypeError("The equation must be a differential polynomial over the base ring with one operator.")
        elif not equation.parent().is_differential():
            raise TypeError("The equation must be a differential polynomial over the base ring with one operator.")
        elif not self.has_coerce_map_from(equation.parent().puiseux_field()):
            raise TypeError("The equation must be a differential polynomial over the base ring of the Puiseux series ring.")

        u = equation.infinite_variables()[0] # generator of the equation
        d = equation.order(u) # order of the equation
        if equation.degree(u[d]) != 1:
            raise ValueError("The equation must be linear in its highest order term.")

        ## We ensure the map is valid for the coefficients
        if map is None:
            map = equation.parent().base().puiseux_morphism()
        if not isinstance(map, PSCoerceFromDRing) or map.codomain() != equation.parent().puiseux_field():
            raise TypeError("The map must be a coercion from the base ring of the equation to the Puiseux series ring.")

        ## The map is correct fr the coefficients. Now we ensure the codomain is ``self``
        if map.codomain() != self:
            map_self = self.coerce_map_from(map.codomain())*map
        else:
            map_self = map

        return self.element_class(self, differential_equation=equation, initial_conditions=conditions, map=map_self)

    def __build_derivation(self) -> DerivationMap:
        r'''
            Internal method to build the derivation of the field of Puiseux series.

            The chain rule gives `d(x^{n/e}) = (n/e) x^{(n-e)/e}` for a term with (internal) numerator `n` at
            ramification `e`.

            ::NO EXAMPLE::

            TODO (puiseux): (2), (3)
        '''
        def derivation_map(element: PuiseuxSeries_Element) -> PuiseuxSeries_Element:
            if element.is_zero() is True:
                return self.zero()
            e = element.ramification()
            if element.type() == element.TYPES.polynomial:
                out_dict = {k-1 : k*element[k] for k in element._PuiseuxSeries_Element__polydict}
                return self.element_class(self, coefficients=out_dict)
            elif element.type() == element.TYPES.rational:
                n, d = element.numerator(), element.denominator()
                nn = n.derivative()*d - n*d.derivative()
                dd = d*d
                return self.element_class(self, numerator=nn, denominator=dd, _reduce=True)
            elif element.type() == element.TYPES.dalgebraic:
                equ, ics, map, _ = element._PuiseuxSeries_Element__dalgebraic
                gen = equ.infinite_variables()[0] # we assume the equation comes with only one d-variable
                equ_d = equ.derivative()

                # We eliminate gen[0] from equ and equ_d
                E1, E2, v = equ.parent().as_polynomials(equ, equ_d, gen[0])
                new_E = E1.resultant(E2, v)
                new_equ = equ.parent()(new_E)
                monomials = new_equ.monomials()
                coefficients = new_equ.coefficients()

                new_mons = list()
                for mon in monomials:
                    new_mons.append(equ.parent()(mon.parent().element_class(mon.parent(), {(v, tuple(el-1 for el in o)): e for (v, o), e in mon._variables.items()})))

                new_equ = sum(c*mon for c, mon in zip(coefficients, new_mons))
                new_ics = tuple(ic if not isinstance(ic, (list,tuple)) else (ic[0]-1, ic[1]) for ic in ics)
                return self.algebraic_element(new_equ, *new_ics, map=map)
            else:
                return self.element_class(self,
                    coefficient_map=lambda k: (k+1)*element[k+1] + element[k].derivative(),
                    order=element.order()-1, ramification=e)

        return DerivationMap(self, derivation_map, check=False)


class PuiseuxSeriesFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`PuiseuxSeries_Ring`.

        This class represents the functor `F: R \mapsto \bigcup_{e>0} R((x^{1/e}))`.
        The name of the variable must be given to the functor and, then
        this can take any differential field ring and create the corresponding field of Puiseux
        series.

        INPUT:

        * ``name``: name of the variable that the functor will add

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import PuiseuxSeries
            sage: f, base = PuiseuxSeries(QQ, 'x').construction()
            sage: repr(f)
            'PuiseuxSeries(*,x)'
            sage: f == PuiseuxSeries(QQ, 'x').construction()[0]
            True
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
        return self.codomain().element_class(self.codomain(), coefficients={0:element})


class PSConvertToBase(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to its field of coefficients.

        EXAMPLES::

            sage: from dalgebra.dextension.puiseux import PuiseuxSeries
            sage: R = PuiseuxSeries(QQ, 'x')
            sage: R.base()(R(7))
            7
            sage: R.base()(R.gen())
            Traceback (most recent call last):
            ...
            TypeError: Impossible to convert the formal Puiseux series to the base ring, as it has non-zero higher order terms.
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
        if element.is_monomial() is True and element.order() == 0:
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
            out_dict = {k : self.base_map(element[k]) for k in element._PuiseuxSeries_Element__polydict}
            return self.codomain().element_class(self.codomain(), coefficients=out_dict)
        elif element.type() == PuiseuxSeries_Element.TYPES.rational:
            return self.codomain().element_class(self.codomain(),
                                                 numerator = self(element.numerator()),
                                                 denominator = self(element.denominator()))
        else: # default case
            if element.type() == PuiseuxSeries_Element.TYPES.dalgebraic:
                logger.warning("[dalgebraic] Coercion of differential algebraic formal Puiseux series between different bases is not yet implemented. Using default coercion.")
                # TODO (series): implement this option for dalgebraic
            new_map = lambda k: self.base_map(element[k])
            return self.codomain().element_class(self.codomain(),
                                                 coefficient_map=new_map, 
                                                 order=element.order(), 
                                                 ramification=element.ramification())


class PSCoerceFromPoly(Morphism):
    r'''
        Coercion morphism from the polynomial ring naturally embedded (at trivial ramification) in the Puiseux series ring.
    '''
    def __init__(self, domain, codomain: PuiseuxSeries_Ring, ramification: int = 1):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        elif ramification not in ZZ or ramification <= 0:
            raise ValueError(f"Ramification {ramification} must be a positive integer.")

        super().__init__(domain, codomain)
        self.ramification = ramification

    def _call_(self, element: Element) -> PuiseuxSeries_Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        out_dict = {k/ZZ(self.ramification): element[k] for k in range(element.degree()+1)}
        # element is a univariate polynomial
        return self.codomain().element_class(self.codomain(), coefficients=out_dict)


class PSConvertToPoly(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to the polynomial ring that is naturally embedded (at trivial ramification) into it.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring, codomain, ramification: int = 1):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        
        super().__init__(domain, codomain)
        self.ramification = ramification

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if self.ramification % element.ramification() != 0:
            raise TypeError("The desired ramification does not divide the actual ramification.")
        elif element.type() != element.TYPES.polynomial:
            raise TypeError("The element is not a polynomial.")
            ## TODO (series): implement special check for dalgebraic series
        elif element.order() < 0:
            raise TypeError("The element is not a polynomial (it has negative order).")

        var = self.codomain()(self.domain().variable_name(ramification = None if self.ramification == 1 else self.ramification))
        base = self.codomain().base()
        return sum(
            (base(coeff) * var**ZZ(k*self.ramification)
             for k, coeff in element._PuiseuxSeries_Element__polydict.items()),
            self.codomain().zero(),
        )


class PSConvertToRational(Morphism):
    r'''
        Conversion morphism from the Puiseux series ring to the field of rational functions that is naturally embedded (at trivial ramification) into it.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring, ramification: int = 1):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.rat_field(ramification=ramification)
        super().__init__(domain, codomain)
        self.ramification = ramification

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if self.ramification % element.ramification() != 0:
            raise TypeError("The desired ramification does not divide the actual ramification.")
        elif element.numerator().type() not in (element.TYPES.polynomial, element.TYPES.rational) or element.denominator().type() not in (element.TYPES.polynomial, element.TYPES.rational):
            raise TypeError("The numerator and denominator must be finite formal Puiseux series.")
            ## TODO (series): implement special check for dalgebraic series

        ## We convert both numerator and denominator to rational functions
        numerator = element.numerator()
        denominator = element.denominator()
        if numerator.type() == element.TYPES.rational:
            n = numerator.rational_function(self.ramification) # this may raise an error if the numerator was not fully finite
        else: # polynomial type (function polynomial is not enough, since we now allow negative order)
            name = element.parent().variable_name(
                None if self.ramification == 1 else self.ramification
            )
            var = element.parent().poly_ring(ramification=self.ramification)(name)
            base = element.parent().base().to_sage()
            n = sum(base(coeff) * var**ZZ(k*self.ramification) for (k,coeff) in numerator._PuiseuxSeries_Element__polydict.items())
        # Denominator
        if denominator.type() == element.TYPES.rational:
            d = denominator.rational_function(self.ramification) # this may raise an error if the denominator was not fully finite
        else: # polynomial type (function polynomial is not enough, since we now allow negative order)
            name = element.parent().variable_name(
                None if self.ramification == 1 else self.ramification
            )
            var = element.parent().poly_ring(ramification=self.ramification)(name)
            base = element.parent().base().to_sage()
            d = sum(base(coeff) * var**ZZ(k*self.ramification) for (k,coeff) in denominator._PuiseuxSeries_Element__polydict.items())

        return n / d


class PSCoerceToSage(Morphism):
    r'''
        Coercion morphism from the Puiseux series ring to corresponding structure in SageMath.

        WARNING: SageMath structure do not preserve infinite tails of the elements.
    '''
    def __init__(self, domain: PuiseuxSeries_Ring):
        if not isinstance(domain, PuiseuxSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.to_sage()
        super().__init__(domain, codomain)

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.type() == element.TYPES.polynomial:
            var = self.codomain().gen()
            base = self.domain().base().to_sage()
            return sum(
                (base(coeff) * var**k for k, coeff in element._PuiseuxSeries_Element__polydict.items()),
                self.codomain().zero(),
            )
        elif element.type() == element.TYPES.rational:
            return self(element.numerator()) / self(element.denominator())
        else:
            var = self.codomain().gen()
            out =  sum(
                self.domain().base().to_sage()(element[k]) * var**k
                for k in rat_range(element.order(), PS_GLOBAL_BOUND+(1/element.ramification()), 1/element.ramification())
            )
            return out.add_bigoh(PS_GLOBAL_BOUND+1)
            


class PSConvertFromSage(Morphism):
    r'''
        Coercion morphism from the Puiseux series ring to corresponding structure in SageMath.

        WARNING: SageMath structure do not preserve infinite tails of the elements.
    '''
    def __init__(self, codomain: PuiseuxSeries_Ring):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The codomain must be a formal power series ring")
        domain = codomain.to_sage()
        super().__init__(domain, codomain)

    def _call_(self, element: PuiseuxSeries_Element) -> Element:
        r'''
            See :func:`Morphism._call_` for further information.

            ::NO EXAMPLE::
        '''
        if element.prec() < oo:
            raise ValueError("A finite-precision Sage Puiseux series cannot be reconstructed exactly.")
        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(v) * x**k for k, v in zip(element.exponents(), element.coefficients()))


class PSCoerceFromDRing(Morphism):
    r'''
        Coercion morphism from a differential ring to the Puiseux series ring.

        This is a generic morphism that coerce a differential ring into a field of Puiseux series. It 
        takes a callable that builds the Puiseux series of an element in a differential ring. It overlaps
        with the other coercions from the base ring, which is always the field of constants.
    '''
    def __init__(self, domain: Parent, codomain: PuiseuxSeries_Ring, *, map: Callable[[Element], PuiseuxSeries_Element]):
        if not isinstance(codomain, PuiseuxSeries_Ring):
            raise TypeError("The codomain must be a formal Puiseux series ring")
        super().__init__(domain, codomain)
        self.__map = map

    def _call_(self, element: Element) -> PuiseuxSeries_Element:
        return self.__map(element)
        
        
