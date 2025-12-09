from __future__ import annotations

r'''
    Module to create univariate formal power series over a given differential field of constants.

    EXAMPLES::

        sage: from dalgebra import FPSeriesRing
        sage: R.<x> = FPSeriesRing(QQ, differential=True)
        sage: R
        Differential ring of Formal Power series in x over Differential Ring [[Rational Field], (0,)]
        sage: x^2 - x + 1
        x^2 - x + 1
        sage: 1/(1-x)
        1 + x + x^2 + x^3 + x^4 + x^5 + x^6 + x^7 + x^8 + x^9 + O(x^10)
        sage: (1/(1-x)).derivative()
        1 + 2*x + 3*x^2 + 4*x^3 + 5*x^4 + 6*x^5 + 7*x^6 + 8*x^7 + 9*x^8 + 10*x^9 + O(x^10)
        
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

from enum import Enum

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.functions.other import binomial, factorial
from functools import lru_cache
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
from ..dpolynomial.dpolynomial import DPolynomial, DPolynomialRing, DPolynomialRing_Monoid

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)

#################################################################################
###
### FACTORY FOR PSEUDO DIFFERENTIAL OPERATORS
###
#################################################################################
GLOBAL_BOUND = 50


def PSChangeBound(bound: int):
    global GLOBAL_BOUND
    if bound not in ZZ or bound < 0:
        raise ValueError(f"The bound must be a non-negative integer, got {bound}.")
    GLOBAL_BOUND = bound


def CheckBound(func):
    from functools import wraps

    @wraps(func)
    def wrapper(self: PSeries_Element | PSeries_Ring, *args, **kwds):
        import inspect
        sig = inspect.signature(func)
        if "bound" not in sig.parameters:
            raise TypeError(f"The method {func.__name__} does not accept a 'bound' argument.")
        elif sig.parameters["bound"].default is not None:
            raise TypeError(f"The method {func.__name__} does not accept a default value for 'bound'.")
        value = kwds.pop("bound") if "bound" in kwds else GLOBAL_BOUND

        if value not in ZZ or value < 0:
            raise TypeError(f"The method {func.__name__} requires a non-negative integer 'bound' argument to be passed.")

        kwds["bound"] = value

        return func(self, *args, **kwds)
    return wrapper


#################################################################################
###
### FACTORY FOR PSEUDO DIFFERENTIAL OPERATORS
###
#################################################################################
class PSeries_RingFactory(UniqueFactory):
    r'''
        Factory to create the ring of pseudo-differential operators.

        This allows to cache the same rings created from different objects. See
        :class:`PSeries_Ring` for further information on this structure.
    '''
    def create_key(self, base, name: str = None, **kwds):
        if base not in _Fields:
            raise TypeError("The base ring must be a field")
        # We check now whether the base ring is valid or not
        if base not in _DRings:
            base = DifferentialRing(base) # automatically add the zero derivative

        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The given ring must be a differential ring with just 1 derivation.")
        elif base.constant_ring() != base:
            raise TypeError("The base ring must be a field of constants.")

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

    def create_object(self, _, key) -> PSeries_Ring:
        base, name = key

        return PSeries_Ring(base, name)


PSeries = PSeries_RingFactory("dalgebra.pseries.pseries.PSeries_Element")


class PSeries_Element(Element):
    r'''
        Class representing a formal power series.

        A formal power series is a formal sum over a given variable with coefficients in a field tat will be considered as constants. 
        
        These objects are non-finite by nature (elements tend to have infinite tails). This class handles this infinite tail 
        by storing a method that computes (upon request) the coefficients for any given integer.

        This class has a clear limitation: computations are usually non exact. For example, the traditional zero-checking can only be performed
        up to some given order. These methods have an optional parameter ``bound`` that allows to specify the order up to which computations are
        performed.

        We allow three different ways to create a formal power series:
        1. By providing a ``coefficient_map``, which is a callable that receives an integer and returns the corresponding coefficient. This is the most generic way to create a formal power series. We never have a criteria for zero testing.
        2. By providing a finite list or map of elements as ``coefficients``. This creates a finite formal power series, and all computations are exact. This is the case of considering polynomials as formal power series.
        3. By providing a differential polynomial in one variable with coefficients in the constant field. This is interpret as a differential algebraic equation that the formal power series must satisfy. We require for this input a set of initial conditions that determines the formal power series uniquely. This is the most complex way to create a formal power series, but it allow for zero testing while keeping the tail infinite.
    '''
    TYPES = Enum('Type', [("default",0), ("polynomial", 1), ("dalgebraic", 2)])

    def __init__(self, parent: PSeries_Ring, *,
                 coefficient_map: Callable[[int],Element] | None = None,
                 coefficients: Collection[Element] | Mapping[int, Element] | None = None,
                 differential_equation: DPolynomial | None = None, initial_conditions: Collection[Element] | Mapping[int, Element] | None = None
    ):
        base = parent.base()

        default = coefficient_map is not None
        polynomial = coefficients is not None
        dalgebraic = differential_equation is not None and initial_conditions is not None

        if not any((default, polynomial, dalgebraic)):
            raise TypeError("You must provide at least one of the following arguments: coefficient_map, coefficients, differential_equation and initial_conditions.")
        elif sum((default, polynomial, dalgebraic)) > 1:
            raise TypeError("You can only provide one of the following arguments: coefficient_map, coefficients, differential_equation and initial_conditions.")
        
        if default:
            # We set the type of the power series
            self.__type = self.TYPES.default
            
            # We create the cached function to get the coefficients
            self.__map = coefficient_map
            self.__poly = None
            self.__dalgebraic = None
        elif polynomial:
            self.__type = self.TYPES.polynomial

            if not isinstance(coefficients, Mapping):
                self.__poly = {i: base(c) for (i,c) in enumerate(coefficients) if c != base.zero()}
            elif any(k < 0 for k in coefficients.keys()):
                raise ValueError("Polynomial coefficients can not have negative degree.")
            else:
                self.__poly = {k: base(v) for k, v in coefficients.items() if base(v) != base.zero()}
            self.__map = None
            self.__dalgebraic = None
        else: # dalgebraic
            self.__type = self.TYPES.dalgebraic
            differential_equation = parent.equ_ring()(differential_equation)

            # small analysis for the initial conditions
            DEP = differential_equation.parent()
            u = DEP.gens()[0]
            
            o = differential_equation.order(u)
            d = differential_equation.degree(u[o])

            if d > 1:
                raise TypeError("Only equations linear in their highest order are allowed.")

            # We convert the initial conditions into the sequence elements
            if isinstance(initial_conditions, Mapping):
                initial_conditions = [base(initial_conditions.get(i, base.zero())/factorial(i)) for i in range(max(initial_conditions.keys()) + 1)]
            else:
                initial_conditions = [base(c/factorial(i)) for i, c in enumerate(initial_conditions)]

            if len(initial_conditions) < o:
                raise ValueError(f"You must provide at least {o} initial conditions, got {len(initial_conditions)}.")
            
            self.__dalgebraic = (differential_equation, initial_conditions)
            self.__map = None
            self.__poly = None

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
            if any(self[k] != self.parent().base().zero() for k in range(bound+1)):
                return False
            return bound
        elif self.__type == self.TYPES.polynomial:
            return len(self.__poly) == 0
        else: # dalgebraic
            return all(el == 0 for el in self.__dalgebraic[1])

    @CheckBound
    def is_one(self, *, bound: int | None = None) -> bool | int: #: Checker for the identity element
        return (self - self.parent().one()).is_zero(bound=bound)

    @CheckBound
    def order(self, *, bound: int | None = None) -> int: # Gets degree of first non-zero element
        r'''
            Method to get the order of a formal power series.
        '''
        if self.__type == self.TYPES.default:
            for i in range(bound+1):
               if self[i] != 0:
                   return i
            return bound
        else:
            if self.is_zero():
                return oo
            elif self.__type == self.TYPES.polynomial:
                return min(self.__poly.keys())
            else: # dalgebraic
                # at least one is non-zero
                for i in range(len(self.__dalgebraic[1])):
                    if self.__dalgebraic[1][i] != 0:
                        return i
                else:
                    raise ValueError("This should not happen, as the element is not zero.")
        
    def type(self) -> PSeries_Element.TYPES:
        r'''
            Method to get the type of formal power series.
        '''
        return self.__type

    def is_finite(self) -> bool:
        r'''
            Method to check whether the formal power series is finite or not.
        '''
        return self.__type == self.TYPES.polynomial

    def truncate(self, order: int) -> PSeries_Element:
        r'''
            Return a :class:`PSeries_Element` that contains only the coefficients with degree at most than or equal to ``order``.

            This method always return a finite formal power series, even if the original one is not finite.
        '''
        coeffs = {k : self[k] for k in range(order+1)}
        return self.parent().element_class(self.parent(), coefficients=coeffs)

    def polynomial(self) -> Element:
        if self.__type == self.TYPES.polynomial:
            return self.parent().poly_ring()(self)
        raise TypeError("The element is not a polynomial formal power series.")

    def equation(self) -> DPolynomial:
        r'''
            Gets the differential equation that defines the element. (Not always possible)
        '''
        if self.__type == self.TYPES.polynomial:
            from sage.arith.misc import GCD
            c = self.polynomial()
            d = c.derivative()
            g = GCD(c,d)
            u = self.parent().equ_ring().gens()[0]
            return (c//g)*u[1]-(d//g)*u[0] 
        elif self.__type == self.TYPES.dalgebraic:
            return self.__dalgebraic[0]
        raise TypeError("The element is not defined by a differential equation.")

    def __getitem__(self, key: int) -> Element:
        if key not in self.__cache_computed:
            if self.__type == self.TYPES.default:
                self.__cache_computed[key] = self.parent().base()(self.__map(key))
            elif self.__type == self.TYPES.polynomial:
                self.__cache_computed[key] = self.__poly.get(key, self.parent().base().zero())
            else: # dalgebraic
                if key < len(self.__dalgebraic[1]):
                    self.__cache_computed[key] = self.__dalgebraic[1][key]
                else:
                    ## TODO: Fix this using the non-constant coefficients properly
                    equ = self.__dalgebraic[0]
                    u = equ.parent().gens()[0]
                    o = equ.order(u)

                    equ = equ.derivative(times=key-o) # now the equation is of order key
                    denom = equ.coefficient_full(u[o])
                    num = denom*u[o] - equ

                    num_val = num.polynomial()(**{str(u[i]): self[i]*factorial(i) for i in range((key))})
                    denom_val = denom.polynomial()(**{str(u[i]): self[i]*factorial(i) for i in range((key))})
                    self.__cache_computed[key] = num_val / denom_val / factorial(key)
            
        return self.__cache_computed[key]
    

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: PSeries_Element) -> PSeries_Element:
        ## Checking for trivial cases
        if self.is_zero() is True:
            return other
        elif other.is_zero() is True:
            return self
        
        if any(el.__type == self.TYPES.default for el in (self, other)):
            # at least one is default
            add_map = lambda k : self[k] + other[k]
            return self.parent().element_class(self.parent(), coefficient_map=add_map)
        elif self.__type == self.TYPES.polynomial and other.__type == self.TYPES.polynomial: # polynomial case
            out = self.__poly.copy()
            for k, v in other.__poly.items():
                if k in out:
                    out[k] += v
                else:
                    out[k] = v
            return self.parent().element_class(self.parent(), coefficients=out)
        else: # at least one is dalgebraic
            self_equ = self.equation()
            other_equ = other.equation()

            u = self_equ.parent().gens()[0]

            # TODO: To be implemented
            new_equ = self_equ.add_sol(other_equ, u)
            new_initials = {k: self[k] + other[k] for k in range(new_equ.order(u)+1)}

            return self.parent().element_class(self.parent(), differential_equation=new_equ, initial_conditions=new_initials)

    def __neg__(self) -> PSeries_Element:
        if self.is_zero() is True:
            return self
        if self.__type == self.TYPES.polynomial:
            coeffs = {k: -self[k] for k in self.__poly}
            return self.parent().element_class(self.parent(), coefficients=coeffs)
        elif self.__type == self.TYPES.dalgebraic:
            equ = self.equation()
            u = equ.parent().gens()[0]
            new_equ = equ(**{u.variable_name(): -u[0]})
            new_initials = {k: -self[k] for k in range(new_equ.order(u)+1)}
            return self.parent().element_class(self.parent(), differential_equation=new_equ, initial_conditions=new_initials)
        else:
            neg_map = lambda k : -self[k]
            
            return self.parent().element_class(self.parent(), coefficient_map=neg_map)

    def _sub_(self, other: PSeries_Element) -> PSeries_Element:
        return self + (-other)

    def _mul_(self, other: PSeries_Element) -> PSeries_Element:
        if (self.is_zero() is True) or (other.is_zero() is True):
            return self.parent().zero()
        elif (self.is_one() is True):
            return other
        elif (other.is_one() is True):
            return self
        
        if any(el.__type == self.TYPES.default for el in (self, other)):
            # at least one is default
            add_map = lambda k : sum(self[i]*other[k-i] for i in range(k+1))
            return self.parent().element_class(self.parent(), coefficient_map=add_map)
        elif self.__type == self.TYPES.polynomial and other.__type == self.TYPES.polynomial: # polynomial case
            out = dict()
            for i in self.__poly:
                for j in other.__poly:
                    out[i+j] = out.get(i+j, self.parent().base().zero()) + self[i]*other[j]
                    
            return self.parent().element_class(self.parent(), coefficients=out)
        else: # at least one is dalgebraic
            self_equ = self.equation()
            other_equ = other.equation()
            u = self_equ.parent().gens()[0]

            ## TODO: To be implemented
            new_equ = self_equ.mul_sol(other_equ, u)
            new_initials = {k: self[k] + other[k] for k in range(new_equ.order(u)+1)}

            return self.parent().element_class(self.parent(), differential_equation=new_equ, initial_conditions=new_initials)

    @cached_method
    def __invert__(self) -> PSeries_Element:
        r'''
            Computes the multiplicative inverse of the formal power series.
        '''
        if self[0] == 0:
            raise ZeroDivisionError(f"Inverse of element with zero constant term do not exist: {self}.")
        
        @lru_cache(maxsize=256)
        def inverse_coeffs(k: int) -> Element:
            if k == 0:
                return 1 / self[0]
            else:
                num = sum(self[k-i]*inverse_coeffs(i) for i in range(0, k))
                denom = -inverse_coeffs(0)
                return num * denom
            
        if self.__type == self.TYPES.default:
            return self.parent().element_class(self.parent(), coefficient_map=inverse_coeffs)
        else: # There is an equation
            self_equ = self.equation()
            u = self_equ.parent().gens()[0]

            new_equ = self_equ(**{u.variable_name(): ~u[0]}).numerator()
            new_initials = {k: inverse_coeffs(k) for k in range(new_equ.order(u)+1)}
            return self.parent().element_class(self.parent(), differential_equation=new_equ, initial_conditions=new_initials)

    @cached_method
    def __pow__(self, power: int | Rational) -> PSeries_Element:
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
                a0 = self[0]
                b0 = a0**power # this checks if the operation can be done
                a_inv = ~self # this also checks if the operation can be done
                goal_parent = pushout(b0.parent(), self.parent()) # this is usually self.parent()

                @lru_cache(maxsize=256)
                def coeff_root(t: int) -> Element:
                    if t == 0:
                        return b0
                    result = goal_parent.base().zero()
                    for j in range(t):
                        to_add = goal_parent.base().zero()
                        for k in range(0, t-j):
                            to_add += a_inv[k]*sum((self[i+1] for i in range(t-j-k)), goal_parent.base().zero())
                        result += coeff_root(j) * to_add
                    return result

                return self.parent().element_class(self.parent(), coefficient_map=coeff_root)
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

    ###################################################################################
    @CheckBound
    def __repr__(self, *, bound: int | None = None) -> str:
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()

        def term_str(order:int, element:Element, first:bool=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""
            ## If the element is 1, we just return the monomial
            if element in (1, -1):
                if element == -1:
                    element = -element
                    sign = " - " if not first else "-"
                else:
                    sign = " + " if not first else ""

                if order == 0:
                    op_str = "1"
                elif order == 1:
                    op_str = f"{g}"
                else:
                    op_str = f"{g}^{order}"
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

                if order == 0:
                    op_str = ""
                elif order == 1:
                    op_str = f"{g}"
                else:
                    op_str = f"{g}^{order}"

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
            order = self.order(bound=bound)

            return term_str(order, self[order], True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, bound+1) 
                if self[o] != 0
            ) + (f" + O({term_str(bound+1,1,True)})")

    @CheckBound
    def _latex_(self, *, bound: int | None = None) -> str:
        if self.is_zero() is True:
            return "0"
        elif self.is_one() is True:
            return "1"

        ## We know there is something in the element
        g = self.parent().gen_name()

        def term_str(order, element, first=False):
            ## Some cases:
            ## If element is 0 we return nothing
            if element == 0: return ""
            ## If the element is 1, we just return the monomial
            if element == 1:
                if order == 0:
                    output = "1"
                elif order == 1:
                    output = f"{latex_variable_name(g)}"
                else:
                    output = f"{latex_variable_name(g)}^{{{order}}}"
            else: # element is something != 1
                if str(element)[0] == "-":
                    sign = " - " if not first else "-"
                    element = -element
                else:
                    sign = " + " if not first else ""

                if any(char in str(element) for char in ("+", "/", "*", "-", " ")): # case with several terms
                    el_str = f"\\left({latex(element)}\\right)"
                else:
                    el_str = latex(element)

                if order == 0:
                    op_str = ""
                elif order == 1:
                    op_str = f"{latex_variable_name(g)}"
                else:
                    op_str = f"{latex_variable_name(g)}^{{{order}}}"

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
            order = self.order(bound=bound)

            return term_str(order, self[order], True) + "".join(
                term_str(o, self[o]) 
                for o in range(order+1, bound+1) 
                if self[o] != 0
            ) + (f" + \\text{{O}}({term_str(bound+1,1,True)})")

class PSeries_Ring(Parent):
    r'''
        Class for a ring of power series over a :class:`~dalgebra.dring.DRing`.

        Given a ring `R`, we can always define the ring of formal power series `R[[x]]` whose elements
        are formal power series in a new variable `x`. Here we can define the standard derivation, where 
        all the elements of `R` are considered as constants and `\partial(x) = 1`.

        INPUT:

        * ``base``: a ring with the zero derivative.
        * ``name``: name that the variable `x` will have.

        TODO: add examples
    '''
    Element = PSeries_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif isinstance(base, PSeries_Ring):
            raise TypeError("The base must not be a formal power series ring")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")
        elif base.constant_ring() != base:
            raise TypeError("The base ring must be a field of constants.")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.__operators = [self.__build_derivation()]
        self.__gen = self.element_class(self, coefficients={1: self.base().one()})
        self.__poly_ring = PolynomialRing(base.to_sage(), name)
        self.__d_poly_ring = DifferentialRing(self.__poly_ring)
        # self.__equ_ring = DPolynomialRing(self.d_poly_ring().fraction_field(), "u")
        self.__equ_ring = DPolynomialRing(self, "u")

        ## Setting up basic conversions
        try:
            self.base().register_conversion(PSConvertToBase(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(PSCoerceFromPoly(self))
            self.poly_ring().register_conversion(PSConvertFromPoly(self))
        except AssertionError: # This conversion was already registered
            pass
        try:
            self.register_coercion(PSCoerceFromDPoly(self))
            self.d_poly_ring().register_conversion(PSConvertFromDPoly(self))
        except AssertionError: # This conversion was already registered
            pass

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        return self.__gens[0]

    def gen(self) -> PSeries_Element:
        r'''
            Return the generator of the ring of pseudo-differential operators.
        '''
        return self.__gen
    
    def gens(self) -> tuple[PSeries_Element]:
        r'''
            Return the generators of the ring of pseudo-differential operators.
        '''
        return (self.__gen,)

    def ngens(self) -> int:
        r'''
            Return the number of generators of the ring of pseudo-differential operators.
        '''
        return 1

    def one(self) -> PSeries_Element:
        r'''
            Return the identity element of the ring of pseudo-differential operators.
        '''
        return self.element_class(self, coefficients=[0,self.base().one()])

    def zero(self) -> PSeries_Element:
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
        return True

    def poly_ring(self) -> Parent:
        r'''
            Return the polynomial ring associated to this ring this ring of formal power series
        '''
        return self.__poly_ring
    
    def d_poly_ring(self) -> Parent:
        r'''
            Return the differential polynomial ring associated to this ring of formal power series.
        '''
        return self.__d_poly_ring
    
    def equ_ring(self) -> DPolynomialRing_Monoid:
        r'''
            Return the differential polynomial ring associated to this ring of formal power series.
        '''
        return self.__equ_ring

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        return PSCoerceFromBase(self)

    def construction(self) -> tuple[PseudoDOperatorFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return PseudoDOperatorFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        raise NotImplementedError("Formal Power series does not allow a fraction field structure. (A Laurent series implementation is required)")

    def change_base(self, R: Parent) -> PSeries_Ring:
        new_ring = PSeries(R, self.gen_name())
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
        return f"Formal Power Series Ring in {self.__gens[0]} over {self.base()}"

    def _latex_(self):
        return f"{latex(self.base())}\\left[\\left[{self.__gens[0]}\\right]\\right]"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        up_bound : int = 0, lower_bound : int = 0,
        *args,**kwds
    ) -> PSeries_Element:
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

    def add_constants(self, *new_constants: str) -> PSeries_Ring:
        return PSeries(self.base().add_constants(*new_constants), self.__gens[0])

    def linear_operator_ring(self):
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError("Linear operator ring over Formal Power Series not yet implemented")

    def inverse_operation(self, element: PSeries_Element, operation: int = 0) -> PSeries_Element:
        if element not in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if operation != 0:
            raise ValueError(f"The given operation({operation}) is not valid")

        if element.type() == PSeries_Element.TYPES.polynomial:
            return self.element_class(self, coefficients={k+1: element[k]/(k+1) for k in self._PSeries_Element__poly})
        elif element.type() == PSeries_Element.TYPES.dalgebraic:
            equ = element.equation()
            u = equ.parent().gens()[0]

            inits = {0: self.base().zero()}
            for k in range(equ.order(u)+1):
                inits[k+1] = element[k]/(k+1)

            return self.element_class(self, 
                                        differential_equation=equ(**{u.variable_name(): u[1]}), 
                                        initial_conditions=inits
            )
        else:
            return self.element_class(self, coefficient_map=lambda k: 0 if k == 0 else element[k-1]/k)

    def __build_derivation(self) -> AdditiveMap:
        r'''
            Internal method to build the derivation of the ring of pseudo-differential operators.
        '''
        def derivation_map(element: PSeries_Element) -> PSeries_Element:
            if element.type() == PSeries_Element.TYPES.polynomial:
                return self.element_class(self, coefficients={k-1: element[k]*k for k in element._PSeries_Element__poly if k > 0})
            elif element.type() == PSeries_Element.TYPES.dalgebraic:
                equ = element.equation()
                u = equ.parent().gens()[0]

                while(equ.degree(u[0]) > 0):
                    a = equ.coefficient_full(u[0]**equ.degree(u[0]))
                    c = a.derivative()
                    equ = a*equ.derivative() - c*equ # this reduces the degree of u[0]
                assert equ.degree(u[u.order(u)]) == 1, "The equation must be linear in its highest order after reduction."

                return self.element_class(self, 
                                          differential_equation=equ.derivative()(**{u.variable_name(): u[0]}), 
                                          initial_conditions={k: element[k+1]*(k+1) for k in range(equ.order(u)+1)}
                )
            else:
                return self.element_class(self, coefficient_map=lambda k: (k+1)*element[k+1])

        return AdditiveMap(self, derivation_map)

    @staticmethod
    def evaluate_dpoly_at_zero(dpoly: DPolynomial, **kwds: PSeries_Element) -> Element:
        r'''
            Static method to evaluate a differential polynomial at given formal power series without computing the full substitution.

            INPUT:

            * ``dpoly``: a differential polynomial in the differential polynomial ring over the formal power series base ring.
            * ``kwds``: dictionary with the variables to substitute and their corresponding formal power series.

            OUTPUT:

            An :class:`Element` resulting from the evaluation of ``dpoly`` at the given formal power series.
        '''
        from functools import reduce

        DRing = dpoly.parent()

        if not isinstance(DRing, DPolynomialRing_Monoid):
            raise TypeError("The differential polynomial must be in a differential polynomial ring.")
        variables = DRing.variable_names()
        
        ## We check the inputs in kwds
        if any(v not in variables for v in kwds):
            raise ValueError("Some variable in the differential polynomial is not in the given keywords.")
        if any(v not in kwds for v in variables):
            raise ValueError("Some variable in the differential polynomial is missing in the given keywords.")
        
        ## We compute the pushout of the parents for kwds
        data = list(kwds.values())
        output = data[0].parent()
        output = reduce(lambda x,y: pushout(x,y), (d.parent() for d in data[1:]), output)

        if not isinstance(output, PSeries_Ring):
            raise TypeError("The resulting ring after pushout is not a formal power series ring.")
        
        newRing = DRing.change_ring(output)
        dpoly = newRing(dpoly)

        result = output.base().zero()
        for mon,coeff in zip(dpoly.monomials(), dpoly.coefficients()):
            term = output.base().one()
            for var, exp in mon._variables:
                i,o = var
                term *= (kwds[variables[i]][o]/factorial(o))**exp ## TODO: Check this operation
            result += term * coeff[0]
        return result
        

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
        return PSeries(x,self.__operator_name)

    def _repr_(self):
        return f"PSeries(*,{self.__operator_name})"

    def __eq__(self, other):
        if other.__class__ == self.__class__:
            return self.__operator_name == other.__operator_name


class PSCoerceFromBase(Morphism):
    def __init__(self, codomain: PSeries_Ring):
        if not isinstance(codomain, PSeries_Ring):
            raise TypeError("The codomain must be a formal power series ring")

        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> PSeries_Element:
        return self.codomain().element_class(self.codomain(), coefficients=[element])


class PSConvertToBase(Morphism):
    def __init__(self, domain: PSeries_Ring):
        if not isinstance(domain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")

        super().__init__(domain, domain.base())

    def _call_(self, element: PSeries_Element) -> Element:
        if (element - element[0]).is_zero() is True:
            return self.codomain()(element[0])
        else:
            raise TypeError("Impossible to convert the formal power series to the base ring, as it has non-zero higher order terms.")

class PSCoerceBetweenBases(Morphism):
    def __init__(self, domain: PSeries_Ring, codomain: PSeries_Ring, map: Morphism):
        if not isinstance(domain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        if not isinstance(codomain, PSeries_Ring):
            raise TypeError("The codomain must be a formal power series ring")
        if not map.domain() == domain.base() or not map.codomain() == codomain.base():
            raise ValueError("Error in the format for the morphism")

        self.base_map = map

        super().__init__(domain, codomain)

    def _call_(self, element: PSeries_Element) -> PSeries_Element:
        if element.type() == PSeries_Element.TYPES.polynomial:
            return self.codomain().element_class(self.codomain(),
                                                 coefficients={k: self.base_map(element[k]) for k in self._PSeries_Element__poly})
        elif element.type() == PSeries_Element.TYPES.dalgebraic:
            equ = element._PSeries_Element__dalgebraic[0]
            u = equ.parent().gens()[0]

            new_equ = equ.change_base(self.base_map)
            new_initials = {k: self.base_map(element[k]) for k in range(new_equ.order(u)+1)}

            return self.codomain().element_class(self.codomain(),
                                                 differential_equation=new_equ,
                                                 initial_conditions=new_initials)
        else: # default case
            new_map = lambda k: self.base_map(element[k])
            return self.codomain().element_class(self.codomain(),
                                                 coefficient_map=new_map)

class PSCoerceFromPoly(Morphism):
    def __init__(self, codomain: PSeries_Ring):
        if not isinstance(codomain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        domain = codomain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: Element) -> DPolynomial:
        # element is a univariate polynomial
        return self.codomain().element_class(self.codomain(),
                                             coefficients={k: element[k] for k in range(element.degree()+1)})
    
class PSConvertFromPoly(Morphism):
    def __init__(self, domain: PSeries_Ring):
        if not isinstance(domain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: PSeries_Element) -> Element:
        if element.type() != PSeries_Element.TYPES.polynomial:
            raise ValueError("The element must be finite to convert it to a polynomial")
        
        x = self.codomain().gen()
        B = self.codomain().base()
        return sum(B(element[k]) * x**k for k in element._PSeries_Element__poly)
    
class PSCoerceFromDPoly(Morphism):
    def __init__(self, codomain: PSeries_Ring):
        if not isinstance(codomain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        domain = codomain.d_poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: DPolynomial) -> PSeries_Element:
        return self.codomain()(self.codomain().wrapped(element))
    
class PSConvertFromDPoly(Morphism):
    def __init__(self, domain: PSeries_Ring):
        if not isinstance(domain, PSeries_Ring):
            raise TypeError("The domain must be a formal power series ring")
        codomain = domain.d_poly_ring()

        super().__init__(domain, codomain)

    def _call_(self, element: PSeries_Element) -> DPolynomial:
        return self.codomain()(self.codomain().wrapped(element))
