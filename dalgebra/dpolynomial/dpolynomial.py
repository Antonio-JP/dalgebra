from __future__ import annotations

import logging

from itertools import product

from sage.calculus.functional import diff
from sage.categories.category import Category
from sage.categories.monoids import Monoids
from sage.categories.morphism import Morphism, SetMorphism
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.categories.sets_cat import Sets
from sage.matrix.constructor import matrix
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.misc_c import prod
from sage.modules.free_module_element import vector
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing, InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.rings.integer_ring import ZZ
from sage.rings.ring import Ring
from sage.sets.family import LazyFamily
from sage.structure.element import Element, Matrix
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent
from sage.symbolic.ring import SR

from typing import Collection

from ..dring import DRings, DFractionField, AdditiveMap, DifferentialRing, DifferenceRing
from .dmonoids import DMonomialMonoid, DMonomialGen, DMonomial, IndexBijection

logger = logging.getLogger(__name__)
_DRings = DRings.__classcall__(DRings)
_Sets = Sets.__classcall__(Sets)

## Factories for all structures
class DPolynomialRingFactory(UniqueFactory):
    r'''
        Factory to create a ring of polynomials over a ring with operators.

        This allows to cache the same rings created from different objects. See
        :class:`DPolynomialRing_Monoid` for further information on this structure.
    '''
    def create_key(self, base, *names : str, **kwds):
        if "names" in kwds and len(names) > 0:
            raise ValueError("Duplicated values for names")
        if len(names) == 1 and isinstance(names[0], (list, tuple)):
            names = names[0]
        names = tuple(kwds.pop("names", names))

        # We check now if base is an infinite polynomial ring to gather more names or not
        if isinstance(base, InfinitePolynomialRing_dense) or isinstance(base, InfinitePolynomialRing_sparse):
            names = tuple(list(base._names) + list(names))
            base = base.base()

        if len(names) == 0:
            raise ValueError("No variables given: impossible to create a ring")
        if len(set(names)) < len(names):
            raise ValueError("Repeated names given: impossible to create the ring")

        ## Method to create sorting keys for variable names:
        ## We split the underscores and sort lexicographically transforming numbers when possible.
        def _name_sorting_criteria(name):
            el = name.split("_")
            for i,part in enumerate(el):
                try:
                    el[i] = ZZ(part)
                except Exception:
                    pass
            return tuple(el)

        names = tuple(sorted(names, key=_name_sorting_criteria))

        # We check now whether the base ring is valid or not
        if base not in _DRings:
            raise TypeError("The base ring must have operators attached")

        # Now the names are appropriate and the base is correct
        return (base, names)

    def create_object(self, _, key) -> DPolynomialRing_Monoid:
        base, names = key

        return DPolynomialRing_Monoid(base, names)


DPolynomialRing = DPolynomialRingFactory("dalgebra.dpolynomial.dpolynomial.DPolynomialRing")
RWOPolynomialRing = DPolynomialRing #: alias for DPolynomialRing (used for backward compatibility)
def DifferentialPolynomialRing(base, *names : str, **kwds) -> DPolynomialRing_Monoid:
    if base not in _DRings:
        base = DifferentialRing(base, kwds.pop("derivation", diff))
    if not base.is_differential():
        raise TypeError("The base ring must be a differential ring")
    return DPolynomialRing(base, *names, **kwds)
def DifferencePolynomialRing(base, *names : str, **kwds) -> DPolynomialRing_Monoid:
    if base not in _DRings:
        base = DifferenceRing(base, kwds.pop("difference", base.Hom(base).one()))
    if not base.is_difference():
        raise TypeError("The base ring must be a difference ring")
    return DPolynomialRing(base, *names, **kwds)

class DPolynomial(Element):
    r'''
        Class for a DPolynomial.

        A DPolynomial is a sum of terms formed as a coefficient times a :class:`DMonomial`.
        This is a sparse representation of d-polynomials.
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, input : DPolynomial | list[tuple[DMonomial, Element]] | dict[DMonomial, Element]):
        if isinstance(input, DPolynomial):
            input = input._content # this convert input to a dict
        elif isinstance(input, (list, tuple)):
            input = dict(input) # we convert it to a dictionary

        if not isinstance(input, dict):
            raise TypeError("[DPolynomial] Incorrect type for input")
        if any(not isinstance(k, DMonomial) for k in input):
            raise TypeError("[DPolynomial] The keys for a DPolynomial must be DMonomials")
        # Here we cast everything to be in the correct parent
        self._content: dict[DMonomial,Element] = {parent.monoids()(mon) : parent.base()(coeff) for (mon, coeff) in input.items() if coeff != 0}

        super().__init__(parent)

    ## TODO: Add element "monomial_coefficients"

    ###################################################################################
    ### Property methods
    ###################################################################################
    def is_zero(self) -> bool: #: Checker for the zero element -> nothing on the _content.
        return len(self._content) == 0

    def is_term(self) -> bool: #: Checker for terms -> elements with just one monomial
        return len(self._content) == 1

    def is_monomial(self) -> bool: #: Checker for monomials -> just one monomial and coefficient 1
        return self.is_term() and self.coefficients()[0] == self.parent().base().one()

    def is_variable(self) -> bool: #: Checker for variable -> just one monomial that is a variable
        return self.is_monomial() and next(iter(self._content)).is_variable()

    def is_unit(self) -> bool: #: Checker for an element to be a unit (i.e., has degree 0)
        return self.degree() == 0

    def is_linear(self, variables: Collection[DMonomialGen | DPolynomial] = None):
        r'''
            Method to check if a d-polynomial is linear w.r.t. some variables.

            We allow as input either generators (and we check linearity w.r.t. to all variables withing those generators)
            or variables of the ring.

            A polynomial is linear w.r.t. a set of variables if no monomial has a combined degree higher than 1.
        '''
        # processing the variables
        if variables is None:
            return self.degree() <= 1
        if not isinstance(variables, (list, tuple)):
            raise TypeError("Variables for checking linearity must be given as tuple/list")

        variables = [v if isinstance(v, DMonomialGen) and v in self.parent().gens() else self.parent()(v) for v in variables]
        variables = [v for v in self.variables() if any(v in g if isinstance(g, DMonomialGen) else v == g for g in variables)]

        return max(sum(m.degree(next(iter(v._content))) for v in variables) for m in self.monomials()) <= 1

    def divides(self, other: DPolynomial) -> bool:
        pself, pother = self.parent().as_polynomials(self, other)
        return pself.divides(pother)

    ###################################################################################
    ### Getter methods
    ###################################################################################
    @cached_method
    def monomials(self, *gens : DMonomialGen) -> tuple[DMonomial]:
        r'''
            Method to get a tuple of the monomials appearing in ``self``.

            If any generator is provided, then we return the monomials of ``self`` considering the ``gens`` and the main variables.
            This means, if `S = R\{u_1,u_2,u_3\}` and ``gens = u_2, u_3``, then we consider ``self`` as an element in 
            `R\{u_1\}\{u_2,u_3\}` and return the monomials in this case.
        '''
        if len(gens) == 0:
            return tuple(self._content.keys())
        
        ## We check the consistency of the arguments
        gens = [self.parent().gen(v) if isinstance(v, str) else v for v in gens]
        if any(v not in self.parent().gens() for v in gens):
            raise ValueError(f"The variables must be part of the parent ring: got {gens}, expected {self.parent().gens()}")
        
        if len(gens) == self.parent().ngens():
            return self.monomials()
        else:
            result = set()
            for m in self.monomials():
                collected = dict()
                for ((v, o), d) in m._variables.items():
                    if any(g._index == v for g in gens):
                        collected[(v,o)] = d
                nm = self.parent().monoids()(collected)
                result.add(nm)
            
            return tuple(sorted(result))

    @cached_method
    def coefficients(self, *gens: DMonomialGen) -> tuple[Element]:
        r'''
            Return a list of elements in the ``self.parent().base()`` of the coefficients.

            If any generator is provided, then we return the monomials of ``self`` considering the ``gens`` and the main variables.
            This means, if `S = R\{u_1,u_2,u_3\}` and ``gens = u_2, u_3``, then we consider ``self`` as an element in 
            `R\{u_1\}\{u_2,u_3\}` and return the monomials in this case.
        '''
        if len(gens) == 0:
            return tuple([self._content[m] for m in self.monomials()])
        else:
            return tuple([self.coefficient_full(m).constant_coefficient(*gens) for m in self.monomials(*gens)])
        
    def coefficient(self, monomial: DMonomial, *gens: DMonomialGen) -> Element:
        r'''
            Getter for the coefficient structure for a given monomial

            If any generator is provided, then we return the monomials of ``self`` considering the ``gens`` and the main variables.
            This means, if `S = R\{u_1,u_2,u_3\}` and ``gens = u_2, u_3``, then we consider ``self`` as an element in 
            `R\{u_1\}\{u_2,u_3\}` and return the monomials in this case.
        '''
        if not isinstance(monomial, DMonomial):
            monomial = self.parent().monoids()(monomial)
        if len(gens) == 0:
            return self._content.get(monomial, self.parent().base().zero())
        else:
            # We check the monomial
            if any(all(v[0] != g._index for g in gens) for v in monomial._variables):
                raise ValueError(f"Requested monomial {monomial} when working only with variables {gens}")
            monoms = self.monomials(*gens)
            coeffs = self.coefficients(*gens)
            
            if monomial in monoms:
                return coeffs[monoms.index(monomial)]
            else:
                return self.parent().zero()            

    def coefficient_full(self, monomial: DMonomial) -> DPolynomial:
        r'''Getter for the polynomial of all the elements for which ``monomial`` is part of the monomial'''
        if isinstance(monomial, DPolynomial):
            if not monomial.is_monomial():
                raise TypeError(f"If requested with d-polynomial, it must be a monomial")
            monomial = monomial.monomials()[0]

        output = dict()
        for (m,c) in self._content.items():
            if all(m._variables.get(v, -1) == monomial._variables.get(v) for v in monomial._variables):
                output[self.parent().monoids()({v: e for (v,e) in m._variables.items() if (v not in monomial._variables)})] = c
        if len(output) == 0:
            return self.parent().zero()
        return self.parent().element_class(self.parent(), output)

    def constant_coefficient(self, *gens) -> Element: #: Method to get the coefficient without variables
        r'''
            Method to get the constant coefficient of a :class:`DPolynomial`.

            This method allows to obtain the constant coefficient of a d-polynomial, i.e., that coefficient
            that do not contain any of the d-variables of the ring.

            As we can only build d-rings in the form `R\{u_1,\ldots,u_n\}` this method allows to specify
            a set of d-variables to interpret the element as an element of `R\{u_1,\ldots,u_k\}\{u_{k+1},\ldots,u_n\}`
            (see method :func:`coefficients` or :func:`monomials`).

            INPUT:

            * ``gens``: a sequence of :class:`DMonomialGen` indicating the outer d-variables of the ring.

            OUTPUT:

            The corresponding constant coefficient in the corresponding d-ring.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: R.<u,v> = DPolynomialRing(B)
                sage: P = (3*x -1)*u[0]*v[0] + x^2*v[1]*u[0] + u[2] + 1
                sage: Q = 7*x*v[0] + x^2*v[0]*u[1]
                sage: P.constant_coefficient()
                1
                sage: P.constant_coefficient(u,v)
                1
                sage: P.constant_coefficient(u)
                1
                sage: P.constant_coefficient(v)
                1 + u_2
                sage: Q.constant_coefficient(u)
                (7*x)*v_0
                sage: Q.constant_coefficient(v)
                0
        '''
        if len(gens) == 1 and isinstance(gens[0], (list,tuple)):
            gens = gens[0]
        if len(gens) == 0:
            return self.coefficient(())

        output = dict()
        for (m,c) in self._content.items():
            if all(all(v._index != el[0] for el in m._variables) for v in gens):
                output[m] = c

        if len(output) == 0:
            return self.parent().zero()
        return self.parent().element_class(self.parent(), output)
    
    def coefficient_without_var(self, *vars: DPolynomial) -> DPolynomial:
        r'''
            Method to compute the part of a d-polynomial without specific sets of algebraic variables.

            This method is similar to :func:`constant_coefficient` but in this case we consider the d-polynomial
            as an usual polynomial and we compute the coefficient without some algebraic variables (instead of 
            complete appearances of d-variables).

            INPUT:

            * ``vars``: variables that we are going to remove from ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: R.<u,v> = DPolynomialRing(B)
                sage: P = (3*x -1)*u[0]*v[0] + x^2*v[1]*u[0] + u[2] + 1
                sage: Q = 7*x*v[0] + x^2*v[0]*u[1]
                sage: P.coefficient_without_var([u[i] for i in range(P.order(u)+1)]) == P.constant_coefficient(u)
                True
                sage: P.coefficient_without_var(u[2])
                1 + (3*x - 1)*u_0*v_0 + x^2*u_0*v_1
                sage: P.coefficient_without_var(v[0], v[1])
                1 + u_2
                sage: P.coefficient_without_var(v[0])
                1 + x^2*u_0*v_1 + u_2
                sage: Q.coefficient_without_var(u[0]) == Q
                True
                sage: Q.coefficient_without_var(v[0])
                0
                sage: P.coefficient_without_var() == P
                True
        '''
        if len(vars) == 1 and isinstance(vars[0], (list,tuple)):
            vars = vars[0]
        if len(vars) == 0:
            return self
        if any(not v.is_variable() for v in vars):
            raise ValueError(f"Requested constant coefficient w.r.t. something that is not a variable")
        
        gens = [v.infinite_variables()[0] for v in vars]
        vars = [(gens[i]._index, gens[i].index(v, True)) for i,v in enumerate(vars)]

        output = dict()

        for (m,c) in self._content.items():
            if all(all(v != el for el in m._variables) for v in vars):
                output[m] = c

        if len(output) == 0:
            return self.parent().zero()
        return self.parent().element_class(self.parent(), output)

            

    @cached_method
    def orders(self, operation: int = -1) -> tuple[int]:
        r'''
            Method that gets the order of a polynomial in all its variables.

            This method computes the order of a concrete polynomial in all the
            variables that appear in its parent. This method relies on the method
            :func:`~dalgebra.dpolynomial.dpolynomial.DPolynomialRing_Monoid.gens`
            and the method :func:`~DMonomialGen.index`.

            INPUT:

            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            A tuple of integers where the index `i` is the order of ``self`` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates that variable does not show up in the polynomial.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.orders()
                (2, 0)
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.orders()
                (1, 2)
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.orders()
                (-1, 10)
                sage: R.one().orders()
                (-1, -1)
        '''
        output = [-1 for _ in range(self.parent().ngens())] # creating the basic orders for each variable
        for m in self.monomials():
            for (v,o) in m._variables:
                output[v] = max(output[v], o[operation] if operation != -1 else sum(o))
        return tuple(output)

    @cached_method
    def order(self, gen: DMonomialGen = None, operation: int = -1) -> int:
        r'''
            Method to obtain the order of a polynomial w.r.t. a variable

            This method computes the order of a polynomial with respect to
            a particular variable. Such variable has to be provided as a generator of
            the ring of polynomials (see :class:`DMonomialGen`).

            This method uses the method :func:`orders` as a basic definition of these orders.

            In the case the polynomial only has one differential variable, the input ``gen``
            can be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`DMonomialGen` in the parent ring.
            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            An integer representing the order of ``self`` with respect with the differential variable ``gen``

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.order(u)
                2
                sage: f1.order(v)
                0
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.order(u)
                1
                sage: f2.order(v)
                2
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.order(u)
                -1
                sage: f3.order(v)
                10
                sage: R.one().order(u)
                -1
                sage: R.one().order(v)
                -1
        '''
        if (gen is None) and self.parent().ngens() == 1:
            gen = self.parent().gens()[0]
        if gen is None:
            raise TypeError("The variable has to be provided")

        return self.orders(operation)[gen._index]

    @cached_method
    def lorders(self, operation: int = -1) -> tuple[int]:
        r'''
            Method that gets the order of a polynomial in all its variables.

            This method computes the lowest appearing order of a concrete polynomial in all the
            variables that appear in its parent. This method relies on the method
            :func:`~dalgebra.dpolynomial.dpolynomial.DPolynomialRing_Monoid.gens`
            and the method :func:`~DMonomialGen.index`.

            INPUT:

            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            A tuple of integers where the index `i` is the lowest order of ``self`` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates that variable does not show up in the polynomial..

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.lorders()
                (0, 0)
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.lorders()
                (1, 1)
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.lorders()
                (-1, 0)
                sage: R.one().lorders()
                (-1, -1)
        '''
        output = list(self.orders()) # creating the basic orders for each variable
        for m in self.monomials():
            for (v,o) in m._variables:
                output[v] = min(output[v], o[operation] if operation != -1 else sum(o))
        return tuple(output)

    @cached_method
    def lorder(self, gen: DMonomialGen = None, operation: int = -1) -> int:
        r'''
            Method to obtain the minimal order of a polynomial w.r.t. a variable

            This method computes the minimal order of a polynomial with respect to
            a particular variable. Such variable has to be provided as a generator of
            the ring of polynomials (see :class:`DMonomialGen`).

            This method uses the method :func:`lorders` as a basic definition of these orders.

            In the case the polynomial only has one variable, the input ``gen``
            may be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`DMonomialGen` in the parent ring.
            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            An integer representing the minimal order appearing in ``self`` with respect with the variable ``gen``
            or `-1` if the variable does not appear.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.lorder(u)
                0
                sage: f1.lorder(v)
                0
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.lorder(u)
                1
                sage: f2.lorder(v)
                1
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.lorder(u)
                -1
                sage: f3.lorder(v)
                0
                sage: R.one().lorder(u)
                -1
                sage: R.one().lorder(v)
                -1
        '''
        if (gen is None) and self.parent().ngens() == 1:
            gen = self.parent().gens()[0]
        if gen is None:
            raise TypeError("The variable has to be provided")

        return self.lorders(operation)[gen._index]

    def degree(self, x=None) -> int:
        if x is None: # general degree is computed
            return max(m.degree() for m in self._content)

        x : DPolynomial = self.parent()(x)
        if not x.is_variable():
            raise ValueError("Impossible to get degree w.r.t. a non-variable element")
        return max(m.degree(next(iter(x._content))) for m in self._content)

    @cached_method
    def variables(self) -> tuple[DPolynomial]: #: Get variables appearing in a polynomial (i.e., monomials of degree 1)
        union: set[DMonomial] = set()
        for m in self._content:
            union.update(m.variables())

        result: list[DPolynomial] = []
        for v in union:
            # Since it is a variable, we can get the index and order
            (i,o) = next(iter(v._variables))
            result.append(self.parent().gens()[i][o])
        return tuple(result)

    @cached_method
    def infinite_variables(self) -> tuple[DPolynomialGen]:
        r'''
            Method to compute which generators of the parent appear in ``self``.
        '''
        return tuple(g for g in self.parent().gens() if self.order(g) != -1)

    ###################################################################################
    ## Operation as polynomial
    ###################################################################################
    @cached_method
    def as_polynomial(self) -> Element:
        return self.parent().as_polynomials(self)[0]

    def as_linear_operator(self) -> Element:
        return self.parent().as_linear_operator(self)

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: DPolynomial) -> DPolynomial:
        keys = set(self._content.keys()).union(other._content.keys())
        return self.parent().element_class(self.parent(), {m : self._content.get(m,self.parent().base().zero()) + other._content.get(m,self.parent().base().zero()) for m in keys})
    def __neg__(self) -> DPolynomial:
        return self.parent().element_class(self.parent(), {m : -c for (m,c) in self._content.items()})
    def _sub_(self, other: DPolynomial) -> DPolynomial:
        return self + (-other)
    def _mul_(self, other: DPolynomial) -> DPolynomial:
        output = dict()
        for (ms, mo) in product(self.monomials(), other.monomials()):
            m = ms*mo
            output[m] = output.get(m, self.parent().base().zero()) + self._content[ms]*other._content[mo]
        return self.parent().element_class(self.parent(), output)
    def __truediv__(self, other: Element) -> DPolynomial:
        if other in self.parent().base():
            other = self.parent().base()(other)
            return self.parent().element_class(self.parent(), {m : c/other for (m,c) in self._content.items()})
        return super().__truediv__(other)
    def _floordiv_(self, _: DPolynomial) -> DPolynomial:
        return NotImplemented
    @cached_method
    def __pow__(self, power: int) -> DPolynomial:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            raise NotImplementedError("Negative powers not allowed")
        else:
            a,A = (self**(power//2 + power % 2), self**(power//2))
            return a*A

    def __eq__(self, other) -> bool:
        if isinstance(other, DMonomial):
            return self == self.parent()(other)
        elif isinstance(other, DPolynomial):
            # Trying a faster comparison
            if set(self.monomials()) == set(other.monomials()) and all(self.coefficient(m) == other.coefficient(m) for m in self.monomials()):
                return True
        return super().__eq__(other)
    def __ne__(self, other) -> bool:
        return not self == other

    def __hash__(self) -> int:
        r'''
            Hash function for DPolynomials.

            We use the sum of hash functions for each monomial appearing. This implies that the polynomial with only one monomial has the same hash as
            that monomial, meaning that having equality between polynomials and monomials implies same hash function.
        '''
        return sum(hash(m) for m in self.monomials())

    def numerator(self) -> DPolynomial:
        return self
    def denominator(self) -> DPolynomial:
        return self.parent().one()

    ###################################################################################
    ### Operational operations
    ###################################################################################
    def eval_coefficients(self, *args, **kwds):
        return self.parent().element_class(self.parent(), {t : c(*args, **kwds) for (t,c) in self._content.items()})

    def eval(self, *args, dic : dict = None, **kwds):
        r'''
            Evaluating a DMonomial

            We rely on the variable names of the parent. There are no coercions in this method, it simply computes the corresponding product
            with the corresponding values.
        '''
        if len(args) != 0:
            if dic is not None or len(kwds) != 0:
                raise TypeError("Incorrect format for evaluating a DMonomial")
            kwds.update({self.parent().variable_names()[i] : args[i] for i in range(len(args))})
        elif dic is not None:
            if not isinstance(dic, dict):
                raise TypeError("Invalid type for dictionary evaluating DMonomial")
            kwds.update({v.variable_name() if isinstance(v, DMonomialGen) else str(v) : val for (v,val) in dic.items()})

        ###########################################################
        ## Evaluating coefficients first
        ###########################################################
        inner_kwds = dict()
        out_kwds = dict()
        for entry, value in kwds.items():
            if entry not in self.parent().variable_names():
                inner_kwds[entry] = value
            else:
                out_kwds[entry] = value
        kwds = out_kwds

        if len(inner_kwds) > 0: # Evaluating coefficients -> this forces everything to remain in the same base ring
            return self.eval_coefficients(**inner_kwds)(**kwds)

        if len(kwds) > 0:
            ## Computing the final ring
            from functools import reduce
            final_base = reduce(pushout,
                                (el.parent() if not is_DPolynomialRing(el.parent()) else el.parent().base()
                                    for el in kwds.values()),
                                self.parent().base())
            R_w_kwds = self.parent().remove_variables(*list(kwds.keys())) # conversion from self.parent() to R_w_kwds is created
            final_dvariables = set(R_w_kwds.variable_names()) if is_DPolynomialRing(R_w_kwds) else set()
            for value in kwds.values():
                if is_DPolynomialRing(value.parent()):
                    final_dvariables.update(value.parent().variable_names())
            if len(final_dvariables) > 0 and is_DPolynomialRing(R_w_kwds):
                output_ring = DPolynomialRing(final_base, list(final_dvariables))
                self_to_output = DPolynomialVariableMorphism(R_w_kwds, output_ring) * R_w_kwds.convert_map_from(self.parent())
            elif len(final_dvariables) > 0:
                output_ring = DPolynomialRing(final_base, list(final_dvariables))
                self_to_output = output_ring.coerce_map_from(R_w_kwds) * R_w_kwds.convert_map_from(self.parent())
            else:
                output_ring = final_base
                self_to_output = output_ring.coerce_map_from(R_w_kwds) * R_w_kwds.convert_map_from(self.parent())

            ## Changing names to integers
            kwds = {
                self.parent().variable_names().index(k) :
                    DPolynomialVariableMorphism(v.parent(), output_ring)(v) if is_DPolynomialRing(v.parent()) else
                    final_base(v)
                for (k,v) in kwds.items()}

            result = output_ring.zero()
            for (m, c) in self._content.items():
                ## Evaluating the monomial
                ev_mon = final_base.one() # ev_mon will be in final_base or output_ring
                rem_mon = dict() # rem_mon will be in output_ring using ``self_to_output``
                for (v,o),e in m._variables.items():
                    if v in kwds:
                        el = kwds[v]
                        P = el.parent()
                        ev_mon *= P.apply_operations(el, o)**e
                    else:
                        rem_mon[(v,o)] = m._variables[(v,o)]
                rem_mon = self.parent()(self.parent().monoids().element_class(self.parent().monoids(), rem_mon)) if len(rem_mon) > 0 else self.parent().one()
                result += self_to_output(rem_mon) * final_base(c) * ev_mon
            return result
        else: # Nothing to evaluate -> we return the object
            return self

    def lie_bracket(self, other: DPolynomial, gen: DMonomialGen = None) -> DPolynomial:
        r'''
            Computes the Lie-bracket (or commutator) of ``self`` with other :Class:`DPolynomial`.
        '''
        if other not in self.parent():
            raise ValueError(f"The two objects must be DPolynomials")
        other = self.parent()(other)

        if isinstance(gen, DMonomialGen):
            name_gen = self.parent().variable_names()[gen._index]
        elif gen in ZZ:
            name_gen = self.parent().variable_names()[gen]
        elif isinstance(gen, str):
            name_gen = gen
        else:
            raise TypeError("Incorrect generator for Lie bracket")

        return self(**{name_gen: other}) - other(**{name_gen: self})

    @cached_method
    def sym_power(self, power: int, gen: DMonomialGen = None) -> DPolynomial:
        r'''
            Computes the symmetric power of an operator.

            Given a `d`-polynomial, we can consider two different products:

            * The algebraic product of `d`-polynomials.
            * The operational composition (where `A\circ B \equiv A(z=B)` for `z` the `d`-variable.

            This second multiplication is, generally, not commutative. However, when the Lie-bracket
            between two `d`-polynomial vanishes (i.e., `[A,B] = A\circ B - B\circ A = 0`), this product
            is commutative.

            In particular, a `d`-polynomial **always** commutes with itself. Hence, we can compute the power
            of the `d`-polynomial in any order. This power is called "symmetric power".

            INPUT:

            * ``power``: the power we want to compute.
            * ``gen``: the generator that will be substituted. If not given, we will take the first generator of the parent.
        '''
        gen = gen if gen is not None else self.parent().gens()[0]
        power = int(power)
        if power == 0:
            return gen[0]
        elif power == 1:
            return self
        else:
            H1 = self.sym_power(power//2 + power % 2, gen)
            H2 = self.sym_power(power//2, gen)

            ngen = gen.variable_name()
            return H1(**{ngen: H2})

    ###################################################################################
    ### Sylvester methods
    ###################################################################################
    def sylvester_resultant(self, other : DPolynomial, gen: DMonomialGen = None) -> DPolynomial:
        r'''
            Method on an element to compute (if possible) the Sylvester resultant.

            See :func:`~.dpolynomial.DPolynomialRing_Monoid.sylvester_resultant` for further information.
        '''
        return self.parent().sylvester_resultant(self, other, gen)

    def sylvester_matrix(self, other: DPolynomial, gen: DMonomialGen = None, k: int = 0) -> DPolynomial:
        r'''
            Method to compute the Sylvester `k`-matrix for two operator polynomials.

            See :func:`~.dpolynomial.DPolynomialRing_Monoid.sylvester_matrix` for further information.
        '''
        return self.parent().sylvester_matrix(self, other, gen, k)

    ###################################################################################
    ### Solving methods
    ###################################################################################
    def solve(self, gen: DMonomialGen) -> Element:
        r'''
            Finds (if possible) a solution of ``gen`` using ``self == 0``.

            This method tries to solve the equation `p(u) = 0` where `p \in R\{u\}` is a :class:`DPolynomial`
            for a given infinite variable `u`. This means, this method will compute an element `y \in R` such that
            `p(y) = 0` where `p(u)` is represented by ``self``.

            Currently, the only possibility that is implemented is when we can rewrite the polynomial `p(u)` to the
            form `p(u) = u^{(d)} + \alpha` where `\alpha \in R`. Then we try to invert the operation `d` times to `\alpha`
            (see method :func:`inverse_operation`).

            INPUT:

            * ``gen``: the generator in ``self.parent()`` that will be used as main variable (i.e., `u`).

            OUTPUT:

            An element ``e`` in ``self.parent()`` such that ``self(gen=e) == 0`` is True.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DPolynomialRing(DifferentialRing(QQ, lambda p:0))
                sage: p = u[0] - v[1]
                sage: p.solve(u)
                v_1
                sage: p.solve(v)
                Traceback (most recent call last):
                ...
                ValueError: [inverse_derivation] Found an element impossible to invert: u_0
                sage: p = u[1] - 2*v[0]*v[1]
                sage: p.solve(u)
                v_0^2
                sage: p(u=p.solve(u))
                0

        '''
        if self.parent().noperators() > 1:
            raise NotImplementedError("[solve] Method implemented only for 1 operator.")

        appearances = len([v for v in self.variables() if v in gen])
        if appearances == 0:
            raise ValueError(f"[solve] The variable {gen.variable_name()} does not appear in {self}")
        elif appearances > 1:
            raise NotImplementedError(f"[solve] The variable {gen.variable_name()} appear with different orders in {self}")

        coeff = self.coefficient(gen[self.order(gen)])
        rem = -self + coeff*gen[self.order(gen)] # we know ``gen`` do not show up in rem
        return (rem/coeff).inverse_operation(0, times=self.order(gen)) # the division is with coefficient only

    ###################################################################################
    ### Weight methods
    ###################################################################################
    def weight(self, weight=None):
        r'''
            Computes the weight of a d-polynomial.

            This method computes the weight of a d-polynomial for a given weight function. These
            weight functions can be given as an actual :class:`~dalgebra.dpolynomial.dpolynomial.WeightFunction`
            or the same arguments as this class have.
        '''
        if not isinstance(weight, WeightFunction):
            weight = self.parent().weight_func(*weight)

        return weight(self)

    def is_homogeneous(self, weight=None):
        r'''
            Checks whether a d-polynomial is homogeneous. If a weight is given, this will be used for homogeneous.
        '''
        if weight is None:
            return self.as_polynomial().is_homogeneous()

        if not isinstance(weight, WeightFunction):
            weight = self.parent().weight_func(*weight)

        return weight.is_homogeneous(self)

    ###################################################################################
    ### Ranking methods
    ###################################################################################
    def monic(self, ranking: RankingFunction = None):
        r'''Method to get the monic polynomial w.r.t. a ranking'''
        ranking = self.parent().ranking() if ranking is None else ranking
        return ranking.monic(self)

    def leader(self, ranking: RankingFunction = None):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        ranking = self.parent().ranking() if ranking is None else ranking
        return ranking.leader(self)

    def rank(self, ranking: RankingFunction = None):
        r'''
            Gets the rank of ``self`` w.r.t. a ranking.
        '''
        ranking = self.parent().ranking() if ranking is None else ranking
        return ranking.rank(self)

    def initial(self, ranking: RankingFunction = None):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        ranking = self.parent().ranking() if ranking is None else ranking
        return ranking.initial(self)

    def separant(self, ranking: RankingFunction = None):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        ranking = self.parent().ranking() if ranking is None else ranking
        return ranking.separant(self)

    ### Some aliases
    lc = initial #: alias for initial (also called "leading coefficient")

    ###################################################################################
    ### Other magic methods
    ###################################################################################
    @cached_method
    def __repr__(self) -> str:
        if self.is_zero():
            return "0"
        parts = []
        for (m,c) in sorted(self._content.items(), key=lambda p : p[0]):
            if str(c)[0] == "-": # changing sign
                sign = "-"
                c = -c
            else:
                sign = "+"

            par = any(char in str(c) for char in ("+", "*", "-"))

            if m.is_one():
                parts.append((sign, "", f"{'(' if par else ''}{c}{')' if par else ''}"))
            elif c == 1:
                parts.append((sign, f"{m}", ""))
            else:
                parts.append((sign, f"{m}", f"{'(' if par else ''}{c}{')' if par else ''}*"))

        output = f"{parts[0][0] if parts[0][0] == '-' else ''}{parts[0][2]}{parts[0][1]}"
        for (sign, m, c) in parts[1:]:
            output += f" {sign} {c}{m}"
        return output

    def _latex_(self) -> str:
        if self.is_zero():
            return "0"
        parts = []
        for (m,c) in sorted(self._content.items(), key=lambda p : p[0]):
            if str(c)[0] == "-": # changing sign
                sign = "-"
                c = -c
            else:
                sign = "+"

            par = any(char in str(c) for char in ("+", "*", "-"))

            if m.is_one():
                parts.append((sign, "", f"\\left({latex(c)}\\right)"))
            elif c == 1:
                parts.append((sign, latex(m), ""))
            else:
                parts.append((sign, latex(m), f"\\left({latex(c)}\\right)"))

        output = f"{parts[0][0] if parts[0][0] == '-' else ''}{parts[0][2]}{parts[0][1]}"
        for (sign, m, c) in parts[1:]:
            output += f" {sign} {c}{m}"
        return output

    def _maple_(self, gen: DMonomialGen | str, maple_var: str = "t", maple_diff: str = None) -> str:
        r'''
            Method to convert the polynomial into a differential polynomial in Maple.

            This method requires a d-variable as input to determine which is the operator variable.

            INPUT:

            * ``gen``: variable to be used as an operator variable. If the polynomial is not linear in this variable, an error is
              raised. It can be also the name of a d-variable in ``self.parent()``.
            * ``maple_var``: the name that the independent variable will take. This is the variable over which we differentiate.
            * ``maple_diff``: name for the differential operator in Maple. If none is given, we will take the name of the d-variable
              given by ``gen``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: f1 = x*u[0]*v[1] + x^2*u[2]*v[2] + 3*x*v[2] - (1-x)*v[0]
                sage: f1._maple_(v) # correct behavior
                '(x - 1) + x*u(t)*v + ((3*x) + x^2*diff(u(t), t$2))*v^2'
                sage: f1._maple_(v, "x", "D") # changing ind. variable and diff. operator
                '(x - 1) + x*u(x)*D + ((3*x) + x^2*diff(u(x), x$2))*D^2'
                sage: f1._maple_(u) # Not homogeneous in u_*
                Traceback (most recent call last):
                ...
                TypeError: The given polynomial ... is not linear or homogeneous over u_*
                sage: f2 = x*u[0] + x^2*u[2] - (1-x)*v[0] # not homogeneous in v_*
                sage: f2._maple_(v)
                Traceback (most recent call last):
                ...
                TypeError: The given polynomial ... is not linear or homogeneous over v_*
                sage: f3 = x*u[0] + x^2*u[2] # variable v not appearing
                sage: f3._maple_("v", "x", "partial")
                'x*u(x) + x^2*diff(u(x), x$2)'
                sage: R.one()._maple_("u")
                '1'
                sage: R.zero()._maple_("u")
                '0'
                sage: S.<big,small> = DifferentialPolynomialRing(QQ)
                sage: f4 = big[0]*small[1] + 3*big[0]*small[3]^2 - big[1]*small[2]
                sage: f4._maple_(small) # not linear in small_*
                Traceback (most recent call last):
                ...
                TypeError: The given polynomial ... is not linear or homogeneous over small_*
                sage: f4._maple_(big) # correct
                '(diff(small(t), t$1) + 3*diff(small(t), t$3)^2) - diff(small(t), t$2)*big'
        '''
        if not isinstance(gen, DMonomialGen):
            gen = self.parent().gen(str(gen))
        if gen not in self.parent().gens():
            raise ValueError("The given variable must be a valid generator of the parent.")

        if self.is_zero():
            return r"0"

        if not self.is_linear([gen]) or any(self.parent()(m).order(gen) == -1 for m in self.monomials()):
            if self.order(gen) != -1:
                raise TypeError(f"The given polynomial ({self}) is not linear or homogeneous over {gen}")

        if maple_diff is None:
            maple_diff = gen.variable_name()

        coeffs = dict()
        mons = dict()
        if self.order(gen) != -1: # Normal case
            for i in range(self.order(gen)+1):
                c = self.coefficient_full(gen[i])
                if c != 0:
                    coeffs[i] = str(c) if len(c._content) == 1 else f"({c})" # we cast the coefficients to strings
        else: # special case for polynomials without the differential operator
            coeffs[0] = str(self)

        ## We transform the coefficients to fit the Maple format
        regex = r"(" + "|".join([el.variable_name() for el in self.infinite_variables()]) + r")_(\d+)"

        def subs_regex(M):
            var, order = M.groups()
            if order == '0':
                return var + f"({maple_var})"
            else:
                return f"diff({var}({maple_var}), {maple_var}${order})"

        import re
        for i in coeffs:
            coeffs[i] = re.sub(regex, subs_regex, coeffs[i])
            mons[i] = "" if i == 0 else maple_diff if i == 1 else f"{maple_diff}^{i}"

        ## We put everything together
        def mix_coeff_mon(coeff, mon):
            if coeff == "1" and mon == "":
                return "1"
            elif mon == "":
                return f"{coeff}"
            elif coeff == "1":
                return mon
            else:
                return f"{coeff}*{mon}"

        result = ""
        for to_add in (mix_coeff_mon(coeffs[i], mons[i]) for i in coeffs):
            to_add = to_add.strip() # Removing white-spaces
            if result == "": # first iteration
                result += to_add
            elif to_add[0] == "-":
                result += " - " + to_add[1:]
            else:
                result += " + " + to_add

        return result

    def __call__(self, *args, dic : dict = None, **kwds):
        return self.eval(*args, dic=dic, **kwds)


RWOPolynomial = DPolynomial #: alias for DPolynomial (used for backward compatibility)

class DPolynomialGen(DMonomialGen):
    r'''
        :class:`DPolynomial` version of the generator object :class:`DMonomialGen`. It guarantees the output is a :class:`DPolynomial`.
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, name: str, *, index: int = -1):
        super().__init__(parent.monoids(), name, index=index)
        self._poly_parent = parent

    def __getitem__(self, i: int | tuple[int]) -> DPolynomial:
        return self._poly_parent(super().__getitem__(i))

    ## Special arithmetic for these generators
    def __add__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] + x
    def __radd__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x + self[0]
    def __neg__(self):
        return -self[0]
    def __sub__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] - x
    def __rsub__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x - self[0]
    def __mul__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] * x
    def __rmul__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x * self[0]
    def __lmul__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] * x
    def __mod__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] % x
    def __rmod__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x % self[0]
    def __div__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] / x
    def __rdiv__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x / self[0]
    def __floordiv__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return self[0] // x
    def __rfloordiv__(self, x):
        if isinstance(x, DPolynomialGen):
            x = x[0]
        return x // self[0]
    def __pow__(self, n):
        return self[0]**n

class DPolynomialRing_Monoid(Parent):
    r'''
        Class for a ring of polynomials over a :class:`~dalgebra.dring.DRing`.

        Given a ring with an associated operators `(R, (d_1,...,d_n))`, where `d_i : R \rightarrow R`, we can
        always define the ring of polynomials on `y` as the *infinite polynomial ring*

        .. MATH::

            R[y_\sigma : \sigma \in \mathbb{N}^n]

        where the operations acts naturally (preserving all its properties) over this ring and,
        in particular, `d_i(y_\sigma) = y_{\sigma+e_i}` where `\e_i` is the `i`-th canonical vector
        of `\mathbb{N}^n` (i.e., all zeros but the `i`-th coordinate).

        This class represents exactly the ring of polynomials with these operator over the given ring ``base``
        with variables given in ``names``.

        This class inherits from :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse`,
        which is the Sage structure to manipulate polynomial rings over infinitely many variables.

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R` (has to be in the
          category :class:`RingsWithOperator`)
        * ``names``: set of names for the variables of the new ring.

        REMARK:

        The behavior of the operations with respect with the multiplication must be explicit (namely, they must
        all be ''homomorphism'', ''derivation'' or ''skew''). See documentation of :mod:`dalgebra.dring`
        for further information.

        EXAMPLES::

            sage: from dalgebra import *
            sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]; R
            Ring of operator polynomials in (y) over Differential Ring [[Univariate Polynomial Ring in x over Rational Field], (d/dx,)]
            sage: S.<a,b> = DifferentialPolynomialRing(ZZ); S
            Ring of operator polynomials in (a, b) over Differential Ring [[Integer Ring], (0,)]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: diff(y[1])
            y_2
            sage: diff(a[1]*b[0]) #Leibniz Rule
            a_1*b_1 + a_2*b_0

        Although the use of diff can work in these rings, it is not fully recommended because we may require more
        information for the ``diff`` method to work properly. We recommend the use of the ``derivative`` methods
        of the elements or the method ``derivative`` of the Rings (as indicated in the category
        :class:`dalgebra.dring.DRings`)::

            sage: R.derivative(y[0])
            y_1
            sage: R.derivative(x)
            1
            sage: R.derivative(x*y[10])
            y_10 + x*y_11
            sage: R.derivative(x^2*y[1]^2 - y[2]*y[1])
            (2*x^2)*y_1*y_2 - y_1*y_3 + (2*x)*y_1^2 - y_2^2
            sage: (x*y[10]).derivative()
            y_10 + x*y_11

        This derivation also works naturally with several infinite variables::

            sage: S.derivative(a[1] + b[0]*a[0])
            a_0*b_1 + a_1*b_0 + a_2
            sage: (a[3]*a[1]*b[0] - b[2]).derivative()
            a_1*a_3*b_1 + a_1*a_4*b_0 + a_2*a_3*b_0 - b_3

        At the same time, these rings also work with difference operators. This can be easily built
        using the method :func:`DifferencePolynomialRing` using a shift operator as the main
        operator to extend the ring::

            sage: R.<y> = DifferencePolynomialRing(QQ['x']); x = R.base().gens()[0]; R
            Ring of operator polynomials in (y) over Difference Ring [[Univariate Polynomial Ring in x over Rational Field], (Id,)]
            sage: S.<a,b> = DifferencePolynomialRing(ZZ); S
            Ring of operator polynomials in (a, b) over Difference Ring [[Integer Ring], (Id,)]

        And after this code we can start creating polynomials using the generators ``y``, ``a`` and ``b`` and, then
        compute their ``shift`` or ``difference`` as we did with the derivation::

            sage: y[1]
            y_1
            sage: y[1].difference()
            y_2
            sage: R.difference(x)
            x
            sage: R.difference(x*y[10])
            x*y_11
            sage: R.difference(x^2*y[1]^2 - y[2]*y[1])
            -y_2*y_3 + x^2*y_2^2

        This difference also works naturally with several infinite variables::

            sage: (a[1]*b[0]).difference()
            a_2*b_1
            sage: S.difference(a[1] + b[0]*a[0])
            a_1*b_1 + a_2

        We can see other type of shifts or differences operators::

            sage: X = QQ[x]('x'); shift = QQ[x].Hom(QQ[x])(X+1)
            sage: T.<z> = DifferencePolynomialRing(DifferenceRing(QQ[x], shift)); x = T.base().gens()[0]
            sage: T.difference(z[0])
            z_1
            sage: T.difference(x)
            (x + 1)
            sage: T.difference(x^2*z[1]^2 - z[2]*z[1])
            -z_2*z_3 + (x^2 + 2*x + 1)*z_2^2

        One of the main features of the category :class:`dalgebra.dring.DRings` is that
        several operators can be included in the ring. This class of operator rings also have such feature,
        extending all operators at once.

        In this case, the variables are display with a tuple as a sub-index, indicating how many times each
        operators has been applied to each of the infinite variables of the ring::

            sage: R.<x,y> = QQ[] # base ring
            sage: dx, dy = R.derivation_module().gens() # creating derivations
            sage: s = R.Hom(R)([x+1,y-1]) # creating the shift operator
            sage: dsR = DifferenceRing(DifferentialRing(R, dx, dy), s); dsR
            Ring [[Multivariate Polynomial Ring in x, y over Rational Field], (d/dx, d/dy, Hom({x: x + 1, y: y - 1}))]

        We can see that these three operators all commute::

            sage: dsR.all_operators_commute()
            True

        Hence, we can create the ring of operator polynomials with as many variables as we want::

            sage: OR.<u,v> = DPolynomialRing(dsR); OR
            Ring of operator polynomials in (u, v) over Ring [[Multivariate Polynomial Ring in
            x, y over Rational Field], (d/dx, d/dy, Hom({x: x + 1, y: y - 1}))]

        When we have several operators, we can create elements on the variables in two ways:

        * Using an index (as usual): then the corresponding variable will be created but following the order
          that is given by :class:`dalgebra.dpolynomial.dmonoids.IndexBijection`.
        * Using a tuple: have the standard meaning that each of the operators has been applied that amount of times.

        We can see these two approaches in place::

            sage: u[5]
            u_0_1_1
            sage: v[0,3,2]
            v_0_3_2
            sage: u[5].derivative(0)
            u_1_1_1
            sage: u[5].derivative(1, times=3)
            u_0_4_1
            sage: u[5].derivative(1, times=3).derivative(0, times=2).difference(times=1)
            u_2_4_2
            sage: (u[5]*v[0,1,0]).derivative(1)
            u_0_1_1*v_0_2_0 + u_0_2_1*v_0_1_0
            sage: (u[5]*v[0,1,0]).derivative(1) - u[0,1,0].shift()*v[0,2,0]
            u_0_2_1*v_0_1_0
    '''
    Element = DPolynomial

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Monoids.Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, names : Collection[str], category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        if not base.all_operators_commute():
            raise TypeError("Detected operators that do NOT commute. Impossible to build the DPolynomialRing_Monoid")

        if any(ttype == "none" for ttype in base.operator_types()):
            raise TypeError(f"All operators in {base} must be typed")

        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__operators : tuple[AdditiveMap] = tuple([
            self._create_operator(operation, ttype)
            for operation, ttype in enumerate(self.base().operator_types())
        ])
        self.__monoids = DMonomialMonoid(len(self.__operators), *names)
        self.__gens = tuple(DPolynomialGen(self, name, index=i) for (i,name) in enumerate(names))
        self.__cache : list[dict[DPolynomial, DPolynomial]] = [dict() for _ in range(len(self.__operators))]
        self.__cache_ranking : dict[tuple[tuple[DPolynomial], str], RankingFunction] = dict()
        self.__fraction_field : DFractionField = None

        # registering conversion to simpler structures
        current = self.base()
        morph = DPolynomialSimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DPolynomialSimpleMorphism(self, current)
            current.register_conversion(morph)

        ## Adding conversion to the monoids
        morph = DPolynomialSimpleMorphism(self, self.monoids())
        self.monoids().register_conversion(morph)

        try: # Trying to add conversion for the ring of linear operators
            operator_ring = self.linear_operator_ring()
            morph = DPolynomialToLinOperator(self)
            operator_ring.register_conversion(morph)
        except NotImplementedError:
            pass

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def monoids(self) -> DMonomialMonoid:
        return self.__monoids

    def variable_names(self) -> tuple[str]:
        return self.monoids().variable_names()

    def gens(self) -> tuple[DPolynomialGen]:
        return self.__gens

    @cached_method
    def gen(self, i: int | str = None):
        r'''
            Override method to create the `i^{th}` generator (see method
            :func:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse.gen`).

            For a :class:`DPolynomialRing_Monoid`, the generator type is
            :class:`~dalgebra.diff_polynomial.diff_polynomial_element.DMonomialGen`
            which provides extra features to know if an object can be generated by that generator.
            See tis documentation for further details.

            INPUT:

            * ``i``: index or name of the required generator.

            OUTPUT:

            A :class:`~dalgebra.diff_polynomial.diff_polynomial_element.DMonomialGen`
            representing the `i^{th}` generator of ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: from dalgebra.dpolynomial.dmonoids import DMonomialGen
                sage: R.<y> = DPolynomialRing(DifferentialRing(QQ['x'], diff))
                sage: R.gen(0)
                y_*
                sage: R.gen(0) is y
                True
                sage: isinstance(R.gen(0), DMonomialGen)
                True
                sage: S = DPolynomialRing(DifferentialRing(ZZ, lambda z : 0), ('a', 'b'))
                sage: S
                Ring of operator polynomials in (a, b) over Differential Ring [[Integer Ring], (0,)]
                sage: S.gen(0)
                a_*
                sage: S.gen(1)
                b_*

            This method also allow the name of the generator as input::

                sage: S.gen('a')
                a_*
                sage: S.gen('b')
                b_*
                sage: S.gen('t')
                Traceback (most recent call last):
                ...
                ValueError: tuple.index(x): x not in tuple
        '''
        if isinstance(i, str):
            i = self.variable_names().index(i)
        if(not(i in ZZ) or (i < 0 or i > len(self.variable_names()))):
            raise ValueError("Invalid index for generator")

        return self.gens()[i]

    def ngens(self) -> int:
        return self.monoids().ngens()

    ################################################################################
    ### MONOIDS.ALGEBRAS METHODS (from Monoids.Algebras.ParentMethods)
    ################################################################################
    def basis(self) -> LazyFamily:
        return LazyFamily(self.monoids().semigroup_generators().set, lambda i : self(self.monoids().semigroup_generators()[i]))

    @cached_method
    def one_basis(self) -> DMonomial:
        return (0, ())

    def term(self, index: DMonomial, coeff: Element = None):
        if not isinstance(index, DMonomial):
            try:
                index = self.monoids()(index)
            except TypeError:
                index = self.monoids().semigroup_generators()[index]
        return self.element_class(self, {index : coeff if coeff is not None else self.base().one()})

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S: Parent) -> bool:
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        if S == self.monoids():
            return True

        coer = self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))

    def _element_constructor_(self, x) -> DPolynomial:
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse`
            and then transforms the output into the corresponding type for ``self``.
        '''
        if x in self.monoids():
            return self.element_class(self, {self.monoids()(x): self.base().one()})
        elif x in self.base():
            return self.element_class(self, {self.monoids().one(): x}) # casting elements in self.base()
        elif isinstance(x, DPolynomial):
            return self.element_class(self, x) # this casts the coefficients
        else:
            ## Converting the input into a Symbolic Expression
            if isinstance(x, str) or x in SR:
                x = SR(x)

            variables = x.variables()

            ## Splitting variables into normal variables and other variables
            inner_variables, outer_variables, var_and_order = list(), list(), dict()
            for v in variables:
                for (i,g) in enumerate(self.gens()):
                    if v in g:
                        outer_variables.append(v)
                        var_and_order[v] = (i, g.index(v))
                        break
            else:
                inner_variables.append(v)

            ## We check the object is a polynomial in the outer variables
            if any(not x.is_polynomial(v) for v in outer_variables):
                raise ValueError(f"The input is not a polynomial: {x}")
            ## We check if the inner variables are in the base ring
            if any(v not in self.base() for v in inner_variables):
                raise ValueError(f"The input has coefficients that are not in base ring: {x}")
            ## Creating a polynomial out of the element
            PR = PolynomialRing(self.base(), outer_variables, sparse=True)
            x = x.polynomial(ring=PR)

            return self.element_class(self, {
                self.monomial(tuple((var_and_order[v], m.degree(v)) for v in m.variables())) : c
                for (c,m) in zip(x.coefficients(), x.monomials())
            })

    def _pushout_(self, other):
        if isinstance(other, DMonomialMonoid):
            if other.ngens() <= self.ngens():
                return self
            else: # more generators in other than in self
                return DPolyRingFunctor(tuple(v.variable_name() for v in other.gens()))(self.base())

        scons, sbase = self.construction()
        if isinstance(other, DPolynomialRing_Monoid):
            ocons, obase = other.construction()
            cons = scons.merge(ocons)
            try:
                base = pushout(sbase, obase)
            except TypeError:
                base = pushout(obase, sbase)
            return cons(base)
        return None

    def construction(self) -> tuple[DPolyRingFunctor, Ring]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DPolynomialRing_Monoid`, the associated functor class is :class:`DPolyRingFunctor`.
            See its documentation for further information.
        '''
        return DPolyRingFunctor(self.variable_names()), self.base()

    def flatten(self, polynomial : DPolynomial) -> Element:
        r'''
            Method to compute the flatten version of a polynomial.

            This method allows to compute a basic object where all variables appearing in the given ``polynomial``
            and all its base parents are at the same level. This is similar to the method :func:`flattening_morphism`
            from multivariate polynomials, but adapted to the case of infinite variable polynomials.

            Moreover, we need to take care of possible wrapping problems in the DRing category.

            INPUT:

            * ``polynomial``: an element in ``self`` to be flatten.

            OUTPUT:

            A multivariate polynomial with all the variables appearing in ``polynomial`` and all bases rings of ``self``
            at the same level.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: R.flatten(f1) # u_2*x^2 + u_0*x + v_0*x - v_0
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented
                sage: R.flatten(f1).parent() # Multivariate Polynomial Ring in u_2, u_1, u_0, v_2, v_1, v_0, x over Rational Field
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented

            This method works with more complicated ring with operators::

                sage: B.<x,ex,l,m,e> = QQ[]
                sage: dx,dex,dl,dm,de = B.derivation_module().gens()
                sage: shift = B.Hom(B)([x+1, e*ex, l, m, e])
                sage: DSB = DifferenceRing(DifferentialRing(B, dx + ex*dex), shift); x,ex,l,m,e = DSB.gens()
                sage: R.<u,v> = DPolynomialRing(DSB)
                sage: f1 = u[1,0]*ex + (l-1)*v[0,1]*x - m; f1
                -m + ex*u_1_0 + (x*l - x)*v_0_1
                sage: f1.as_polynomial()
                ex*u_1_0 + (x*l - x)*v_0_1 - m
                sage: f1.derivative()
                ex*u_1_0 + ex*u_2_0 + (l - 1)*v_0_1 + (x*l - x)*v_1_1
                sage: f1.derivative().as_polynomial()
                ex*u_1_0 + ex*u_2_0 + (l - 1)*v_0_1 + (x*l - x)*v_1_1
                sage: R.flatten(f1.derivative()) # v_4*x*l - v_4*x + u_5*ex + u_2*ex + v_1*l - v_1
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented
                sage: R.flatten(f1.derivative()).parent() # Multivariate Polynomial Ring in u_5, u_4, u_3, u_2, u_1, u_0, v_5, v_4, v_3, v_2, v_1, v_0, x, ex, l, m, e over Rational Field
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented

            We remark that we can reconstruct the original polynomial from the flattened version::

                sage: R(R.flatten(f1.derivative())) == f1.derivative() # True
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented
                sage: R(R.flatten(f1)) == f1 # True
                Traceback (most recent call last):
                ...
                NotImplementedError: This method is not yet implemented
        '''
    #     # we check that the input is in ``self``
    #     polynomial = self(polynomial)

    #     # we compute the destination ring for the polynomial
    #     variables = [*polynomial.polynomial().parent().gens()]
    #     current = self.base()
    #     while (
    #         isinstance(current, DRing_Wrapper) or
    #         is_PolynomialRing(current) or
    #         is_MPolynomialRing(current) or
    #         isinstance(current, InfinitePolynomialRing_dense) or
    #         isinstance(current, InfinitePolynomialRing_sparse)
    #     ):
    #         if is_PolynomialRing(current) or is_MPolynomialRing(current):
    #             variables.extend(current.gens())
    #         elif isinstance(current, InfinitePolynomialRing_dense) or isinstance(current, InfinitePolynomialRing_sparse):
    #             variables.extend(reduce(lambda p, q : pushout(p,q), [c.polynomial().parent() for c in polynomial.polynomial().coefficients()]).gens())

    #         if isinstance(current, DRing_Wrapper):
    #             current = current.wrapped
    #         else:
    #             current = current.base()

    #     # at this state we have a "current" that can not be extracted further and a list of variables
    #     destiny_ring = PolynomialRing(current, variables)
    #     return destiny_ring(str(polynomial.polynomial()))
        raise NotImplementedError("This method is not yet implemented")

    def change_ring(self, R):
        r'''
            Return the operator polynomial ring changing the base ring to `R`.

            We will keep the name of the variables of ``self`` but now will take coefficients
            over `R` and the operations will be those on `R`.

            INPUT:

            * ``R``: a Ring with Operators.

            OUTPUT:

            A :class:`DPolynomialRing_Monoid` over ``R`` with the same variables as ``self``.
        '''
        return DPolynomialRing(R, *self.variable_names())

    def append_variables(self, *variables) -> DPolynomialRing_Monoid:
        r'''Add new d-variables to the current ring'''
        F,B = self.construction()
        new_ring = F.append_variables(*variables)(B)

        ## We add the conversion method
        try:
            self.register_conversion(DPolynomialSimpleMorphism(new_ring, self))
            new_ring.register_coercion(DPolynomialVariableMorphism(self, new_ring))
        except AssertionError: # already called with these arguments
            pass

        return new_ring

    def remove_variables(self, *variables: str | DMonomialGen) -> DPolynomialRing_Monoid:
        r'''
            Method that removes d-variables from the ring of d-polynomials and guarantees the conversion between structures.
            If all variables are removed, we return the base d-ring.

            INPUT:

            * ``variables``: list of names to be removed. If any name is not is ``self``, we ignore it.

            EXAMPLES::

                sage: from dalgebra.dring import *
                sage: from dalgebra.dpolynomial.dpolynomial import *
                sage: R.<a,b,c> = DPolynomialRing(DifferentialRing(QQ))
                sage: Ra = R.remove_variables("b", c)
                sage: Ra
                Ring of operator polynomials in (a) over Differential Ring [[Rational Field], (0,)]
                sage: p = a[2]*b[0] - c[1]^2
                sage: Ra(p)
                Traceback (most recent call last):
                ...
                ValueError: Impossible to convert element a_2*b_0 - c_1^2 from ...
                sage: pp = a[3] + 3*a[2] + 3*a[1] + a[0]
                sage: Ra(pp)
                a_0 + 3*a_1 + 3*a_2 + a_3
                sage: R(Ra(pp)) == pp
                True
        '''
        variables = set([v._name if isinstance(v, DMonomialGen) else str(v) for v in variables])
        rem_variables = [v_name for v_name in self.variable_names() if (v_name not in variables)]
        if len(rem_variables) == 0: # all removed
            return self.base()
        elif len(rem_variables) == self.ngens(): # nothing removed
            return self
        else: # some intermediate ring
            ## We create the new ring
            output = DPolynomialRing(self.base(), rem_variables)
            ## We guarantee the conversion/coercion between structures
            try:
                self.register_coercion(DPolynomialVariableMorphism(output, self))
                output.register_conversion(DPolynomialSimpleMorphism(self, output))
            except AssertionError:
                pass

            return output

    def fraction_field(self):
        try:
            if self.is_field():
                return self
        except NotImplementedError:
            pass

        if self.__fraction_field is None:
            self.__fraction_field = DFractionField(self)
        return self.__fraction_field

    #################################################
    ### Magic python methods
    #################################################
    def __contains__(self, x):
        if x in self.monoids():
            return True
        return super().__contains__(x)
    
    ## Other magic methods
    def __repr__(self):
        return f"Ring of operator polynomials in ({', '.join(self.variable_names())}) over {self.base()}"

    def _latex_(self):
        return latex(self.base()) + r"\{" + ", ".join(self.variable_names()) + r"\}"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        deg_bound : int = 0,order_bound : int = 0,
        *args,**kwds
    ):
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
        deg_bound = 0 if ((deg_bound not in ZZ) or deg_bound < 0) else deg_bound
        order_bound = 0 if ((order_bound not in ZZ) or order_bound < 0) else order_bound

        gens_for_poly = [g[el] for g in self.gens() for el in IndexBijection(self.noperators()).iter(order_bound)]
        poly_ring = PolynomialRing(self.base(), gens_for_poly)
        p = poly_ring.random_element(deg_bound, *args, **kwds)

        return self(p)

    def as_polynomials(self, *elements : DPolynomial) -> list[Element]:
        r'''
            Transform the list of elements to polynomials in a common parent

            This method converts the ``elements`` in ``self`` to plain polynomials without any
            differential structure behind. The variables used for the polynomial ring are only
            those that actively appear in some of the elements.

            Currently, there is no guarantee that the conversion back works effectively.

            INPUT:

                * ``elements``: a list of :class:`DPolynomial` to be converted into a polynomial list.

            OUTPUT:

            A list of polynomials in SageMath (in sparse form) only involving the variables that appear
            in the ``elements``.

            EXAMPLES::

                sage: from dalgebra.dring import *
                sage: from dalgebra.dpolynomial.dpolynomial import *
                sage: R.<a_1,a_2,c> = DPolynomialRing(DifferentialRing(QQ))
                sage: p = a_1[2]*a_2[1] - c[3]
                sage: q = 3*a_1[2] - c[2]*a_2[0]
                sage: pp, qq = R.as_polynomials(p,q)
                sage: pp.parent()
                Multivariate Polynomial Ring in a_1_2, a_2_0, a_2_1, c_2, c_3 over Differential Ring [[Rational Field], (0,)]
                sage: qq
                -a_2_0*c_2 + 3*a_1_2

        '''
        variables = set()
        for element in elements:
            variables.update(self(element).variables())
        # This sort the variables first by index (i.e., alphabetically) then by order
        variables = sorted(variables, key=lambda p : tuple(next(iter(p._content))._variables.items())[0])

        PR = PolynomialRing(self.base(), [str(v) for v in variables], sparse=True)
        try:
            self.register_coercion(PR.hom(variables, self))
        except AssertionError:
            pass # coercion already registered
        result = [PR(str(element)) for element in elements] # TODO: This may be improved?

        return result

    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[Morphism]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def _create_operator(self, operation: int, ttype: str) -> AdditiveMap:
        r'''
            Method to create a map on the ring of polynomials from an operator on the base ring.

            We create an :class:`AdditiveMap` from the given operator assuming the type given in ``ttype``.
            This type will determine how the multiplication behaves with respect to the different variables.
        '''
        operator : AdditiveMap = self.base().operators()[operation]
        if ttype == "homomorphism":
            def __extended_homomorphism(element : DPolynomial) -> DPolynomial:
                element = self(element)

                if(element in self.base()):
                    return self(operator(self.base()(element)))

                if(element not in self.__cache[operation]):
                    self.__cache[operation][element] = self.element_class(
                        self,
                        {m._shift_(operation) : operator(c) for (m,c) in element._content.items()}
                    )

                return self.__cache[operation][element]
            func = __extended_homomorphism
        elif ttype == "derivation":
            def __extended_derivation(element : DPolynomial) -> DPolynomial:
                element = self(element)

                if(element in self.base()):
                    return self(operator(self.base()(element)))

                if(element not in self.__cache[operation]):
                    final_dict = dict()
                    for (m,c) in element._content.items():
                        for nm, e in m._derivative_(operation):
                            final_dict[nm] = final_dict.get(nm, self.base().zero()) + c*e
                        final_dict[m] = final_dict.get(m, self.base().zero()) + operator(c)

                    self.__cache[operation][element] = self.element_class(self, final_dict)

                return self.__cache[operation][element]
            func = __extended_derivation
        elif ttype == "skew":
            raise NotImplementedError("The 'skew' case is not yet implemented")
            # func = None
        else:
            raise ValueError(f"The type {ttype} is not recognized as a valid operator.")

        return AdditiveMap(self, func)

    def add_constants(self, *new_constants: str) -> DPolynomialRing_Monoid:
        return DPolynomialRing(self.base().add_constants(*new_constants), *self.variable_names())

    def linear_operator_ring(self) -> Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        if self.ngens() > 1:
            raise NotImplementedError(f"Impossible to generate ring of linear operators with {self.ngens()} variables")

        return self.base().linear_operator_ring()

    def inverse_operation(self, element: DPolynomial, operation: int = 0) -> DPolynomial:
        if element not in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if self.operator_types()[operation] == "homomorphism":
            return self.__inverse_homomorphism(element, operation)
        elif self.operator_types()[operation] == "derivation":
            return self.__inverse_derivation(element, operation)
        elif self.operator_types()[operation] == "skew":
            return self.__inverse_skew(element, operation)
        else:
            raise NotImplementedError("[inverse_operation] Inverse for unknown operation not implemented")

    def __inverse_homomorphism(self, element: DPolynomial, operation: int):
        # solution = self.zero()
        # for coeff, monomial in zip(element.coefficients(), element.monomials()):
        #     coeff = coeff.inverse_operation(operation) if not coeff.d_constant() else coeff
        #     variables = monomial.variables()
        #     new_mon = self.one()
        #     for v in variables:
        #         for g in element.infinite_variables():
        #             if v in g:
        #                 ind = list(g.index(v, True))
        #                 if ind[operation] == 0:
        #                     raise ValueError(f"[inverse_homomorphism] Found an element impossible to invert: {monomial}")
        #                 ind[operation] -= 1
        #                 new_mon *= g[tuple(ind) if len(ind) > 1 else ind[0]]
        #     solution += coeff*new_mon
        # return solution
        raise NotImplementedError("This method is not yet implemented")

    def __inverse_derivation(self, element: DPolynomial, operation: int):
        r'''
            Implementation of integration of differential polynomials using Bilge's INTEG algorithm
            (see :doi:`10.1016/0010-4655(92)90013-o`).

            Method ``INTEG`` splits a differential polynomial into three parts: an integrable part, a
            non-integrable part and a constant part. We ignore the constant part (we always assume it to
            be zero).
        '''
        A,B = self.integral_decomposition(element, operation)
        if B != 0:
            raise ValueError(f"[inverse_derivation] Element {element} not integrable -> non-zero non-integrable part in decomposition: {B}")
        
        return A

    def __inverse_skew(self, element: DPolynomial, operation: int):
        raise NotImplementedError("[inverse_skew] Skew-derivation operation not yet implemented")
    
    def integral_decomposition(self, element: DPolynomial, operation: int = 0) -> tuple[DPolynomial, DPolynomial]:
        r'''
            Method to compute an integral decomposition of an element.

            Method that perform an integral decomposition, i.e., takes an element `f` and computes two new values 
            `A` and `B` such that ``f = partial(A) + B``.

            A good integral decomposition is such that `f` is integrable if and only if `B = 0`.
            
            In the article by Bilge (:doi:``), an integral decomposition is computed where `f = partial(A) + B + C`
            where `C` is an element of the base field, obtaining that `f` is integrable if and only if `B = 0` and 
            `C` is integrable.

            This is the algorithm we are implementing here in the context of :class:`DPolynomial`, after the computation w.r.t. `C`.
        '''
        logger.debug(f"[inverse_derivation] Called with {element}")
        if self.operator_types()[operation] != "derivation":
            raise TypeError(f"Computing inverse derivation for an operation ({operation}) that is not a derivation.")
        
        ## Casting the element to ``self``
        element = self(element) if not hasattr(element, "parent") or element.parent() != self else element

        ## Calling the recursive method with the beginning arguments
        return self.__integral_decomposition(element, operation, self.zero(), self.zero())

    def __integral_decomposition(self, element: DPolynomial, operation: int, integral: DPolynomial, nintegral: DPolynomial) -> tuple[DPolynomial, DPolynomial]:
        if element == 0:
            logger.debug(f"[integral_decomposition] Found a zero --> Easy (we do nothing)")
            return integral, nintegral
        elif element.constant_coefficient() != 0:
            logger.debug(f"[integral_decomposition] Found a constant coefficient --> Computing this part first")
            coeff = element.constant_coefficient()
            try:
                integral += self(coeff.inverse_operation(operation))
            except Exception:
                nintegral += self(coeff)
            return self.__integral_decomposition(element - coeff, operation, integral, nintegral)
        elif element.degree() == 1:
            logger.debug(f"[integral_decomposition] Found linear element --> Easy to do")
            for monomial, coeff in element._content.items():
                if monomial.is_one():
                    raise RuntimeError(f"[integral_decomposition] (Constant coefficient) This should never happen!!")
                else:
                    # We are in the term (c*v^(d)), we can see that:
                    #     (c*v^(d-1))' = c'*v^(d-1) + c*v^(d)
                    # So we can then write
                    #     c*v^(d) = (c*v^(d-1))' - c'v^(d-1)
                    # We now iterate this process on the c'v^(d-1) term, obtaining:
                    #     c*v^(d) = (c*v^(d-1) - c'*v^(d-2)) + c''*v^(d-2)
                    var = next(iter(monomial.variables()))
                    var, (i,) = next(iter(monomial._variables))
                    var = self.gens()[var]
                    integral += sum((-1)**j*coeff.operation(operation, times=j)*var[i-1-j] for j in range(i))
                    nintegral += (-1)**i*coeff.operation(operation, times=i)*var[0]
            return integral, nintegral
        else:
            logger.debug(f"[integral_decomposition] Element is not linear")
            monomials = element.monomials()
            if 1 in monomials:
                raise RuntimeError(f"[integral_decomposition] (Constant coefficient) This should never happen!!")
            monomials_with_points = []
            for mon in monomials:
                bv = max(k[0] for k in mon._variables) # index of the maximum variable
                bo = mon.order(bv, operation) # order of the biggest variable w.r.t. operation
                monomials_with_points.append((bv, bo))

            V, O = max(monomials_with_points)
            V = self.gens()[V]
            logger.debug(f"[integral_decomposition] Maximal variable: {V[O]}")

            D = element.degree(V[O])
            highest_part = element.coefficient_full(V[O]**D)

            if D > 1: ## Highest variable non linear --> non-integrable
                return self.__integral_decomposition(
                    element - highest_part * V[O]**D, operation, 
                    integral, 
                    nintegral + highest_part * V[O]**D
                )
            elif O == 0: ## Highest variable without derivatives --> non-integrable
                return self.__integral_decomposition(
                    element - highest_part * V[O], operation,
                    integral,
                    nintegral + highest_part * V[O]
                )
            else:
                deg_order_1 = highest_part.degree(V[O-1])

                cs = [highest_part.coefficient_full(V[O-1]**i) for i in range(deg_order_1+1)]
                order_1_part = sum(cs[i]*V[O-1]**i for i in range(deg_order_1+1))
                q1 = highest_part - order_1_part # order q1 < d-1

                ## we compute remaining polynomial
                partial_integral = sum(cs[i]/ZZ(i+1) * V[O-1]**(i+1) for i in range(deg_order_1+1)) + V[O-1]*q1 # division is on coeff. level

                logger.debug(f"[integral_decomposition] Partial integral: {partial_integral}")
                integral += partial_integral
                element -= partial_integral.operation(operation)
                logger.debug(f"[integral_decomposition] Remaining to integrate: {element}")
                return self.__integral_decomposition(element, operation, integral, nintegral)

    @cached_method
    def to_sage(self):
        result = InfinitePolynomialRing(self.base().to_sage(), [el.replace("_", "") for el in self.variable_names()])
        map_of_variables = dict(zip(self.gens(), result.gens()))
        inverse_map_of_variables = list(zip(result.gens(), self.gens()))
        ## Creating the conversion between ``self`` and the plain sage equivalent
        self.register_conversion(MapSageToDalgebra_Infinite(result, self, inverse_map_of_variables))
        result.register_conversion(MapDalgebraToSage_Infinite(self, result, map_of_variables))

        return result

    #################################################
    ### Sylvester methods
    #################################################
    def sylvester_resultant(self, P: DPolynomial, Q: DPolynomial, gen: DMonomialGen = None) -> DPolynomial:
        r'''
            Method to compute the Sylvester resultant of two operator polynomials.

            **REMARK**: this method only works when ``self`` have with 1 operator and both `P` and `Q` are linear on the given generator.

            If we have two linear operator polynomials `P(u), Q(u) \in R\{u\}` where `(R, \sigma)` is a ring with 1 operator `\sigma`,
            then we can consider the extended system

            .. MATH::

                \{P, \sigma(P), \ldots, \sigma^{m-1}(P), Q, \sigma(Q), \ldots, \sigma^{n-1}(Q)\},

            where `n` is the order of `P` and `m` is the order of `Q`. Then, it is clear that the only appearances of the infinite variable
            `u_*` is within `[u_0,\ldots,u_{n+m-1}]`. Hence we can build a Sylvester-type matrix using these polynomials and compute its
            determinant obtaining an expression in `R`.

            This determinant is called the Sylvester resultant of `P` and `Q` and it is equivalent to the Sylvester resultant on the algebraic case.

            This method computes the Sylvester resultant of two linear operator polynomials given the appropriate variable. If only one infinite variable
            is present, the it is not necessary to provide this value.

            INPUT:

            * ``P``: an operator polynomial (has to be linear) to be used as `P`.
            * ``Q``: an operator polynomial (has to be linear) to be used as `Q`.
            * ``gen``: an infinite variable that will be eliminated from `P` and `Q`. Can be ``None`` only if one infinite variable is in ``self``.

            OUTPUT:

            A :class:`~.dpolynomial.DPolynomial` with the Sylvester resultant of `P` and `Q`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_resultant(Q)
                (x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19)

            If several variables are available, we need to explicitly provide the variable we are considering::

                sage: R.<u,v> = DPolynomialRing(B)
                sage: P = (3*x -1)*u[0]*v[0] + x^2*v[1]*u[0] + u[2]
                sage: Q = 7*x*v[0]*u[0] + x^2*v[0]*u[1]
                sage: P.sylvester_resultant(Q)
                Traceback (most recent call last):
                ...
                ValueError: [sylvester_checking] No infinite variable provided but several available.
                sage: P.sylvester_resultant(Q, u)
                (56*x^2)*v_0^2 + x^6*v_0^2*v_1 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, v)
                (14*x^3)*u_0*u_1*u_2 + (49*x^2)*u_0^2*u_2 + x^4*u_1^2*u_2

            The infinite variable can also be given as an index::

                sage: P.sylvester_resultant(Q, 0)
                (56*x^2)*v_0^2 + x^6*v_0^2*v_1 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, 1)
                (14*x^3)*u_0*u_1*u_2 + (49*x^2)*u_0^2*u_2 + x^4*u_1^2*u_2
                sage: P.sylvester_resultant(Q, 2)
                Traceback (most recent call last):
                ...
                IndexError: [sylvester_checking] Requested generator 2 but only 2 exist.
                sage: P.sylvester_resultant(Q, -1)
                Traceback (most recent call last):
                ...
                IndexError: [sylvester_checking] Requested generator -1 but only 2 exist.
        '''
        return self.sylvester_matrix(P,Q,gen).determinant()

    @cached_method
    def sylvester_subresultant(self, P: DPolynomial, Q: DPolynomial, gen: DMonomialGen = None, k: int = 0, i: int = 0):
        r'''
            Method to compute the `(k,i)`-th Sylvester subresultant of two operator polynomials.

            From :func:`sylvester_matrix`, we obtain the matrix `S_k(P,Q)` which has `k` more columns than rows. In
            order to obtain a square matrix, we can remove `k` columns. In particular, removing the `k` out of the `k+1`
            first columns (which are related to the coefficients of `(1,\ldots,\partial^k)`).

            The corresponding `(k,i)`-th subresultant of `P` and `Q` is the determinant of this matrix.

            In particular, when `k=0` and `i=0`, then the subresultant is exactly the Sylvester resultant of `P` and `Q`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant(P, Q, k=1, i=0)
                -(3*x^3 + 3*x^2 - 3*x - 2)
                sage: S.sylvester_subresultant(P, Q, k=1, i=1)
                (8*x^2 + 7*x)

            We can see that the case with `k=0` and `i=0`coincides with the method :func:`sylvester_resultant`::

                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant(P, Q, k=0, i=0) == P.sylvester_resultant(Q)
                True
        '''
        ## Checking the argument `i`
        if i not in ZZ:
            raise TypeError(f"[sylvester_subresultant] The argument {i = } must be an integer")
        elif i < 0 or i > k:
            raise ValueError(f"[sylvester_subresultant] The index {i = } is out of proper bounds [0,...,{k}]")

        S_k = self.sylvester_matrix(P,Q,gen,k)
        S_ki = S_k.matrix_from_columns([i]+list(range(k+1,S_k.ncols())))
        return S_ki.determinant()

    @cached_method
    def sylvester_matrix(self, P: DPolynomial, Q: DPolynomial, gen: DMonomialGen = None, k: int = 0) -> Matrix:
        r'''
            Method to obtain the `k`-Sylvester matrix for two operator polynomials.

            **REMARK**: this method only works when ``self`` have with 1 operator and both `P` and `Q` are linear on the given generator.

            If we have two linear operator polynomials `P(u), Q(u) \in R\{u\}` where `(R, \sigma)` is a ring with 1 operator `\sigma`,
            then we can consider the extended system

            .. MATH::

                \Xi_k(P,Q) = \{P, \sigma(P), \ldots, \sigma^{m-1-k}(P), Q, \sigma(Q), \ldots, \sigma^{n-1-k}(Q)\},

            where `n` is the order of `P` and `m` is the order of `Q` and `k \in\{0,\ldots,N\}` for `N \min(n,m)-1`. We can
            build a Sylvester-type matrix using these polynomials.

            INPUT:

            * ``P``: an operator polynomial (has to be linear) to be used as `P`.
            * ``Q``: an operator polynomial (has to be linear) to be used as `Q`.
            * ``gen``: an infinite variable that will be eliminated from `P` and `Q`. Can be ``None`` only if one infinite variable is in ``self``.
            * ``k``: an integer in `\{0,\ldots,N\}` to get the corresponding `k`-Sylvester matrix. When `k = 0`, the matrix is square.

            OUTPUT:

            A Sylvester-type matrix for the corresponding operators.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_matrix(Q)
                [      (x^2 - 1)          -(3*x)               1               0               0]
                [              0     (x^2 + 2*x)      -(3*x + 3)               1               0]
                [              0               0 (x^2 + 4*x + 3)      -(3*x + 6)               1]
                [             -1               0               0               1               0]
                [              0              -1               0               0               1]
                sage: P.sylvester_matrix(Q, k=1)
                [  (x^2 - 1)      -(3*x)           1           0]
                [          0 (x^2 + 2*x)  -(3*x + 3)           1]
                [         -1           0           0           1]

            It is important to remark that this matrix depends directly on the operation defined on the ring::

                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_matrix(Q)
                [(x^2 - 1)    -(3*x)         1         0         0]
                [    (2*x) (x^2 - 4)    -(3*x)         1         0]
                [        2     (4*x) (x^2 - 7)    -(3*x)         1]
                [       -1         0         0         1         0]
                [        0        -1         0         0         1]
                sage: P.sylvester_matrix(Q,k=1)
                [(x^2 - 1)    -(3*x)         1         0]
                [    (2*x) (x^2 - 4)    -(3*x)         1]
                [       -1         0         0         1]

            However, the Sylvester matrix is not well defined when the ring has several operations::

                sage: B = DifferentialRing(DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)), diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[0,2] - 3*x*z[0,1] + (x^2 - 1)*z[1,0]
                sage: Q = z[2,3] - z[1,0]
                sage: P.sylvester_matrix(Q)
                Traceback (most recent call last):
                ...
                NotImplementedError: [sylvester_checking] Sylvester resultant with 2 is not implemented

            But it works nicely with several d-variables in the ring::

                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<y,z> = DPolynomialRing(B)
                sage: P = z[2] - 3*y[0]*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - y[1]*z[0]
                sage: P.sylvester_matrix(Q, gen=z)
                [        (x^2 - 1)            -3*y_0                 1                 0                 0]
                [            (2*x) (x^2 - 1) - 3*y_1            -3*y_0                 1                 0]
                [                2     (4*x) - 3*y_2 (x^2 - 1) - 6*y_1            -3*y_0                 1]
                [             -y_1                 0                 0                 1                 0]
                [             -y_2              -y_1                 0                 0                 1]
        '''
        ## Checking the polynomials and ring arguments
        P,Q,gen = self.__process_sylvester_arguments(P,Q,gen)

        ## Checking the k argument
        n, m = P.order(gen), Q.order(gen)
        N = min(n,m) - 1

        # Special case when one of the orders is -1 (i.e., the variable `gen` is not present)
        if n == -1:
            return matrix([[P]]) # P does not contain the variable `gen` to eliminate
        elif m == -1:
            return matrix([[Q]]) # Q does not contain the variable `u` to eliminate

        if k not in ZZ:
            raise TypeError(f"[sylvester_matrix] The index {k = } is not an integer.")
        elif N == -1 and k != 0:
            raise TypeError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0].")
        elif N >= 0 and (k < 0 or k > N):
            raise ValueError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0,...,{N}]")

        homogeneous = any(poly.constant_coefficient(gen) != 0 for poly in (P,Q))

        if homogeneous and k > 0:
            raise NotImplementedError(f"[sylvester_matrix] The case of inhomogeneous operators and positive {k=} is not implemented.")

        extra = 1 if homogeneous else 0
        logger.info(f"Sylvester data: {n=}, {m=}, {k=}, {homogeneous=}")

        # Building the extension
        extended_P: list[DPolynomial] = [P.operation(times=i) for i in range(m-k+extra)]
        extended_Q: list[DPolynomial] = [Q.operation(times=i) for i in range(n-k+extra)]

        # Building the Sylvester matrix (n+m-1-k) , (n+m-1-k)
        cols = [gen[pos] for pos in range(n+m-k+extra)]
        equations = extended_P + extended_Q

        ## We get the coefficient of the sylvester matrix
        nrows = len(equations)
        ncols = len(cols) + (1 if homogeneous else 0)
        output = sum([([self(equation).constant_coefficient(gen)] if homogeneous else []) + [self(equation.coefficient_full(m)) for m in cols] for equation in equations], [])

        output = matrix([output[r*ncols:r*ncols + ncols] for r in range(nrows)])

        # Returning the matrix
        logger.info(f"Obtained following matrix:\n{output}")
        return output

    def sylvester_subresultant_sequence(self, P: DPolynomial, Q: DPolynomial, gen: DMonomialGen = None) -> tuple[DPolynomial]:
        r'''
            Method that gets the subresultant sequence in form of a linear d-polynomial.

            As described in :func:`sylvester_subresultant`, when we build the `k`-Sylvester matrix of two linear
            d-polynomials, we obtain a non-square matrix and, in order to compute a determinant, we need to remove `k`
            columns. The subresultants are built by removing `k` out of the first `k+1` columns.

            Hence, we have remaining one columns corresponding to one operator `\sigma^i`. We can then consider the
            following linear operator:

            .. MATH::

                \mathcal{S}_k(P,Q) = \sum_{i=0}^k S_{k,i}(P,Q)\sigma^i

            When iterating w.r.t. `k`, we obtain a sequence of linear operators. This is called the subresultant
            sequence of the d-polynomials `P` and `Q`.

            This sequence is important because it describes the common factor (as operator) of the two d-polynomials. More
            precisely, if the first element is zero (i.e., the Sylvester resultant is zero), then `P` and `Q`
            has a common right factor as linear operators.

            Moreover, the first non-zero element in the sequence provides a formula for the greatest right common factor.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant_sequence(P, Q)
                ((x^6 + 6*x^5 + 10*x^4 - 18*x^3 - 65*x^2 - 42*x - 2)*z_0, -(3*x^3 + 3*x^2 - 3*x - 2)*z_0 + (8*x^2 + 7*x)*z_1)
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant_sequence(P, Q)
                ((x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19)*z_0, -(3*x^3 - x + 1)*z_0 + (8*x^2 + 4)*z_1)
        '''
        ## Checking the polynomials and ring arguments
        P,Q,gen = self.__process_sylvester_arguments(P,Q,gen)
        return tuple(
            sum(self.sylvester_subresultant(P,Q,gen,k,i) * gen[i] for i in range(k+1))
            for k in range(min(P.order(gen),Q.order(gen)))
        )

    def __process_sylvester_arguments(self, P: DPolynomial, Q: DPolynomial, gen: DMonomialGen):
        r'''Check the ring, the generator and the polynomials are correct'''
        ## Checking the ring is appropriate
        if self.noperators() > 1:
            raise NotImplementedError(f"[sylvester_checking] Sylvester resultant with {self.noperators()} is not implemented")

        ## Checking the gen is correctly given
        if self.ngens() > 1 and gen is None:
            raise ValueError("[sylvester_checking] No infinite variable provided but several available.")
        elif self.ngens() > 1 and gen in ZZ:
            if gen < 0 or gen >= self.ngens():
                raise IndexError(f"[sylvester_checking] Requested generator {gen} but only {self.ngens()} exist.")
            gen = self.gens()[gen]
        elif gen in ZZ:
            gen = self.gens()[gen]
        elif isinstance(gen, DMonomialGen) and gen not in self.gens():
            raise ValueError(f"[sylvester_checking] The variable {repr(gen)} do not belong to {self}")
        elif self.ngens() == 1 and gen is None:
            gen = self.gens()[0]
        elif isinstance(gen, str):
            gen = self.gen(gen)

        ## Checking the operator polynomials are correct
        P, Q = self(P), self(Q)
        if not P.is_linear([gen]):
            raise TypeError(f"[sylvester_checking] The polynomial {P} is not linear w.r.t. {gen}")
        if not Q.is_linear([gen]):
            raise TypeError(f"[sylvester_checking] The polynomial {Q} is not linear w.r.t. {gen}")

        return P,Q,gen

    #################################################
    ### Weighting and Ranking methods
    #################################################
    def weight_func(self, weight_vars, weight_operators) -> WeightFunction:
        r'''
            TODO: add documentation to this method
        '''
        return WeightFunction(self, weight_vars, weight_operators)

    def ranking(self, ordering: list[DMonomialGen] | tuple[DMonomialGen] = None, ttype: str = "orderly") -> RankingFunction:
        r'''
            Method to create a ranking for this ring.

            This method creates a ranking for ``self`` using the arguments as in :class:`RankingFunction`.
        '''
        if ordering is None:
            ordering = self.gens()
        elif isinstance(ordering, list):
            ordering = tuple(ordering)

        if not ttype in ("orderly", "elimination"):
            raise ValueError("Only 'orderly' and 'elimination' rankings are allowed")

        if (ordering, ttype) not in self.__cache_ranking:
            self.__cache_ranking[(ordering, ttype)] = EliminationRanking(self, ordering) if ttype == "elimination" else OrderlyRanking(self, ordering)
        return self.__cache_ranking[(ordering, ttype)]

    def elimination_ranking(self, ordering: list[DMonomialGen] | tuple[DMonomialGen] = None):
        return self.ranking(ordering, "elimination")
    
    def orderly_ranking(self, ordering: list[DMonomialGen] | tuple[DMonomialGen] = None):
        return self.ranking(ordering, "orderly")

    #################################################
    ### Other computation methods
    #################################################
    def as_linear_operator(self, element: DPolynomial) -> Element:
        r'''
            Method that tries to convert an operator polynomial into a linear operator.

            This method tries to create a linear operator coming from a :class:`DPolynomial`.
            In the case where we have an :class:`DPolynomial` `p(u) \in R\{u\}` (for `R` a ring with operators)
            we can interpret the polynomial `p(u)` as an operator over any extension of `R` that acts
            by substituting `u` by the element the operator acts on. If `p` is linear, then it represents
            what it is called a linear operator.

            These linear operators may be represented more efficiently in other structures (see :func:`linear_operator_ring`
            for further information). This method transforms the elements of ``self`` that can be seen as linear
            operators to this ring structure.

            Conversely, a :class:`DPolynomialRing_Monoid` can transform elements from its ring of linear operators
            (i.e., the output of :func:`linear_operator_ring`) to linear :class:`DPolynomial`.

            This method checks that ``self`` has the appropriate structure (i.e., it has only one infinite variable)
            and also the ``element`` has the appropriate shape: it is linear without a constant term.

            REMARK: **this method is equivalent to the method :func:`~.dpolynomial_ring_element.DPolynomial.as_linear_operator`
            since it calls this method directly**

            INPUT:

            * ``element``: a :class:`DPolynomial` in ``self`` to be casted to a linear operator.

            OUTPUT:

            An element in ``self.linear_operator_ring()`` if this ring can be built.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DifferentialPolynomialRing(QQ[x]); x = R.base()(x)
                sage: p1 = y[2] - (x^2 - 1)*y[1] - y[0] # linear operator of order 2
                sage: p1.as_linear_operator() # D^2 + (-x^2 + 1)*D - 1
                Traceback (most recent call last):
                ...
                NotImplementedError: ...
                sage: R(p1.as_linear_operator()) == p1 # True
                Traceback (most recent call last):
                ...
                NotImplementedError: ...

            If the operator polynomial is not linear or has a constant term, this method raises a :class:`TypeError`::

                sage: p2 = x*y[2]*y[0] - (x^3 + 3)*y[1]^2 # non-linear operator
                sage: p2.as_linear_operator() # TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.
                Traceback (most recent call last):
                ...
                NotImplementedError: ...
                sage: p3 = y[2] - (x^2 - 1)*y[1] - y[0] + x^3 # linear operator but inhomogeneous
                sage: p3.as_linear_operator() # TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.
                Traceback (most recent call last):
                ...
                NotImplementedError: ...

            This also work when having several operators in the same ring::

                sage: S.<u> = DPolynomialRing(DifferenceRing(DifferentialRing(QQ[x], diff), QQ[x].Hom(QQ[x])(QQ[x](x)+1))); x = S.base()(x)
                sage: p4 = 2*u[0,0] + (x^3 - 3*x)*u[1,0] + x*u[1,1] - u[2,2]
                sage: p4.as_linear_operator() # -D^2*S^2 + x*D*S + (x^3 - 3*x)*D + 2
                Traceback (most recent call last):
                ...
                NotImplementedError: ...
                sage: S(p4.as_linear_operator()) == p4 # True
                Traceback (most recent call last):
                ...
                NotImplementedError: ...

            However, when having several infinite variables this method can not work even when the operator is clearly linear::

                sage: T.<a,b> = DifferentialPolynomialRing(QQ[x]); x = T.base()(x)
                sage: p5 = a[0] - b[1]
                sage: p5.as_linear_operator()
                Traceback (most recent call last):
                ...
                NotImplementedError: ...

        '''
        # linear_operator_ring = self.linear_operator_ring() # it ensures the structure is alright for building this
        # element = self(element) # making sure the element is in ``self``

        # if not element.is_linear() or 1 in element.polynomial().monomials():
        #     raise TypeError("Linear operator can only be built from an homogeneous linear operator polynomial.")

        # coeffs = element.coefficients(); monoms = element.monomials(); y = self.gens()[0]
        # base_ring = linear_operator_ring.base(); gens = linear_operator_ring.gens()

        # return sum(base_ring(c)*prod(g**i for (g,i) in zip(gens, y.index(m,as_tuple=True))) for (c,m) in zip(coeffs, monoms))
        raise NotImplementedError(f"Method need a revision")

def is_DPolynomialRing(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, DPolynomialRing_Monoid)


is_RWOPolynomialRing = is_DPolynomialRing #: alias for is_DPolynomialRing (used for backward compatibility)

#################################################################################################
### FUNCTORS AND MORPHISMS
#################################################################################################
class DPolyRingFunctor (ConstructionFunctor):
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
    def __init__(self, variables):
        self.__variables = set(variables)
        super().__init__(_DRings,_DRings)
        self.rank = 12 # just above PolynomialRing and DRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        return DPolynomialRing(x,list(self.variables()))

    def _repr_(self):
        return f"DPolynomialRing((*),{self.variables()})"

    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.variables() == self.variables())

    def merge(self, other):
        if isinstance(other, DPolyRingFunctor):
            self_names = self.__variables
            other_names = other.__variables
            global_names = tuple(set(list(self_names)+list(other_names)))
            return DPolyRingFunctor(global_names)
        return None

    def variables(self) -> set[str]:
        return self.__variables

    def append_variables(self, *variables) -> DPolyRingFunctor:
        r'''Returns the same functor with more variables attached. If repeated variables are provided, we raise an error'''
        new_vars = set(variables)
        if len(variables) > len(new_vars) or new_vars.intersection(self.variables()):
            raise ValueError(f"Repeated variables: impossible to extend the Functor")
        return self.__class__(self.variables().union(new_vars))

class DPolynomialToLinOperator (Morphism):
    r'''
        Class representing a map to a ring of linear operators

        This map allows the coercion system to detect that some elements in a
        :class:`DPolynomialRing_Monoid` are included in its ring of linear operators.
    '''
    def __init__(self, dpoly_ring : DPolynomialRing_Monoid):
        linear_operator_ring = dpoly_ring.linear_operator_ring()
        super().__init__(dpoly_ring, linear_operator_ring)

    def _call_(self, p):
        return self.codomain()(self.domain().as_linear_operator(p))

class DPolynomialVariableMorphism (Morphism):
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        if not isinstance(codomain, DPolynomialRing_Monoid) or not isinstance(domain, DPolynomialRing_Monoid):
            raise TypeError("Incorrect domain or codomain for a map on d-variables")
        self.__map_vars = dict()
        dom_vnames = domain.variable_names()
        codom_vnames = codomain.variable_names()
        for (i,v) in enumerate(dom_vnames):
            self.__map_vars[i] = codom_vnames.index(v)
    def _call_(self, p):
       ## We do a deep transformation mapping the variables
        return self.codomain().element_class(
            self.codomain(),
            {
                self.codomain().monoids().element_class(
                    self.codomain().monoids(), {(self.__map_vars[v], o): e for ((v,o),e) in m._variables.items()}
                ) : c for (m,c) in p._content.items()
            }
        )

class DPolynomialSimpleMorphism (Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a
        :class:`DPolynomialRing_Monoid` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        if isinstance(codomain, DPolynomialRing_Monoid):
            self.__map_vars = dict()
            dom_vnames = domain.variable_names()
            codom_vnames = codomain.variable_names()
            for (i,v) in enumerate(codom_vnames):
                self.__map_vars[dom_vnames.index(v)] = i

    def _call_(self, p):
        if self.codomain() == self.domain().monoids():
            if p.is_monomial():
                return next(iter(p._content))
        elif isinstance(self.codomain(), DPolynomialRing_Monoid):
            if any(p.order(self.domain().gen(i)) >= 0 for i in range(self.domain().ngens()) if i not in self.__map_vars): # this variable appears
                raise ValueError(f"Impossible to convert element {p} from {self.domain()} to {self.codomain()}")
            ## We do a deep transformation mapping the variables
            return self.codomain().element_class(
                self.codomain(),
                {
                    self.codomain().monoids().element_class(
                        self.codomain().monoids(), {(self.__map_vars[v], o): e for ((v,o),e) in m._variables.items()}
                    ) : c for (m,c) in p._content.items()
                }
            )
        elif(p.degree() == 0):
            return self.codomain()(next(iter(p.coefficients())))

        return self.codomain()(str(p))

class MapSageToDalgebra_Infinite(Morphism):
    def __init__(self, domain, codomain, map_of_variables):
        super().__init__(domain, codomain)
        self.__map = map_of_variables

    def _call_(self, element):
        output = self.codomain().zero()
        for (c, m) in zip(element.coefficients(), element.monomials()):
            nc = self.codomain().base()(c)
            nm = self.codomain().one()
            for v in m.variables():
                vname, vindex = str(v).split("_")
                vindex = int(vindex)
                deg = m.degree(v)
                for g in self.domain().gens():
                    if vname == repr(g).removesuffix("_*"):
                        for (g_old, g_new) in self.__map:
                            if g_old == g:
                                nm *= g_new[vindex]**deg
                                break
                        else:
                            return NotImplementedError(f"We could not find new generator for gen {g}")
                        break
                else:
                    return NotImplementedError(f"We could not find generator for variable {v}")
            output += nc*nm
        return output
    
class MapDalgebraToSage_Infinite(Morphism):
    def __init__(self, domain, codomain, map_of_variables):
        super().__init__(domain, codomain)
        self.__map = map_of_variables
    
    def _call_(self, element):
        output = self.codomain().zero()
        for (c, m) in zip(element.coefficients(), element.monomials()):
            nc = self.codomain().base()(c)
            nm = self.codomain().one()
            for v in m.variables():
                deg = m.degree(v)
                for g in self.domain().gens():
                    if v in g:
                        nm *= self.__map[g][g.index(v, False)]**deg
                        break
                else:
                    return NotImplementedError(f"We could not find generator for variable {v}")
            output += nc*nm
        return output

#################################################################################################
### WEIGHT AND RANKING FUNCTIONS
#################################################################################################
class WeightFunction(SetMorphism):
    r'''
        Class to represent a weight or grading function for a ring of d-polynomials.

        Let `\mathcal{R} = (R,\Delta)\{a_1,\ldots,a_m\}` be a ring of d-polynomials and let `\mathcal{T}`
        be the monoid of monomials of `\mathcal{R}`. We say that a function `w: \mathcal{T} \rightarrow \mathbb{N}`
        if a weight function if it is a monoid homomorphism, i.e., `w(st) = w(s) + w(t)`.

        With this definition, it is clear that we can write the set `\mathcal{R}` a direct sum of the abelian groups where we keep in each
        summand the monomials of a fixed weight:

        .. MATH::

            \mathcal{R} = \bigoplus_{i \in \mathbb{N}} \mathcal{R}_i,

        where `\mathcal{R}_i = \langle t\ :\ t\in T\text{ with }w(t) = i\rangle_R`. We call each layer `\mathcal{R}_i` the set of
        `i`-homogeneous polynomials w.r.t. the weight function `w(\cdot)`.

        In order to define a weight function, we only need to define for each of the generators of `\mathcal{T}`. It
        is interesting to remark that, for a ring of d-polynomials, we have an infinite amount of generators. In order to simplify
        the implementation, we require two information:

        * A list of base weights `(w_1,\ldots,w_m)` such that `w(a_i) = w_i`.
        * A list of extending weights `(W_1,\ldots,W_n)` such that for

        .. MATH::

            w(\sigma_j^k(a_i)) = \left\{\begin{array}{ll}
                w_i + kW_j & \text{if w_i \neq 0},\\
                0 & \text{otherwise}.
            \end{array}\right.

        INPUT:

        * ``dpoly_ring``: a :class:`DPolynomialRing` over which we will base the weight function.
        * ``base_weights``: a list, tuple or dictionary indicating the base weights. If a variable is not provided, we consider it with weight 0.
        * ``operator_weights``: a list or tuple indicating how each operation extends the weights (i.e., a list with the `W_i`).

        TODO:

        * Add reference to weight functions in differential setting.
        * Add reference to weight functions in difference setting.
    '''
    def __init__(self, dpoly_ring: DPolynomialRing_Monoid, base_weights: list[int] | tuple[int] | dict[str | DMonomialGen, int], operator_weights: list[int] | tuple[int]):
        if isinstance(base_weights, (list,tuple)): # we got a list of weights
            if not len(base_weights) == dpoly_ring.ngens():
                raise TypeError(f"[WeightFunction] A weight must be define for all generators (got {len(base_weights)}, expected {dpoly_ring.ngens()})")
            if any(el < 0 for el in base_weights):
                raise ValueError(f"[WeightFunction] Weights must be always non-negative.")
        elif isinstance(base_weights, dict):
            base_weights = [int(base_weights.get(v, base_weights.get(v.variable_name(), base_weights.get(str(v), 0)))) for v in dpoly_ring.gens()]
            if any(el < 0 for el in base_weights):
                raise ValueError(f"[WeightFunction] Weights must be always non-negative.")
        else:
            raise TypeError("[WeightFunction] Weights must be given as lists or dictionaries.")
        self.__base_weights = base_weights

        if not isinstance(operator_weights, (list,tuple)): # we got a list of weights
            raise TypeError("[WeightFunction] Extension of weights must be given as lists.")
        if not len(operator_weights) == dpoly_ring.noperators():
            raise TypeError(f"[WeightFunction] A weight must be define for all operations (got {len(operator_weights)}, expected {dpoly_ring.noperators()})")
        if any(el <= 0 for el in operator_weights):
            raise ValueError(f"[WeightFunction] Weights must be always positive.")
        self.__operator_weights = operator_weights

        super().__init__(dpoly_ring.Hom(ZZ, _Sets), self.weight)

    def parent(self) -> DPolynomialRing_Monoid:
        r'''
            Return the base ring of d-polynomials
        '''
        return self.domain()

    def weight(self, element: DPolynomial) -> int:
        r'''
            Method to weight an element of the parent

            This method compute the actual weight of a d-polynomial. If the element is a monomial, we return the corresponding weight
            for the monoid as defined by its base weights. Otherwise, we return the maximal weight of the monomials appearing in ``self``.

            INPUT:

            * ``element``: a :class:`DPolynomial` in the base ring of the weight function.

            OUTPUT:

            The weight of the element following the usual definitions.

            TODO:

            * Add examples
        '''
        monomials = element.monomials()
        if len(monomials) == 0:
            return ZZ(0)
        elif len(monomials) > 1:
            return max(self(m) for m in monomials)
        else:
            m = monomials[0] # we treat the monomial by itself
            if m == 1:
                return ZZ(0)
            return sum(
                (self.__base_weights[i] + sum(j*w for (j,w) in zip(gen.index(variable, as_tuple=True), self.__operator_weights)))*m.degree(variable)
                for variable in m.variables()
                for (i,gen) in enumerate(self.parent().gens()) if variable in gen
            )

    def homogeneous_components(self, element: DPolynomial) -> dict[int, DPolynomial]:
        r'''
            Method that decomposes an element into its different homogeneous components.

            INPUT:

            * ``element``: the :class:`DPolynomial` that will be split into homogeneous components.

            OUTPUT:

            A dictionary (empty if ``element`` is zero) where the keys are the weights appearing in the polynomial
            and the values are the :class:`DPolynomial` that represent the terms of that specific weight. It must always
            satisfy that ``sum(out.values()) == element``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B.<c,x> = QQ[]
                sage: R.<a,b> = DPolynomialRing(DifferenceRing(DifferentialRing(B, lambda p : diff(p,x)), B.Hom(B)([c,x+1])))
                sage: w = R.weight_func([1,2],[2,1])
                sage: f = a[0,1]*b[0,0] + c*x^2*b[0,1]*a[0,0] - 2*c^2*a[3,1]
                sage: w.homogeneous_components(f)
                {4: (c*x^2)*a_0_0*b_0_1 + a_0_1*b_0_0, 8: -(2*c^2)*a_3_1}
                sage: sum(w.homogeneous_components(f).values()) == f
                True
                sage: w.homogeneous_components(R.zero())
                {}
        '''
        solution = dict()

        R = element.parent()

        if not element.is_zero():
            for c, m in zip(element.coefficients(), element.monomials()):
                w = self(m)
                if not w in solution:
                    solution[w] = element.parent().zero()
                
                solution[w] = solution[w] + c*R(m)

        return dict(sorted(solution.items()))


    @cached_method
    def weighted_variables(self, weight: int) -> set[DPolynomial]:
        r'''
            Method that generates the variables with a given weight.

            INPUT:

            * ``weight``: the value of the weight we want to generate

            OUTPUT:

            A set of :class:`DPolynomial` with variables of the given weight.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B.<c,x> = QQ[]
                sage: R.<a,b> = DPolynomialRing(DifferenceRing(DifferentialRing(B, lambda p : diff(p,x)), B.Hom(B)([c,x+1])))
                sage: w = R.weight_func([1,2],[2,1])
                sage: w.weighted_variables(0)
                set()
                sage: w.weighted_variables(1)
                {a_0_0}
                sage: w.weighted_variables(2)
                {a_0_1, b_0_0}
                sage: w.weighted_variables(3)
                {a_0_2, a_1_0, b_0_1}
                sage: w.weighted_variables(4)
                {a_0_3, a_1_1, b_0_2, b_1_0}
                sage: w.weighted_variables(5)
                {a_0_4, a_1_2, a_2_0, b_0_3, b_1_1}
                sage: w.weighted_variables(6)
                {a_0_5, a_1_3, a_2_1, b_0_4, b_1_2, b_2_0}
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                sage: w = R.weight_func([1,3],[1,1])
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
        '''
        if weight <= 0:
            return set()

        ## recursive part
        recursive = set()
        for i in range(self.parent().noperators()):
            recursive = recursive.union([v.operation(i) for v in self.weighted_variables(weight - self.__operator_weights[i])])

        ## adding the special case if needed
        return recursive.union(set([v[0] for (v,i) in zip(self.parent().gens(), self.__base_weights) if i == weight]))

    @cached_method
    def homogeneous_monomials(self, weight: int) -> tuple[DPolynomial]:
        r'''
            Method that generates the homogeneous monomials of weight ``weight``.

            This uses a recursive approach using the basic formulas on how to compute the
            weights of monomials.

            INPUT:

            * ``weight``: the value of the weight we want to generate.

            OUTPUT:

            A set of :class:`DPolynomial` with monomials of the given weight.

            REMARK:

            If a generator has weight zero, it won't appear in the set generated wince we could have infinitely many monomials, and we
            are looking for finite sets.

            TODO: add examples
        '''
        if weight < 0:
            return tuple()
        elif weight == 0:
            return tuple([self.parent().one()])
        else:
            result = list()
            to_add = list()

            ## operation part
            for (operator, ttype, op_weight) in zip(self.parent().operators(), self.parent().operator_types(), self.__operator_weights):
                if ttype == "derivation":
                    logger.debug(f"Adding derivations of monomials of weights {weight-op_weight}")
                    to_add += sum((tuple(self.parent()(m) for m in operator(mon).monomials()) for mon in self.homogeneous_monomials(weight - op_weight)), tuple())
                elif ttype == "homomorphism":
                    cweight = weight - op_weight
                    i = 1
                    while cweight >= 0:
                        logger.debug(f"Adding shifts of monomials of weights {cweight} with degree {i}")
                        to_add += sum((tuple(self.parent()(m) for m in operator(mon).monomials()) for mon in self.homogeneous_monomials(cweight) if mon.degree() == i), tuple())

                        i += 1
                        cweight -= op_weight
                else:
                    cweight = weight - 1
                    while cweight >= 0:
                        logger.debug(f"Adding operation of monomials of weights {cweight} that has weight {weight}")
                        to_add += sum(([self.parent()(m) for m in operator(mon).monomials() if self(m) == weight] for mon in self.homogeneous_monomials(cweight)), tuple())
                        cweight -= 1

            ## multiplication part
            for i in range(1,weight//2 + 1):
                logger.debug(f"Adding product of monomials of weights {i} and {weight-i}")
                to_add += [tl*th for (tl,th) in product(self.homogeneous_monomials(i), self.homogeneous_monomials(weight-i))]

            ## special cases for the variables
            to_add += [v[0] for i,v in enumerate(self.parent().gens()) if self.__base_weights[i] == weight]
            logger.debug(f"Special cases added: {len(to_add)}")

            added = set()
            for v in to_add:
                if v not in added:
                    result.append(v)
                    added.add(v)

            return tuple(result)

    def is_homogeneous(self, element: DPolynomial) -> bool:
        r'''
            Method that check if a polynomial is homogeneous w.r.t. this weight or not.
        '''
        if element == 0:
            return True
        mons = self.parent()(element).monomials()
        w = self(mons[0])
        return all(self(m) == w for m in mons[1:])

    def as_vector(self, element: DPolynomial) -> Element:
        element = self.parent()(element)
        if not self.is_homogeneous(element):
            raise ValueError("[WeightFunction] Vector representation only valid for homogeneous d-polynomials")

        w = self(element)
        mons = self.homogeneous_monomials(w)
        return vector([element.coefficient(m) for m in mons])

    def operation_from_vector(self, vector: Element, weight: int, operation: int):
        r'''
            Method that applies an operation to a vector.

            This method takes a vector, interpret it as an homogeneous element (hence the need to specifying the weight)
            and applies the corresponding operation to it. When the result is again homogeneous, we return the new vector.

            INPUT:

            * ``vector``: a vector with a parent that can be casted into ``self.parent()``.
            * ``weight``: the weight assigned to the vector. We need the dimension to be appropriate.
            * ``operation``: the operation to be applied. We will check the result is homogeneous again.

            OUTPUT:

            A new vector with the result of applying the given operation to the vector when interpret as a homogeneous d-polynomial.

            TODO: add examples
        '''
        mons = self.homogeneous_monomials(weight)
        if len(vector) != len(mons):
            raise TypeError(f"[WeightFunction] The given vector is not of appropriate dimension (got {len(vector)}, expected {len(mons)})")

        element = sum(c*m for (c,m) in zip(vector, mons))
        element = element.operation(operation)
        if not self.is_homogeneous(element):
            raise ValueError("[WeightFunction] After operation, the result is not homogeneous")

        return self.as_vector(element)

class RankingFunction:
    r'''
        Class for representing a ranking function over a ring of d-polynomials.

        Let `(R,(\sigma_1,\ldots,\sigma_n))\{u_1,\ldots,u_m\}` be a ring of d-polynomials with `n` operators and `m` d-variables.
        A ranking is a total order over the set of all the variables that satisfies the two axioms:

        * `t < \sigma_j(t)` for all monomial `t \in \mathcal{T}`.
        * If `t \leq s` then `\sigma_j(t) \leq \sigma_j(s)` for all monomials `s, t \in \mathcal{T}`.

        A ranking is the analog of a term ordering used in Gröbner bases algorithms. However, rankings order the monomials in
        `\mathcal{T}` that is a monoid infinitely generated with some extra properties that relate the operations with the variables.

        Once a ranking is fully define, the following methods are automatically defined for non-constant d-polynomials:

        * ``leader``: given `p(u) \in R\{u\}`, the leader is the actual variable that is maximal on the polynomial
        * ``rank``: given `p(u) \in R\{u\}`, the rank is the biggest monomial involving the leader variable.
        * ``initial``: given `p(u) \in R\{u\}`, the initial is the coefficient of the rank of the polynomial.
        * ``separant``: given `p(u) \in R\{u\}`, the separant is the derivative of `p(u)` w.r.t. the leader variable.

        INPUT:

        * ``parent``: a :class:`DPolynomialRing_Monoid` where the ranking will be applied.
        * ``ordering``: a list or tuple of :class:`DMonomialGen` that will include the variables of a :class:`DPolynomialRing_Monoid`
          that will be incorporated to the ranking and the base ordering between the base variables. In the case of missing variables,
          we will consider the ring `R\{u_1,\ldots,u_n\}` split into two layers `R\{u_1,\ldots,u_k\}\{u_{k+1},\ldots,u_n\}`, and the ranking 
          will be created for the outer variables.
        * ``ttype``: the type of ranking to be created. Currently, only "elimination" or "orderly" are allowed:
          - "elimination": the ranking will be the elimination ranking where the ``ordering`` determines the order of the variables.
          - "orderly": generates the orderly ranking where ``ordering`` provides the basic ordering between variables.

        TODO: add examples
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, ordering: (list | tuple)[DMonomialGen | str], order_operators: (list | tuple)[int] = None):
        ## Checking the argument ``parent``
        if not isinstance(parent, DPolynomialRing_Monoid):
            raise TypeError(f"[ranking] Rankings only defined over rings of d-polynomials")

        ## Checking the argument ``order_operators``
        if order_operators is None:
            order_operators = list(range(parent.noperators()))
        if not isinstance(order_operators, (list,tuple)) or len(order_operators) != parent.noperators():
            raise TypeError(f"[ranking] The order of operations must be always given")
        elif any(i not in ZZ or i < 0 or i >= parent.noperators() for i in order_operators):
            raise ValueError(f"[ranking] Invalid values for ordering the operations of the d-Ring")
        elif len(set(order_operators)) != parent.noperators():
            raise ValueError(f"[ranking] Invalid values for ordering the operations of the d-Ring (repeated elements)")
        
        ## Checking the argument ``ordering``
        if not isinstance(ordering, (list, tuple)): 
            raise TypeError(f"[ranking] Invalid format for ordering: must be a list or tuple")
        ordering = [parent.gen(v) if isinstance(v, str) else v for v in ordering]
        if any(v not in parent.gens() for v in ordering):
            raise ValueError(f"[ranking] Error in ordering of variables: provided a variable that is not in the ring")
        
        ## Storing the values into the class
        self.__parent = parent
        self.__ordering = tuple(ordering)
        self.__order_operators = tuple(order_operators)

    ## Attribute type methods
    def parent(self) -> DPolynomialRing_Monoid:
        return self.__parent
    
    @property
    def ordering(self) -> tuple[DMonomialGen]:
        return self.__ordering
    
    @property
    def order_operators(self) -> tuple[int]:
        return self.__order_operators
    
    ## Comparison methods
    def compare_gens(self, u: DPolynomialGen | str, v: DPolynomialGen | str) -> int:
        r'''
            Method that compares two d-variables.

            INPUT:

            * ``u``: first variable to be checked.
            * ``v``: second variable to be checked.

            OUTPUT:

            It returns a negative integer if `u < v` according to this ranking, a positive integer if `u > v` or `0` when no comparison is available.
            All variables not included in ``self.__ordering`` are considered smaller than those in sorted.
        '''
        u = self.parent().gens(u) if isinstance(u, str) else u
        v = self.parent().gens(v) if isinstance(v, str) else v

        if any(el not in self.parent().gens() for el in (u,v)):
            raise ValueError(f"[ranking - gens] Error when comparing generators: they are not generators of ``parent``")
        
        if u not in self.__ordering and v not in self.__ordering:
            return 0
        elif u not in self.__ordering:
            return -1
        elif v not in self.__ordering:
            return 1
        else:
            return self.__ordering.index(v) - self.__ordering.index(u)
        
    def compare_operations(self, t1: tuple[int], t2: tuple[int]) -> int:
        r'''
            Method that compares two tuples of elements marking how many operations has been performed over an element.

            This method uses :func:`order_operators` to check the ordering.
        '''
        t1 = [t1[i] for i in self.order_operators]
        t2 = [t2[i] for i in self.order_operators]

        if t1 < t2:
            return -1
        elif t1 > t2:
            return 1
        else:
            return 0

    def compare_variables(self, u: DPolynomial, v: DPolynomial) -> int:
        r'''
            Method to compare two variables.

            This method implements the actual ranking order. It compares two variables
            and returns which one is bigger as follows: the output is positive if `u > v`,
            the output is negative is `u < v` and the output is 0 if `u = v`.

            INPUT:

            * ``u``: first d-polynomial to be compared.
            * ``v``: second d-polynomial to be compared.

            OUTPUT:

            This method behaves like the :func:`cmp` method in Python 2.x, returning a negative element if `u < v`,
            a positive element if `u > v` and 0 if they are equal.
        '''
        raise NotImplementedError(f"[ranking - variables] This is an abstract method")
        
    def compare(self, p: DPolynomial, q: DPolynomial) -> int:
        r'''
            Method that compares two d-polynomials.

            This method is the critical step of a ranking function. It takes two variables in
            a ring of d-polynomials, i.e., two variables in a :class:`DPolynomialRing_Monoid`
            and compare which one is bigger in terms of this ranking function.

            When the inputs are d-polynomials (not only variables) we proceed to extend
            the ranking to the whole d-polynomial as follows:

            1. We sort by the leaders.
            2. If the leaders coincide, we sort by degree on the leader (i.e., by rank)
            3. If the rank coincide, we sort by initials (recursively).
            4. If we compare two elements without ranking (i.e., with leaders 1) we say they are equal.

            INPUT:

            * ``p``: first d-polynomial to be compared.
            * ``q``: second d-polynomial to be compared.

            OUTPUT:

            This method behaves like the :func:`cmp` method in Python 2.x, returning a negative element if `p < q`,
            a positive element if `p > q` and 0 if they are equal or we can not compare them.

            TODO: add examples
        '''
        u, v = self.leader(p), self.leader(q)
        # special cases when the leader are 1
        if u == 1 and v == 1:
            return 0
        elif u == 1:
            return -1
        elif v == 1:
            return 1

        # both have a non-constant leader
        cmp_leaders = self.compare_variables(u,v)
        if cmp_leaders != 0:
            return cmp_leaders

        # here the leader are the same
        cmp_rank = p.degree(u) - q.degree(u)
        if cmp_rank != 0:
            return cmp_rank

        # here the rank are equal
        return self.compare(self.initial(p), self.initial(q))
        
    ################################################################################
    ### Basic extraction methods from d-polynomials
    ################################################################################
    @cached_method
    def leader(self, element: DPolynomial) -> DPolynomial:
        r'''
            Method to get the leader variable from a d-polynomial.

            This method computes the leader variable for the current ranking function. The leader is the maximal
            variable that appear in a d-polynomial. If there is no variable appearing, we say the leader is the
            monomial `1`.

            INPUT:

            * ``element``: the d-polynomial to get the leader.

            OUTPUT:

            A variable of ``self.parent()`` or `1` if no variables to compare appear in ``element``.

            TODO: add examples
        '''
        element = self.parent()(element)

        ## we get the variables that must be ordered
        variables = [self.parent()(v) for v in element.variables() if any(v in g for g in self.ordering)]
        if len(variables) == 0: # if nothing is there, the leader is the `1`
            return self.parent().one()

        max_var = variables[0]
        for new_var in variables[1:]:
            if self.compare_variables(max_var, new_var) < 0: # max_var < new_var
                max_var = new_var
        return max_var

    @cached_method
    def rank(self, element: DPolynomial) -> DPolynomial:
        r'''
            Method to get the rank from a d-polynomial.

            This method computes the rank for the current ranking function. The rank is the maximal
            variable that appear in a d-polynomial to the highest degree. If there is no variable appearing, we say the rank is the
            monomial `1`.

            INPUT:

            * ``element``: the d-polynomial to get the rank.

            OUTPUT:

            A variable of ``self.parent()`` or `1` if no variables to compare appear in ``element``.

            TODO: add examples
        '''
        element = self.parent()(element)

        max_var = self.leader(element)
        if max_var == 1: # Special case when the polynomial do not involve any ranked variable
            return self.parent().zero()
        deg = element.degree(max_var) if max_var != self.parent().one() else 1
        return max_var**deg

    @cached_method
    def initial(self, element: DPolynomial) -> DPolynomial:
        r'''
            Method to get the initial from a d-polynomial.

            This method computes the initial for the current ranking function. The initial is the coefficient
            that multiplies the rank of a d-polynomial. If there is no variable appearing, we say the initial
            the whole d-polynomial.

            INPUT:

            * ``element``: the d-polynomial to get the initial.

            OUTPUT:

            The initial of ``element`` with respect to ``self``.

            TODO: add examples
        '''
        element = self.parent()(element)

        return element.coefficient_full(self.rank(element)) 

    @cached_method
    def separant(self, element: DPolynomial) -> DPolynomial:
        r'''
            Method to get the separant from a d-polynomial.

            This method computes the separant for the current ranking function. The separant is the partial
            derivative w.r.t. the leader variable of a d-polynomial. If there is no variable appearing, we
            define the separant to be zero.

            INPUT:

            * ``element``: the d-polynomial to get the separant.

            OUTPUT:

            The separant of ``element`` with respect to ``self``

            TODO: add examples
        '''
        element = self.parent()(element)

        max_var = self.leader(element)
        if max_var == 1: # Special case when no ranked variable is present
            return self.parent().zero()
        
        ## Else, we compute the partial derivative. For that, we convert the structure to usual polynomials
        poly_element, poly_var = self.parent().as_polynomials(element, max_var)
        return self.parent()(poly_element.derivative(poly_var)) 

    ################################################################################
    ### Boolean methods
    ################################################################################
    def is_partially_reduced(self, p: DPolynomial, A: DPolynomial | list[DPolynomial]) -> bool:
        r'''
            Method to check whether a d-polynomial `p` is *partially reduced* w.r.t. `A`.

            Let `A` be a d-polynomial and let `u_A` be its leader w.r.t. ``self``. We say that `p` is
            partially reduced w.r.t. `A` if no derivated element from `u_A` appear in `p`. For example,
            if `u_3\'\'` is the leader of `A`, then `u_3\'` may appear in `p`, but `u_3\'\'\'` cannot.

            For further information about this property, we refer to "Differential Algebra and Algebraic
            Groups" by E.R. Kolchin (1973). 
        '''
        if not isinstance(A, (list, tuple, set)):
            A = [A]
        p = self.parent()(p)
        A = [self.parent()(a) for a in A]

        if p == 0: # Special case, 0 is always partially reduced
            return True
        
        for a in A:
            u = self.leader(a)
            gu = u.infinite_variables()[0] # the generator of the leader
            if any(self.compare_variables(u, v) < 0 for v in p.variables() if v in gu):
                return False
        
        return True
    
    def is_reduced(self, p: DPolynomial, A: DPolynomial |list[DPolynomial]) -> bool:
        r'''
            Method to check whether a d-polynomial `p` is *partially reduced* w.r.t. `A`.

            We say that a d-polynomial `p` is reduced w.r.t. `A` if it is partially reduced (see :func:`is_partially_reduced`)
            and the degree of the leader of `A` is lower in `p` than in `A`.

            For further information about this property, we refer to "Differential Algebra and Algebraic
            Groups" by E.R. Kolchin (1973). 
        '''
        if not isinstance(A, (list, tuple, set)):
            A = [A]
        p = self.parent()(p)
        A = [self.parent()(a) for a in A]

        if p == 0: # Special case, 0 is always partially reduced
            return True
        
        if not self.is_partially_reduced(p, A):
            return False

        return all(p.degree(self.leader(a)) < a.degree(self.leader(a)) for a in A)            
    
    def is_autoreduced(self, A: DPolynomial | list[DPolynomial]) -> bool:
        r'''
            Method to check whether a set of d-polynomials `A` is autoreduced or not.

            A set `A` of d-polynomials is called *autoreduced* if, for every `p\in A`, `p`
            is reduced w.r.t. `A\setminus\{p\`}` (see :func:`is_reduced` for further information).

            In particular, singleton sets or empty sets are autoreduced.
        '''
        if A is None:
            raise TypeError(f"None is not a valid input for 'is_autoreduced'")
        if not isinstance(A, (list, tuple, set)):
            A = [A]

        if len(A) <= 1:
            return True
        
        return all(self.is_reduced(p, [a for a in A if a != p]) for p in A)

    ################################################################################
    ### Operations for d-polynomials induced by ranking
    ################################################################################
    def pseudo_quo_rem(self, p: DPolynomial, q: DPolynomial) -> tuple[DPolynomial, dict[tuple,tuple[DPolynomial,DPolynomial]], DPolynomial]:
        r'''
            Compute a pseudo-operational division of `p` and `q`.

            The output of this method will be a tuple `(a,b,r)` such that :

            * `ap + bq = r`,
            * `r < q`.

            In this case, the operations can be applied to `q` but not to `a`.
        '''
        if self.compare(p, q) < 0: # base case: we are done
            return (1, dict(), p)

        N = self.parent().noperators()

        ## Here we have p > q.
        ####################################################################
        ### In this part we will get:
        ###   - a
        ###   - b
        ###   - r
        ### such that `ap = b(q) + r` with `r < p`
        ####################################################################
        lp, lq = self.leader(p), self.leader(q)
        original_q = q
        comparison = self.compare_variables(lp, lq)
        if comparison < 0: # impossible condition
            raise TypeError("[ranking] Impossible condition reached: 'l(p) < l(q) when p > q'")
        elif comparison == 0: # same leader --> we need to multiply by the leader to match degrees
            a = lp**(q.degree(lp)-p.degree(lp)) * self.initial(q)
            b = {tuple(N*[0]): (self.initial(p), 1)}
            r = a*p - self.initial(p)*q
        else: # different variables are the leader. Two cases:
            vp = lp.infinite_variables()[0]
            vq = lq.infinite_variables()[0]
            if vp == vq: # the same variable --> we need to apply an operator to p
                ip = vp.index(lp, as_tuple=True)
                iq = vp.index(lq, as_tuple=True)
                operation = tuple([ip[i] - iq[i] for i in range(len(ip))])
                if any(el < 0 for el in operation):
                    raise TypeError("[ranking] Impossible condition reached: inverse operation from 'l(q)' to 'l(p)' when 'p > q'")
                prev = 1
            else: # different variables: we multiply `p` by `vq` and apply again
                operation = vp.index(lp, as_tuple=True)
                prev = vp[0]
            q = self.parent().apply_operations(prev*q, operation, _ordered=False)
            a = lp**(q.degree(lp)-p.degree(lp)) * self.initial(q)
            b = {operation: (self.initial(p), prev)}
            r = a*p - self.initial(p)*q

        ####################################################################
        ### In this part we will get:
        ###   - a
        ###   - b
        ###   - r
        ### such that `ap = b(q) + r` with `r < p`
        ####################################################################
        ra, rb, r = self.pseudo_quo_rem(r, original_q)
        fa = a*ra
        fb = {k: (ra*v[0], v[1]) for (k,v) in b.items()}
        fb.update(rb)

        return fa, fb, r

    def partial_remainder(self, p: DPolynomial, A: DPolynomial | list[DPolynomial]) -> tuple[DPolynomial, dict[DPolynomial,int]]:
        r'''
            Method to compute the partial remainder of `p` w.r.t. `A`. See pp. 77-78 of Kolchin's book.
        '''
        print(f"[partial_remainder] STARTING A PARTIAL REMAINDER COMPUTATION")
        if not isinstance(A, set):
            A = set(A) if isinstance(A, (list, tuple)) else set([A])

        if not self.is_autoreduced(A):
            raise TypeError(f"The partial remainder only works for autoreduced sets.")
        
        return self._partial_remainder(p, A)
    
    def _partial_remainder(self, p: DPolynomial, A: set[DPolynomial]) -> tuple[DPolynomial, dict[DPolynomial,int]]:
        logger.info(f"[partial_remainder] Starting partial remainder with leader {self.leader(p)} vs {[self.leader(a) for a in A]}")
        F = p

        ## We look for the first non-partially reduced
        A_sorted = self.sort(list(A), True) # sorted from biggest to smallest
        U = [self.leader(a) for a in A_sorted]

        for (a, u) in zip(A_sorted, U):
            gu = u.infinite_variables()[0]
            v = self.sort([g for g in F.variables() if g in gu], True)[0]
            if self.compare_variables(u, v) < 0: # v > u
                logger.debug(f"[partial_remainder] Found element not partially reduced to")
                to_apply = tuple([ov - ou for (ou, ov) in zip(gu.index(u, True), gu.index(v, True))])
                logger.debug(f"[partial_remainder] Operation to apply: {to_apply}")
                Sc = self.separant(a)
                e = F.degree(v)
                T = Sc*v - self.parent().apply_operations(a, to_apply)
                logger.debug(f"[partial_remainder] Current v: {v}")
                logger.debug(f"[partial_remainder] Found T: {T}")
                G = Sc**e * F.coefficient_without_var(v) + sum(Sc**(e-i) * F.coefficient_full(v**i) * T**i for i in range(1, F.degree(v)+1))
                logger.debug(f"[partial_remainder] Computed G: {G}")
                
                rF, rs = self._partial_remainder(G, A)
                rs[a] += e
                return rF, rs
            
        return F, {a : 0 for a in A}

    def remainder(self, p: DPolynomial, A: DPolynomial | list[DPolynomial]) -> tuple[DPolynomial, dict[DPolynomial,int], dict[DPolynomial,int]]:
        r'''
            Method to compute the remainder w.r.t. to an autoreduced set `A`. See pp. 78-79 of Kolchin's book.
        '''
        logger.info(f"[partial_remainder] STARTING A PARTIAL REMAINDER COMPUTATION")
        if not isinstance(A, set):
            A = set(A) if isinstance(A, (list, tuple)) else set([A])

        if not self.is_autoreduced(A):
            raise TypeError(f"The partial remainder only works for autoreduced sets.")
        
        return self._remainder(p, A)
    
    def _remainder(self, p: DPolynomial, A: set[DPolynomial]) -> tuple[DPolynomial, dict[DPolynomial,int], dict[DPolynomial,int]]:
        p, s = self._partial_remainder(p, A)

        A = self.sort(list(A)) # sorted from smallest to biggest

        i = dict()

        for r in range(len(A)-1, -1, -1): # we go from biggest to smallest
            u, I = self.leader(A[r]), self.initial(A[r])
                        
            I = self.initial(A[r])
            i[A[r]] = max(0, p.degree(u) - A[r].degree(u) + 1)

            pa, pp, pu = self.parent().as_polynomials(A[r], I**i[A[r]] * p, u)
            p = self.parent()(pa.parent()(pp.polynomial(pu) % pa.polynomial(pu)))

        return p, s, i

    def smallest(self, p: DPolynomial, q: DPolynomial) -> tuple[DPolynomial, DPolynomial]:
        r'''
            Method that return a variation of the arguments so they have the same leading term.

            The leading term for a given ranking is defined as the :func:`rank` times :func:`initial`
            of a d-polynomial. For any given pair of d-polynomials, there is a minimal rank
            that is greater or equal to both polynomials `p` and `q`.

            Then, this method returns an extension of both polynomials (i.e., the returned d-polynomials
            are obtained by multiplication and applying operations only) with that common bigger rank.
            Hence, the difference between the two polynomials has smaller rank than the common smallest
            rank of the two polynomials.
        '''
        if self.compare(p, q) > 0: # we return the inverse call to this function
            return tuple(list(self.smallest(q,p))[::-1])

        lp, lq = self.leader(p), self.leader(q)
        comparison = self.compare_variables(lp, lq)
        if comparison > 0: # impossible condition
            raise TypeError("[ranking] Impossible condition reached: 'l(p) > l(q) when p < q'")
        elif comparison == 0: # same leader --> we need to multiply by the leader to match degrees
            p = lp**(q.degree(lp)-p.degree(lp)) * p
            return self.monic(self.initial(q)*p), self.monic(self.initial(p)*q)
        else: # different variables are the leader. Two cases:
            vp = lp.infinite_variables()[0]
            vq = lp.infinite_variables()[0]
            if vp == vq: # the same variable --> we need to apply an operator to p
                ip = vp.index(lp, as_tuple=True)
                iq = vp.index(lq, as_tuple=True)
                try:
                    for i in range(len(ip)):
                        p = p.operation(i, times=iq[i]-ip[i]) # this must be always be positive
                except ValueError:
                    raise TypeError("[ranking] Impossible condition reached: inverse operation from 'l(p)' to 'l(q)' when 'p < q'")
                return self.smallest(p,q) # we repeat with the changed `p`
            else: # different variables: we multiply `p` by `vq` and apply again
                return self.smallest(vq*p, q)

    def S(self, p: DPolynomial, q: DPolynomial) -> DPolynomial:
        r'''Computes the S-polynomial of two d-polynomials for the given ranking'''
        sp, sq = self.smallest(p, q)
        return sp - sq

    def monic(self, p: DPolynomial) -> DPolynomial:
        r'''Return a d-polynomial where the biggest monomial has coefficient 1'''
        mon = p.parent().one()
        for m in p.monomials():
            mon = m if self.compare(mon, m) < 0 else mon

        return p // p.coefficient(mon)

    ################################################################################
    ### Sorting methods
    ################################################################################
    def __merge(self, left, right):
        # If the first array is empty, then nothing needs
        # to be merged, and you can return the second array as the result
        if len(left) == 0:
            return right

        # If the second array is empty, then nothing needs
        # to be merged, and you can return the first array as the result
        if len(right) == 0:
            return left

        result = []
        index_left = index_right = 0

        # Now go through both arrays until all the elements
        # make it into the resultant array
        while len(result) < len(left) + len(right):
            # The elements need to be sorted to add them to the
            # resultant array, so you need to decide whether to get
            # the next element from the first or the second array
            if self.compare(left[index_left],right[index_right]) <= 0:
                result.append(left[index_left])
                index_left += 1
            else:
                result.append(right[index_right])
                index_right += 1

            # If you reach the end of either array, then you can
            # add the remaining elements from the other array to
            # the result and break the loop
            if index_right == len(right):
                result.extend(left[index_left:])
                break

            if index_left == len(left):
                result.extend(right[index_right:])
                break

        return result

    def sort(self, elements: list[DPolynomial], reverse: bool = False) -> list[DPolynomial]:
        r'''
            Method to sort a list of d-polynomials following a ranking.

            This method allows to sort a list of d-polynomials using the leader as the main
            sorting key and, in case of a tie, we will use the recursive use of ranking
            into the initial of the d-polynomial.

            This is an implementation of Merge-sort (see :wiki:`Merge_sort`).

            INPUT:

            * ``elements``: list of d-polynomials to be sorted.
            * ``reverse``: a boolean indicating if we want the first element to be the biggest (``True``)
              or the smallest (``False`` - default).
        '''
        # Base case when the list is empty or with just 1 element
        if len(elements) <= 1:
            return elements
        middle = len(elements)//2
        left, right = self.sort(elements[:middle]), self.sort(elements[middle:])

        result = self.__merge(left, right)
        if reverse:
            result.reverse()
        return result

    ################################################################################
    ### Representation and Python-magic methods
    ################################################################################
    def __repr__(self) -> str:
        return f"Ranking over {self.parent()} where [{' < '.join([repr(el) for el in self.__ordering])}]"

    def _latex_(self) -> str:
        return r"\mathbf{Ranking}(" + "<".join(latex(v) for v in self.__ordering) + r")"
    
    def __hash__(self) -> int:
        return hash((self.parent(), self.__ordering, self.__order_operators))

class EliminationRanking(RankingFunction):
    r'''
        Class for representing an Elimination Ranking.

        See :class:`RankingFunction`for information about rankings. Since this is an elimination ranking, then it holds (for 
        the ordered variables) that `u < v` implies `\sigma^\alpha(u) < \sigma^\beta(v)` for all `\alpha,\beta\in \mathbb{N}^n`.

        This class implements a new version for :func:`RankingFunction.compare_variables`.

        TODO: add examples
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, ordering: (list | tuple)[DMonomialGen | str], order_operators: (list | tuple)[int] = None):
        super().__init__(parent, ordering, order_operators)

    def compare_variables(self, u: DPolynomial, v: DPolynomial):
        u, v = self.parent()(u), self.parent()(v)
        if not u.is_variable():
            raise TypeError(f"[ranking @ variables] Comparing something that is not a variable: [[{u} < {v}]]?")
        if not v.is_variable():
            raise TypeError(f"[ranking @ variables] Comparing something that is not a variable: [[{u} < {v}]]?")

        gu, gv = u.infinite_variables()[0], v.infinite_variables()[0]
        if (gu not in self.ordering or gv not in self.ordering):
            raise ValueError(f"[ranking @ variables] Comparing a variable that is not ordered (allow {self.ordering}): [[{u} < {v}]]?")

        if self.ordering.index(gu) < self.ordering.index(gv):
            return -1
        elif self.ordering.index(gu) > self.ordering.index(gv):
            return 1
        else:
            return self.compare_operations(gu.index(u, True), gu.index(v, True))

    ################################################################################
    ### Representation and Python-magic methods
    ################################################################################
    def __repr__(self) -> str:
        return f"ELIMINATION " + super().__repr__()

    def _latex_(self) -> str:
        return r"\mathbf{ElimR}(" + "<".join(latex(v) for v in self.ordering) + r")"

class OrderlyRanking(RankingFunction):
    r'''
        Class for representing an Orderly Ranking.

        See :class:`RankingFunction`for information about rankings. Since this is an elimination ranking, then it holds (for 
        the ordered variables) that `\sigma^\alpha(u) < \sigma^\beta(v)` for all `\alpha,\beta \in \mathbb{N}^n` with `|\alpha| < |\beta|`.

        This class implements a new version for :func:`RankingFunction.compare_variables`.

        TODO: add examples
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, ordering: (list | tuple)[DMonomialGen | str], order_operators: (list | tuple)[int] = None):
        super().__init__(parent, ordering, order_operators)

    def compare_variables(self, u: DPolynomial, v: DPolynomial):
        u, v = self.parent()(u), self.parent()(v)
        if not u.is_variable():
            raise TypeError(f"[ranking @ variables] Comparing something that is not a variable: [[{u} < {v}]]?")
        if not v.is_variable():
            raise TypeError(f"[ranking @ variables] Comparing something that is not a variable: [[{u} < {v}]]?")

        gu, gv = u.infinite_variables()[0], v.infinite_variables()[0]
        if (gu not in self.ordering or gv not in self.ordering):
            raise ValueError(f"[ranking @ variables] Comparing a variable that is not ordered (allow {self.ordering}): [[{u} < {v}]]?")

        ord_u, ord_v = u.order(gu), v.order(gv)
        if ord_u < ord_v:
            return -1
        elif ord_u > ord_v:
            return 1
        else:
            check_in_order = self.compare_operations(gu.index(u, True), gv.index(v, True))
            if check_in_order == 0:
                return self.compare_gens(gu,gv)
            return check_in_order

    ################################################################################
    ### Representation and Python-magic methods
    ################################################################################
    def __repr__(self) -> str:
        return f"ORDERLY " + super().__repr__()

    def _latex_(self) -> str:
        return r"\mathbf{OrdR}(" + "<".join(latex(v) for v in self.ordering) + r")"

__all__ = [
    "DPolynomialRing", "DifferentialPolynomialRing", "DifferencePolynomialRing", "is_DPolynomialRing", # names imported
    "RWOPolynomialRing", "is_RWOPolynomialRing" # deprecated names (backward compatibilities)
]