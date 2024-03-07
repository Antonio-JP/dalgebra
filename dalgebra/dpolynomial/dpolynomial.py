from __future__ import annotations

import logging

from itertools import product

from sage.all import (cached_method, ZZ, latex, diff, Parent, parent, SR, vector)
from sage.categories.all import Morphism, Category, Sets
from sage.categories.monoids import Monoids
from sage.categories.morphism import SetMorphism # pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.rings.ring import Ring #pylint: disable=no-name-in-module
from sage.sets.family import LazyFamily
from sage.structure.element import Element, Matrix #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

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
                try: el[i] = ZZ(part) 
                except: pass
            return tuple(el)

        names = tuple(sorted(names, key=_name_sorting_criteria))

        # We check now whether the base ring is valid or not
        if not base in _DRings:
            raise TypeError("The base ring must have operators attached")

        # Now the names are appropriate and the base is correct
        return (base, names)

    def create_object(self, _, key) -> DPolynomialRing_Monoid:
        base, names = key

        return DPolynomialRing_Monoid(base, names)

DPolynomialRing = DPolynomialRingFactory("dalgebra.dpolynomial.dpolynomial.DPolynomialRing_Monoid")
RWOPolynomialRing = DPolynomialRing #: alias for DPolynomialRing_Monoid (used for backward compatibility)
def DifferentialPolynomialRing(base, *names : str, **kwds) -> DPolynomialRing_Monoid:
    if not base in _DRings:
        base = DifferentialRing(base, kwds.pop("derivation", diff))
    if not base.is_differential():
        raise TypeError("The base ring must be a differential ring")
    return DPolynomialRing(base, *names, **kwds)
def DifferencePolynomialRing(base, *names : str, **kwds) -> DPolynomialRing_Monoid:
    if not base in _DRings:
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

        if not isinstance(input, dict): raise TypeError("[DPolynomial] Incorrect type for input")
        if any(not isinstance(k, DMonomial) for k in input): raise TypeError("[DPolynomial] The keys for a DPolynomial must be DMonomials")
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
        if variables == None:
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
    def monomials(self) -> tuple[DMonomial]:
        r'''
            Method to get a tuple of the monomials appearing in ``self``.
        '''
        return tuple(self._content.keys())
    
    @cached_method
    def coefficients(self) -> tuple[Element]:
        r'''
            Return a list of elements in the ``self.parent().base()`` of the coefficients.
        '''
        return tuple([self._content[m] for m in self.monomials()])
    
    def coefficient(self, monomial: DMonomial) -> Element:
        r'''Getter for the coefficient structure for a given monomial'''
        return self._content.get(monomial, self.parent().base().zero())

    def coefficient_full(self, monomial: DMonomial) -> DPolynomial:
        r'''Getter for the polynomial of all the elements for which ``monomial`` is part of the monomial'''
        if isinstance(monomial, DPolynomial):
            if not monomial.is_monomial(): raise TypeError(f"If requested with d-polynomial, it must be a monomial")
            monomial = monomial.monomials()[0]

        output = dict()
        for (m,c) in self._content.items():
            if all(m._variables.get(v, -1) == monomial._variables.get(v) for v in monomial._variables):
                output[self.parent().monoids()({v: e for (v,e) in m._variables.items() if (not v in monomial._variables)})] = c
        if len(output) == 0: return self.parent().zero()
        return self.parent().element_class(self.parent(), output)
        
    def constant_coefficient(self) -> Element: #: Method to get the coefficient without variables
        return self.coefficient(())

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
        if (gen is None) and self.parent().ngens() == 1: gen = self.parent().gens()[0]
        if gen is None: raise TypeError("The variable has to be provided")

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
        if (gen is None) and self.parent().ngens() == 1: gen = self.parent().gens()[0]
        if gen is None: raise TypeError("The variable has to be provided")

        return self.lorders(operation)[gen._index]
    
    def degree(self, x=None) -> int:
        if x == None: # general degree is computed
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
        if power == 0: return self.parent().one()
        elif power == 1: return self
        elif power < 0: raise NotImplementedError("Negative powers not allowed")
        else:
            a,A = (self**(power//2 + power%2), self**(power//2))
            return a*A

    def __eq__(self, other) -> bool:
        if isinstance(other, DMonomial):
            return self == self.parent()(other)
        elif isinstance(other, DPolynomial):
            return set(self.monomials()) == set(other.monomials()) and all(self.coefficient(m) == other.coefficient(m) for m in self.monomials())
        return super().__eq__(other)
    
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
    def eval(self, *args, dic : dict = None, **kwds):
        r'''
            Evaluating a DMonomial

            We rely on the variable names of the parent. There are no coercions in this method, it simply computes the corresponding product
            with the corresponding values.
        '''
        if len(args) != 0: 
            if dic != None or len(kwds) != 0:
                raise TypeError("Incorrect format for evaluating a DMonomial")
            kwds.update({self.parent().variable_names()[i] : args[i] for i in range(len(args))})
        elif dic != None:
            if not isinstance(dic, dict): raise TypeError("Invalid type for dictionary evaluating DMonomial")
            kwds.update({v.variable_name() if isinstance(v, DMonomialGen) else str(v) : val for (v,val) in dic.items()})

        ## Changing names to integers
        kwds = {self.parent().variable_names().index(k): v for (k,v) in kwds.items()}

        result = ZZ(0); pp = result.parent()
        for (m, c) in self._content.items():
            ## Evaluating the monomial
            ev_mon = ZZ(1)
            rem_mon = dict()
            for (v,o) in m._variables: 
                if v in kwds:
                    el = kwds[v]; P = el.parent()
                    ev_mon *= P.apply_operations(el, o)
                else:
                    rem_mon[(v,o)] = m._variables[(v,o)]
            rem_mon = self.parent()(self.parent().monoids().element_class(self.parent().monoids(), rem_mon)) if len(rem_mon) > 0 else ZZ(1)
            pp = pushout(pushout(pushout(pp, c.parent()), ev_mon.parent()), rem_mon.parent())
            result = pp(result) + (pp(c)*pp(ev_mon))*pp(rem_mon)
        return result

    def lie_bracket(self, other: DPolynomial, gen: DMonomialGen = None) -> DPolynomial:
        r'''
            Computes the Lie-bracket (or commutator) of ``self`` with other :Class:`DPolynomial`.
        '''
        if not other in self.parent():
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
        power = int(power)
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        else:
            H1 = self.sym_power(power//2 + power % 2, gen)
            H2 = self.sym_power(power//2, gen)
            gen = gen if gen != None else self.parent().gens()[0]
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
        if weight == None:
            return self.as_polynomial().is_homogeneous()
        
        if not isinstance(weight, WeightFunction):
            weight = self.parent().weight_func(*weight)

        return weight.is_homogeneous(self)
    
    ###################################################################################
    ### Ranking methods
    ###################################################################################
    def __check_ranking_argument(self, ranking, ordering=None, ttype="orderly"):
        if ranking == None: ranking = self.parent().ranking()
        elif not isinstance(ranking, RankingFunction): ranking = self.parent().ranking(ordering, ttype)
        return ranking
    
    def monic(self, ranking, ordering=None, ttype="orderly"):
        r'''Method to get the monic polynomial w.r.t. a ranking'''
        return self.__check_ranking_argument(ranking, ordering, ttype).monic(self)

    def leader(self, ranking=None, ordering=None, ttype="orderly"):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        return self.__check_ranking_argument(ranking,ordering,ttype).leader(self)
    
    def rank(self, ranking=None, ordering=None, ttype="orderly"):
        r'''
            Gets the rank of ``self`` w.r.t. a ranking.
        '''
        return self.__check_ranking_argument(ranking,ordering,ttype).rank(self)
    
    def initial(self, ranking=None, ordering=None, ttype="orderly"):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        return self.__check_ranking_argument(ranking,ordering,ttype).initial(self)
    
    def separant(self, ranking=None, ordering=None, ttype="orderly"):
        r'''
            Gets the leader of ``self`` w.r.t. a ranking.
        '''
        return self.__check_ranking_argument(ranking,ordering,ttype).separant(self)
    
    ### Some aliases
    lc = initial #: alias for initial (also called "leading coefficient")

    ###################################################################################
    ### Other magic methods
    ###################################################################################
    @cached_method
    def __repr__(self) -> str:
        if self.is_zero(): return "0"
        parts = []
        for (m,c) in sorted(self._content.items(), key=lambda p : p[0]):
            if str(c)[0] == "-": # changing sign
                sign = "-"; c = -c
            else:
                sign = "+"

            par = any(char in str(c) for char in ("+", "*", "-"))            

            if m.is_one(): parts.append((sign, "", f"{'(' if par else ''}{c}{')' if par else ''}"))
            elif c == 1: parts.append((sign, f"{m}", ""))
            else: parts.append((sign, f"{m}", f"{'(' if par else ''}{c}{')' if par else ''}*"))

        output = f"{parts[0][0] if parts[0][0] == '-' else ''}{parts[0][2]}{parts[0][1]}"
        for (sign, m, c) in parts[1:]:
            output += f" {sign} {c}{m}"
        return output
    
    def _latex_(self) -> str:
        return "+".join(r"\left(" + latex(c) + r"\right)" + ('' if m.is_one() else latex(m)) for (m,c) in self._content.items())
    
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
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] + x
    def __radd__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return x + self[0]
    def __neg__(self):
        return -self[0]
    def __sub__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] - x
    def __rsub__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return x - self[0]
    def __mul__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] * x
    def __rmul__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return x * self[0]
    def __lmul__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] * x
    def __mod__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] % x
    def __rmod__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return x % self[0]
    def __div__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] / x
    def __rdiv__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return x / self[0]
    def __floordiv__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
        return self[0] // x
    def __rfloordiv__(self, x):
        if isinstance(x, DPolynomialGen): x = x[0]
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
            a_2*b_0 + a_1*b_1

        Although the use of diff can work in these rings, it is not fully recommended because we may require more 
        information for the ``diff`` method to work properly. We recommend the use of the ``derivative`` methods 
        of the elements or the method ``derivative`` of the Rings (as indicated in the category 
        :class:`dalgebra.dring.DRings`)::

            sage: R.derivative(y[0])
            y_1
            sage: R.derivative(x)
            1
            sage: R.derivative(x*y[10])
            x*y_11 + y_10
            sage: R.derivative(x^2*y[1]^2 - y[2]*y[1])
            -y_3*y_1 - y_2^2 + 2*x^2*y_2*y_1 + 2*x*y_1^2
            sage: (x*y[10]).derivative()
            x*y_11 + y_10

        This derivation also works naturally with several infinite variables::

            sage: S.derivative(a[1] + b[0]*a[0])
            a_1*b_0 + a_0*b_1 + a_2
            sage: (a[3]*a[1]*b[0] - b[2]).derivative()
            a_4*a_1*b_0 + a_3*a_2*b_0 + a_3*a_1*b_1 - b_3

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
            -y_3*y_2 + x^2*y_2^2

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
            x + 1
            sage: T.difference(x^2*z[1]^2 - z[2]*z[1])
            -z_3*z_2 + (x^2 + 2*x + 1)*z_2^2

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
            u_0_2_1*v_0_1_0 + u_0_1_1*v_0_2_0
            sage: (u[5]*v[0,1,0]).derivative(1) - u[0,1,0].shift()*v[0,2,0]
            u_0_2_1*v_0_1_0
    '''
    Element = DPolynomial

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Monoids.Algebras(base)] + ([category] if category != None else [])

    def __init__(self, base : Parent, names : Collection[str], category=None):
        if not base in _DRings:
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
    def gen(self, i: int|str = None):
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
    
    def term(self, index: DMonomial, coeff: Element=None):
        if not isinstance(index, DMonomial):
            try:
                index = self.monoids()(index)
            except TypeError:
                index = self.monoids().semigroup_generators()[index]
        return self.element_class(self, {index : coeff if coeff != None else self.base().one()})

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S: Parent) -> bool:
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        if S == self.monoids(): return True
        coer =  self._coerce_map_from_(S)
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
            if isinstance(x, str): x = SR(x)
            if x in SR: x = SR(x)

            variables = x.variables()

            ## Splitting variables into normal variables and other variables
            inner_variables = []; outer_variables = []; var_and_order = dict()
            for v in variables:
                for (i,g) in enumerate(self.gens()):
                    if v in g:
                        outer_variables.append(v)
                        var_and_order[v] = (i, g.index(v))
                        break
            else: inner_variables.append(v)

            ## We check the object is a polynomial in the outer variables
            if any(not x.is_polynomial(v) for v in outer_variables): 
                raise ValueError(f"The input is not a polynomial: {x}")
            ## We check if the inner variables are in the base ring
            if any(not v in self.base() for v in inner_variables):
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
            if other.ngens() <= self.ngens(): return self
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
                sage: R.flatten(f1)
                u_2*x^2 + u_0*x + v_0*x - v_0
                sage: R.flatten(f1).parent()
                Multivariate Polynomial Ring in u_2, u_1, u_0, v_2, v_1, v_0, x over Rational Field

            This method works with more complicated ring with operators. It is interesting to remark that the subindex of the 
            infinite variables (when having several operators) collapse to one number following the rules as in 
            :class:`IndexBijection`::

                sage: B.<x,ex,l,m,e> = QQ[]
                sage: dx,dex,dl,dm,de = B.derivation_module().gens()
                sage: shift = B.Hom(B)([x+1, e*ex, l, m, e])
                sage: DSB = DifferenceRing(DifferentialRing(B, dx + ex*dex), shift); x,ex,l,m,e = DSB.gens()
                sage: R.<u,v> = DPolynomialRing(DSB)
                sage: f1 = u[1,0]*ex + (l-1)*v[0,1]*x - m; f1
                ex*u_1_0 + (x*l - x)*v_0_1 - m
                sage: f1.polynomial()
                ex*u_2 + (x*l - x)*v_1 - m
                sage: f1.derivative()
                ex*u_2_0 + ex*u_1_0 + (x*l - x)*v_1_1 + (l - 1)*v_0_1
                sage: f1.derivative().polynomial()
                ex*u_5 + ex*u_2 + (x*l - x)*v_4 + (l - 1)*v_1
                sage: R.flatten(f1.derivative())
                v_4*x*l - v_4*x + u_5*ex + u_2*ex + v_1*l - v_1
                sage: R.flatten(f1.derivative()).parent()
                Multivariate Polynomial Ring in u_5, u_4, u_3, u_2, u_1, u_0, v_5, v_4, v_3, v_2, v_1, v_0, x, ex, l, m, e over Rational Field

            We remark that we can reconstruct the original polynomial from the flattened version::

                sage: R(R.flatten(f1.derivative())) == f1.derivative()
                True
                sage: R(R.flatten(f1)) == f1
                True
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

    def remove_variables(self, *variables: str|DMonomialGen) -> DPolynomialRing_Monoid:
        r'''
            Method that removes d-variables from the ring of d-polynomials and guarantees the conversion between structures.
            If all variables are removed, we return the base d-ring.

            INPUT:

            * ``variables``: list of names to be removed. If any name is not is ``self``, we ignore it.

            EXAMPLE::

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
                ValueError: Impossible to convert element a_2*b_0+(-1)*c_1^2 from ...
                sage: pp = a[3] + 3*a[2] + 3*a[1] + a[0]
                sage: Ra(pp)
                (3)*a_1 + (3)*a_2 + a_3 + a_0
                sage: R(Ra(pp)) == pp
                True
        '''
        variables = set([v._name if isinstance(v, DMonomialGen) else str(v) for v in variables])
        rem_variables = [v_name for v_name in self.variable_names() if (not v_name in variables)]
        if len(rem_variables) == 0: # all removed
            return self.base()
        elif len(rem_variables) == self.ngens(): # nothing removed
            return self
        else: # some intermediate ring
            ## We create the new ring
            output = DPolynomialRing(self.base(), rem_variables)
            ## We guarantee the conversion/coercion between structures
            self.register_coercion(DPolynomialVariableMorphism(output, self))
            output.register_conversion(DPolynomialSimpleMorphism(self, output))

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
    # def __call__(self, *args, **kwds) -> DPolynomial:
    #     res = super().__call__(*args, **kwds)
    #     if not isinstance(res, self.element_class):
    #         res = self.element_class(self, res)
    #     return res

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
        deg_bound = 0 if ((not deg_bound in ZZ) or deg_bound < 0) else deg_bound
        order_bound = 0 if ((not order_bound in ZZ) or order_bound < 0) else order_bound

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
                Multivariate Polynomial Ring in c_2, a_2_1, a_1_2, a_2_0, c_3 over Differential Ring [[Rational Field], (0,)]
                sage: qq
                -c_2*a_2_0 + 3*a_1_2

        '''
        variables = set()
        for element in elements:
            variables.update(self(element).variables())
        # This sort the variables first by index (i.e., alphabetically) then by order
        variables = sorted(variables, key = lambda p : tuple(next(iter(p._content))._variables.items())[0])

        PR = PolynomialRing(self.base(), [str(v) for v in variables], sparse=True)
        result = [PR(str(element)) for element in elements] # TODO: This may be improved?

        return result

    def eval(self, element, *args, dic: dict[DMonomialGen,DPolynomial] = None, **kwds):
        r'''
            Method to evaluate elements in the ring of differential polynomials.

            Since the infinite polynomials have an intrinsic meaning (namely, the 
            variables are related by the operator), evaluating a polynomial
            is a straight-forward computation once the objects for the ``*_0`` term is given.

            This method evaluates elements in ``self`` following that rule.

            REMARK: **this method can be used to compose operator polynomials**. In the case 
            where we have an operator polynomial `p(u) \in R\{u\}` (for `R` a ring with operators) 
            we can interpret the polynomial `p(u)` as an operator over any extension of `R` that acts
            by substituting `u` by the element the operator acts on.

            In the case of linear operators, we can define a non-commutative product over these operators
            and this method eval can be used to compute such multiplication (see examples below).

            INPUT:

            * ``element``: element (that must be in ``self``) to be evaluated
            * ``args``: list of arguments that will be linearly related with the generators
              of ``self`` (like they are given by ``self.gens()``)
            * ``dic``: dictionary mapping generators to polynomials. This allows an input equivalent to 
              the argument in ``kwds`` but where the keys of the dictionary are :class:`DPOlynomialGen`.
            * ``kwds``: dictionary for providing values to the generators of ``self``. The 
              name of the keys must be the names of the generators (as they can be got using 
              the attribute ``_name``).

            We allow a mixed used of ``args`` and ``kwds`` but an error will be raised if

            * There are too many arguments in ``args``,
            * An input in ``kwds`` is not a valid name of a generator,
            * There are duplicate entries for a generator.

            OUTPUT:

            The resulting element after evaluating the variable `\alpha_{(i_1,...,i_n)} = (d_1^{i_1} \circ ... \circ d_n^{i_n})(\alpha)`,
            where `\alpha` is the name of the generator.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: R.eval(y[1], 0)
                0
                sage: R.eval(y[0] + y[1], x)
                x + 1
                sage: R.eval(y[0] + y[1], y=x)
                x + 1

            This method always commutes with the use of :func:`operation`::

                sage: R.eval(R.derivative(x^2*y[1]^2 - y[2]*y[1]), y=x) == R.derivative(R.eval(x^2*y[1]^2 - y[2]*y[1], y=x))
                True

            This evaluation also works naturally with several infinite variables::

                sage: S = DifferentialPolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.eval(a[1] + y[0]*a[0], a=x, y=x^2)
                x^3 + 1
                sage: in_eval = S.eval(a[1] + y[0]*a[0], y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of operator polynomials in (a) over Differential Ring [[Univariate Polynomial Ring in x over Rational Field], (d/dx,)]

            As explained earlier, we can use this method to compute the product as operator of two linear operators::

                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: p1 = y[2] - (x^2 - 1)*y[1] + y[0]; op1 = p1.as_linear_operator()
                sage: p2 = x*y[1] - 3*y[0]; op2 = p2.as_linear_operator()
                sage: p1(y=p2) == R(op1*op2)
                True

            As expected, similar behavior occurs when having several operators in the ring::

                sage: T.<u> = DPolynomialRing(DifferenceRing(DifferentialRing(QQ[x],diff), QQ[x].Hom(QQ[x])(QQ[x](x)+1))); x = T.base()(x)
                sage: p3 = 2*u[0,0] + (x^3 - 3*x)*u[1,0] + x*u[1,1] - u[2,2]; op3 = p3.as_linear_operator()
                sage: p4 = u[0,1] - u[0,0]; op4 = p4.as_linear_operator()
                sage: p3(u=p4) == T(op3*op4)
                True
                sage: p3(u=p4) - p4(u=p3) == T(op3*op4 - op4*op3) # computing the commutator of the two operators
                True

            This can also work when having several infinite variables (in contrast with the method :func:`as_linear_operator`)::

                sage: U.<a,b> = DifferentialPolynomialRing(QQ[x]); x = U.base()(x)
                sage: p5 = a[0] + b[1]*(b[0]^2 - x^2)*a[1]; p5.is_linear(a)
                True
                sage: p6 = x*a[1] - b[0]*a[0]; p6.is_linear(a)
                True
                sage: p5(a=p6) - p6(a=p5) # commutator of p5 and p6 viewed as operators w.r.t. a
                -a_0*b_1^2*b_0^2 + (-x)*a_1*b_2*b_0^2 + (-2*x)*a_1*b_1^2*b_0 + a_1*b_1*b_0^2 + x^2*a_0*b_1^2 + x^3*a_1*b_2 + x^2*a_1*b_1
        '''
        ### Combining the arguments from dic and kwds
        if dic != None:
            for k,v in dic.items():
                if isinstance(k, DMonomialGen):
                    kwds[k.variable_name()] = v
                else:
                    kwds[str(k)] = v

        ### Checking the element is in self
        if(not element in self):
            raise TypeError("Impossible to evaluate %s as an element of %s" %(element, self))
        element = self(element) # making sure the structure is the appropriate

        ### Checking the input that needs to be evaluated
        gens : tuple[DMonomialGen] = self.gens()
        names : list[str] = [el._name for el in gens]
        if(len(args) > self.ngens()):
            raise ValueError(f"Too many argument for evaluation: given {len(args)}, expected (at most) {self.ngens()}")

        final_input : dict[DMonomialGen, Element] = {gens[i] : args[i] for i in range(len(args))}
        other_input : dict = dict()
        for key in kwds:
            if(not key in names):
                other_input[key] = kwds[key]
            else:
                gen = gens[names.index(key)]
                if(gen in final_input):
                    raise TypeError(f"Duplicated value for generator {gen}")
                final_input[gen] = kwds[key]

        ### Deciding final parent
        rem_names = [name for (name,gen) in zip(names,gens) if gen not in final_input]
        R = DPolynomialRing(self.base(), rem_names) if len(rem_names) > 0 else self.base()
        for value in final_input.values():
            R = pushout(R, parent(value))
        
        final_input = {key : R(value) for key,value in final_input.items()} # updating input to the output ring
        logger.debug(f"[eval] This is the final input for the polynomial: {final_input}")

        ### Building the elements to be used in evaluation
        evaluation_dict = {}
        for variable in element.variables():
            logger.debug(f"[eval] Checking variable {variable}")
            for gen in gens:
                logger.debug(f"[eval] Checking if {variable} in {repr(gen)}")
                
                if variable in gen: # we found the generator of this variable
                    logger.debug(f"[eval] Found generator {repr(gen)} for variable {variable}")
                    operations = gen.index(variable)
                    if gen in final_input:
                        if self.noperators() == 1:
                            value = final_input[gen].operation(times=operations)
                        else:
                            value = final_input[gen]
                            for (i, times) in enumerate(operations):
                                value = value.operation(operation=i, times=times)
                        try:
                            to_add = R(value)
                        except:
                            to_add = R(str(value))
                        logger.debug(f"[eval] Adding value: '{str(variable)}': {to_add}")
                        evaluation_dict[str(variable)] = to_add
                    else:
                        try:
                            to_add = R(gen[operations])
                        except:
                            to_add = R(str(gen[operations]))
                        logger.debug(f"[eval] Adding variable: '{str(variable)}': {to_add}")
                        evaluation_dict[str(variable)] = to_add
                    break
        # extending the dictionary to all variables in element.polynomial().
        variable_names = [str(v) for v in element.variables()]
        for variable in element.polynomial().parent().variable_names():
            if not variable in variable_names: # only those that do not appear
                evaluation_dict[variable] = R.zero() # we can add anything here, since they do not show up

        evaluation_dict.update(other_input)
        logger.debug(f"[eval] Final evaluation performed:\n\t**DICT={evaluation_dict}\n\t**POLY={element.polynomial()}")

        return R(element.polynomial()(**evaluation_dict))
        
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
                
                if(not element in self.__cache[operation]):
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
                
                if(not element in self.__cache[operation]):
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
        if not element in self:
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
        logger.debug(f"[inverse_derivation] Called with {element}")
        if element == 0:
            logger.debug(f"[inverse_derivation] Found a zero --> Easy")
            solution = self.zero()
        elif element.degree() == 1:
            logger.debug(f"[inverse_derivation] Found linear element --> Easy to do")
            solution = self.zero()
            for monomial, coeff in element._content.items():
                if monomial.is_one():
                    raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {monomial}")
                coeff = coeff.inverse_operation(operation) if not coeff.d_constant() else coeff
                var = next(iter(monomial.variables())) # we know there is only 1, since the element is linear
                new_mon = self(var._inverse_(operation))
                solution += coeff*new_mon
        else:
            logger.debug(f"[inverse_derivation] Element is not linear")
            monomials = element.monomials()
            if 1 in monomials:
                raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {element}")
            monomials_with_points = []
            for mon in monomials:
                bv = max(k[0] for k in mon._variables) # index of the maximum variable
                bo = mon.order(bv, operation) # order of the biggest variable w.r.t. operation
                monomials_with_points.append((bv, bo))

            aux = max(o for (_,o) in monomials_with_points) # element with highest order -> used as a balance option to use "max"
            V, O = max(monomials_with_points, key = lambda p: p[0]*aux + p[1])
            V = self.gens()[V]
            logger.debug(f"[inverse_derivation] Maximal variable: {V[O]}")
            
            if element.degree(V[O]) > 1:
                raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {element}")
            else:
                highest_part = element.coefficient_full(V[O]); deg_order_1 = highest_part.degree(V[O-1])
                cs = [highest_part.coefficient_full(V[O-1]**i) for i in range(deg_order_1+1)]
                order_1_part = sum(cs[i]*V[O-1]**i for i in range(deg_order_1+1))
                q1 = highest_part - order_1_part # order q1 < d-1
                
                ## we compute remaining polynomial
                partial_integral = sum(cs[i]/ZZ(i+1) * V[O-1]**(i+1) for i in range(deg_order_1+1)) + V[O-1]*q1 # division is on coeff. level

            logger.debug(f"[inverse_derivation] Partial integral: {partial_integral}")
            rem = element - partial_integral.operation(operation)
            logger.debug(f"[inverse_derivation] Remaining to integrate: {rem}")
            solution = partial_integral + self.inverse_operation(rem, operation)
            
        logger.debug(f"[inverse_derivation] Result: {solution}")
        return solution
   
    def __inverse_skew(self, element: DPolynomial, operation: int):
        raise NotImplementedError("[inverse_skew] Skew-derivation operation not yet implemented")
            
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
                x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19

            If several variables are available, we need to explicitly provide the variable we are considering::

                sage: R.<u,v> = DPolynomialRing(B)
                sage: P = (3*x -1)*u[0]*v[0] + x^2*v[1]*u[0] + u[2]
                sage: Q = 7*x*v[0] + x^2*v[0]*u[1]
                sage: P.sylvester_resultant(Q)
                Traceback (most recent call last):
                ...
                ValueError: [sylvester_checking] No infinite variable provided but several available.
                sage: P.sylvester_resultant(Q, u)
                x^6*v_1*v_0^2 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, v)
                x^2*u_1 + 7*x

            The infinite variable can also be given as an index::

                sage: P.sylvester_resultant(Q, 0)
                x^6*v_1*v_0^2 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, 1)
                x^2*u_1 + 7*x
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
                -3*x^3 - 3*x^2 + 3*x + 2
                sage: S.sylvester_subresultant(P, Q, k=1, i=1)
                8*x^2 + 7*x

            We can see that the case with `k=0` and `i=0`coincides with the method :func:`sylvester_resultant`::
            
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant(P, Q, k=0, i=0) == P.sylvester_resultant(Q)
                True
        '''
        ## Checking the argument `i`
        if not i in ZZ:
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
                [      x^2 - 1          -3*x             1             0             0]
                [            0     x^2 + 2*x      -3*x - 3             1             0]
                [            0             0 x^2 + 4*x + 3      -3*x - 6             1]
                [           -1             0             0             1             0]
                [            0            -1             0             0             1]
                sage: P.sylvester_matrix(Q, k=1)
                [      x^2 - 1          -3*x             1             0]
                [            0     x^2 + 2*x      -3*x - 3             1]
                [           -1             0             0             1]

            It is important to remark that this matrix depends directly on the operation defined on the ring::

                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_matrix(Q)
                [x^2 - 1    -3*x       1       0       0]
                [    2*x x^2 - 4    -3*x       1       0]
                [      2     4*x x^2 - 7    -3*x       1]
                [     -1       0       0       1       0]
                [      0      -1       0       0       1]
                sage: P.sylvester_matrix(Q,k=1)
                [x^2 - 1    -3*x       1       0]
                [    2*x x^2 - 4    -3*x       1]
                [     -1       0       0       1]

            However, the Sylvester matrix is not well defined when the ring has several operations::

                sage: B = DifferentialRing(DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)), diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[0,2] - 3*x*z[0,1] + (x^2 - 1)*z[1,0]
                sage: Q = z[2,3] - z[1,0]
                sage: P.sylvester_matrix(Q)
                Traceback (most recent call last):
                ...
                NotImplementedError: [sylvester_checking] Sylvester resultant with 2 is not implemented
        '''
        # ## Checking the polynomials and ring arguments
        # P,Q,gen = self.__process_sylvester_arguments(P,Q,gen)
        
        # ## Checking the k argument
        # n = P.order(gen); m = Q.order(gen); N = min(n,m) - 1
        # # Special case when one of the orders is -1 (i.e., the variable `gen` is not present)
        # if n == -1:
        #     return matrix([[P]]) # P does not contain the variable `gen` to eliminate
        # elif m == -1:
        #     return matrix([[Q]]) # Q does not contain the variable `u` to eliminate
        
        # if not k in ZZ:
        #     raise TypeError(f"[sylvester_matrix] The index {k = } is not an integer.")
        # elif N == -1 and k != 0:
        #     raise TypeError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0].")
        # elif N >= 0 and (k < 0 or k > N):
        #     raise ValueError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0,...,{N}]")
        
        # part_without_gen = lambda Poly : sum(c*m for (c,m) in zip(Poly.coefficients(), Poly.monomials()) if m.order(gen._index) == -1)
        # homogeneous = any(part_without_gen(poly) != 0 for poly in (P,Q))

        # if homogeneous and k > 0:
        #     raise NotImplementedError(f"[sylvester_matrix] The case of inhomogeneous operators and positive {k=} is not implemented.")

        # extra = 1 if homogeneous else 0
        # logger.info(f"Sylvester data: {n=}, {m=}, {k=}, {homogeneous=}")

        # # Building the extension
        # extended_P: list[DPolynomial] = [P.operation(times=i) for i in range(m-k+extra)]
        # extended_Q: list[DPolynomial] = [Q.operation(times=i) for i in range(n-k+extra)]

        # # Building the Sylvester matrix (n+m-1-k) , (n+m-1-k)
        # fR = self.polynomial_ring() # guaranteed common parent for all polynomials
        # cols = [fR(gen[pos].polynomial()) for pos in range(n+m-k+extra)]
        # equations = [fR(equation.polynomial()) for equation in extended_P + extended_Q]

        # # Returning the matrix
        # output = matrix([([part_without_gen(self(equation))] if homogeneous else []) + [self(equation.coefficient(m)) for m in cols] for equation in equations])
        # logger.info(f"Obtained following matrix:\n{output}")
        # return output
        raise NotImplementedError(f"Method need revisiting")

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
                ((x^6 + 6*x^5 + 10*x^4 - 18*x^3 - 65*x^2 - 42*x - 2)*z_0, (8*x^2 + 7*x)*z_1 + (-3*x^3 - 3*x^2 + 3*x + 2)*z_0)
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant_sequence(P, Q)
                ((x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19)*z_0, (8*x^2 + 4)*z_1 + (-3*x^3 + x - 1)*z_0)
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
        elif isinstance(gen, DMonomialGen) and not gen in self.gens():
            raise ValueError(f"[sylvester_checking] The variable {repr(gen)} do not belong to {self}")
        elif self.ngens() == 1 and gen is None:
            gen = self.gens()[0]

        ## Checking the operator polynomials are correct
        P = self(P); Q = self(Q)
        if not P.is_linear(gen):
            raise TypeError(f"[sylvester_checking] The polynomial {P} is not linear w.r.t. {gen}")
        if not Q.is_linear(gen):
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
        if ordering != None and isinstance(ordering, list): ordering = tuple(ordering)
        if not (ordering, ttype) in self.__cache_ranking:
            self.__cache_ranking[(ordering, ttype)] = RankingFunction(self, ordering, ttype)
        return self.__cache_ranking[(ordering, ttype)]

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
                sage: p1.as_linear_operator()
                D^2 + (-x^2 + 1)*D - 1
                sage: R(p1.as_linear_operator()) == p1
                True
                
            If the operator polynomial is not linear or has a constant term, this method raises a :class:`TypeError`::

                sage: p2 = x*y[2]*y[0] - (x^3 + 3)*y[1]^2 # non-linear operator
                sage: p2.as_linear_operator()
                Traceback (most recent call last):
                ...
                TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.
                sage: p3 = y[2] - (x^2 - 1)*y[1] - y[0] + x^3 # linear operator but inhomogeneous
                sage: p3.as_linear_operator()
                Traceback (most recent call last):
                ...
                TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.

            This also work when having several operators in the same ring::

                sage: S.<u> = DPolynomialRing(DifferenceRing(DifferentialRing(QQ[x], diff), QQ[x].Hom(QQ[x])(QQ[x](x)+1))); x = S.base()(x)
                sage: p4 = 2*u[0,0] + (x^3 - 3*x)*u[1,0] + x*u[1,1] - u[2,2] 
                sage: p4.as_linear_operator()
                -D^2*S^2 + x*D*S + (x^3 - 3*x)*D + 2
                sage: S(p4.as_linear_operator()) == p4
                True

            However, when having several infinite variables this method can not work even when the operator is clearly linear::

                sage: T.<a,b> = DifferentialPolynomialRing(QQ[x]); x = T.base()(x)
                sage: p5 = a[0] - b[1]
                sage: p5.as_linear_operator()
                Traceback (most recent call last):
                ...
                NotImplementedError: Impossible to generate ring of linear operators with 2 variables

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
        self.rank = 12 # just above PolynomialRing and DRingFunctor and DExtension
        
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
            if any(p.order(self.domain().gen(i)) >= 0 for i in range(self.domain().ngens()) if not i in self.__map_vars): # this variable appears
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
    def __init__(self, dpoly_ring: DPolynomialRing_Monoid, base_weights: list[int] | tuple[int] | dict[str|DMonomialGen, int], operator_weights: list[int] |tuple[int]):
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
                {b_0_0, a_0_1}
                sage: w.weighted_variables(3)
                {b_0_1, a_1_0, a_0_2}
                sage: w.weighted_variables(4)
                {b_1_0, b_0_2, a_1_1, a_0_3}
                sage: w.weighted_variables(5)
                {b_1_1, b_0_3, a_2_0, a_1_2, a_0_4}
                sage: w.weighted_variables(6)
                {b_2_0, b_1_2, b_0_4, a_2_1, a_1_3, a_0_5}
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                sage: w = R.weight_func([1,3],[1,1])
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
        '''
        if weight <= 0: return set()
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
                    cweight = weight - op_weight; i = 1
                    while cweight >= 0:
                        logger.debug(f"Adding shifts of monomials of weights {cweight} with degree {i}")
                        to_add += sum((tuple(self.parent()(m) for m in operator(mon).monomials()) for mon in self.homogeneous_monomials(cweight) if mon.degree() == i), tuple())
                        i += 1; cweight -= op_weight
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
                if not v in added:
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
    
        In particular, we say that a ranking `\leq` of `(R,(\sigma_1,\ldots,\sigma_n))\{u_1,\ldots,u_m\}` is an elimination ranking 
        between two d-variables `u, v` (say `u < v`) if they satisfy `\sigma^\alpha(u) < \sigma^\beta(v)` for all `\alpha,\beta\in \mathbb{N}^n`.

        We also say that `\leq` of `(R,(\sigma_1,\ldots,\sigma_n))\{u_1,\ldots,u_m\}` is an orderly ranking on `u_1,\ldots, u_n` if 
        `\sigma^\alpha(u_i) < \sigma^\beta(u_j)` for all `\alpha,\beta \in \mathbb{N}^n` with `|\alpha| < |\beta|`.
        
        Once a ranking is fully define, the following methods are automatically defined for non-constant d-polynomials:

        * ``leader``: given `p(u) \in R\{u\}`, the leader is the actual variable that is maximal on the polynomial
        * ``rank``: given `p(u) \in R\{u\}`, the rank is the biggest monomial involving the leader variable.
        * ``initial``: given `p(u) \in R\{u\}`, the initial is the coefficient of the rank of the polynomial.
        * ``separant``: given `p(u) \in R\{u\}`, the separant is the derivative of `p(u)` w.r.t. the leader variable.

        INPUT:

        * ``parent``: a :class:`DPolynomialRing_Monoid` where the ranking will be applied.
        * ``ordering``: a list or tuple of :class:`DMonomialGen` that will include the variables of a :class:`DPolynomialRing_Monoid`
          that will be incorporated to the ranking and the base ordering between the base variables.
        * ``ttype``: the type of ranking to be created. Currently, only "elimination" or "orderly" are allowed:
          - "elimination": the ranking will be the elimination ranking where the ``ordering`` determines the order of the variables.
          - "orderly": generates the orderly ranking where ``ordering`` provides the basic ordering between variables.

        TODO: add examples
    '''
    def __init__(self, parent: DPolynomialRing_Monoid, ordering: list[DMonomialGen] | tuple[DMonomialGen] = None, ttype: str = "orderly"):
        ## Processing arguments
        if not isinstance(parent, DPolynomialRing_Monoid):
            raise TypeError(f"[ranking] The parent must be a ring of d-polynomials, but got {type(parent)}")
        if ordering is None:
            ordering = parent.gens()
        elif not isinstance(ordering, (list,tuple)):
            raise TypeError(f"[ranking] The base ordering must be given as a list or tuple of generators, but got {type(ordering)}")
        elif any(g not in parent.gens() for g in ordering):
            raise ValueError(f"[ranking] The base ordering must be given as a list of generators (DMonomialGen) (got {ordering})")
        
        if not ttype in ("elimination", "orderly"):
            raise ValueError(f"[ranking] The type of a ranking must be either 'elimination' or 'orderly'. Got {ttype}")
        
        ## Storing the information required for the ranking function
        self.__parent = parent
        self.base_order : list[DMonomialGen] | tuple[DMonomialGen] = ordering
        self.type : str = ttype

    def parent(self) -> DPolynomialRing_Monoid:
        return self.__parent

    def compare_variables(self, u: DPolynomial, v: DPolynomial):
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
        u = self.parent()(u); v = self.parent()(v)
        if not u.is_variable(): raise TypeError(f"[ranking] Comparing something that is not a variable: [[{u} < {v}]]?")
        if not v.is_variable(): raise TypeError(f"[ranking] Comparing something that is not a variable: [[{u} < {v}]]?")

        gu = None; gv = None
        for g in self.base_order:
            if u in g: gu = g
            if v in g: gv = g
            if gu != None and gv != None: break
        else:
            raise ValueError(f"[ranking] Comparing a variable that is not ordered (allow {self.base_order}): [[{u} < {v}]]?")
        
        if self.type == "elimination":
            if self.base_order.index(gu) < self.base_order.index(gv):
                return -1
            elif self.base_order.index(gu) > self.base_order.index(gv):
                return 1
            else:
                return gu.index(u, False) - gu.index(v, False)
        elif self.type == "orderly":
            ord_u = u.order(gu); ord_v = v.order(gv)
            if ord_u < ord_v: return -1
            elif ord_u > ord_v: return 1
            else:
                ind_u = gu.index(u, False); ind_v = gv.index(v, False)
                if ind_u < ind_v: return -1
                elif ind_u > ind_v: return 1
                else:
                    return self.base_order.index(gu) - self.base_order.index(gv)
        else:
            raise NotImplementedError(f"[ranking] Method 'compare' not yet implemented for type {self.type}")

    def compare(self, p: DPolynomial, q: DPolynomial):
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
        u = self.leader(p); v = self.leader(q)
        # special cases when the leader are 1
        if u == 1 and v == 1:
            return 0
        elif u == 1:
            return -1
        elif v == 1:
            return 1

        # both have a non-constant leader
        cmp_leaders = self.compare_variables(u,v)
        if cmp_leaders != 0: return cmp_leaders

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
        variables = [self.parent()(v) for v in element.variables() if any(v in g for g in self.base_order)]
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

        return element.coefficient(self.rank(element), _poly = True)

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
        return self.parent()(element.polynomial().derivative(max_var.polynomial())) if max_var != self.parent().one() else self.parent().zero()

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
        lp = self.leader(p); lq = self.leader(q)
        original_q = q
        comparison = self.compare_variables(lp, lq)
        if comparison < 0: # impossible condition
            raise TypeError("[ranking] Impossible condition reached: 'l(p) < l(q) when p > q'")
        elif comparison == 0: # same leader --> we need to multiply by the leader to match degrees
            a = lp**(q.degree(lp)-p.degree(lp)) * self.initial(q)
            b = {tuple(N*[0]): (self.initial(p), 1)}
            r = a*p - self.initial(p)*q
        else: # different variables are the leader. Two cases:
            vp = lp.infinite_variables()[0]; vq = lq.infinite_variables()[0]
            if vp == vq: # the same variable --> we need to apply an operator to p
                ip = vp.index(lp, as_tuple=True); iq = vp.index(lq, as_tuple=True)
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
        
        lp = self.leader(p); lq = self.leader(q)
        comparison = self.compare_variables(lp, lq)
        if comparison > 0: # impossible condition
            raise TypeError("[ranking] Impossible condition reached: 'l(p) > l(q) when p < q'")
        elif comparison == 0: # same leader --> we need to multiply by the leader to match degrees
            p = lp**(q.degree(lp)-p.degree(lp)) * p
            return self.monic(self.initial(q)*p), self.monic(self.initial(p)*q)
        else: # different variables are the leader. Two cases:
            vp = lp.infinite_variables()[0]; vq = lp.infinite_variables()[0]
            if vp == vq: # the same variable --> we need to apply an operator to p
                ip = vp.index(lp, as_tuple=True); iq = vp.index(lq, as_tuple=True)
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
        left = self.sort(elements[:middle]); right = self.sort(elements[middle:])

        result = self.__merge(left, right)
        if reverse: result.reverse()
        return result
    
    def __repr__(self) -> str:
        return f"{self.type.capitalize()} ranking over {self.parent()} where [{' < '.join([repr(el) for el in self.base_order])}]"
    
    def _latex_(self) -> str:
        return r"\mathbf{" + ("OrdR" if self.type == "orderly" else "ElimR") + r"}(" + "<".join(latex(v) for v in self.base_order) + r")"

__all__ = [
    "DPolynomialRing", "DifferentialPolynomialRing", "DifferencePolynomialRing", "is_DPolynomialRing", # names imported
    "RWOPolynomialRing", "is_RWOPolynomialRing" # deprecated names (backward compatibilities) 
]          