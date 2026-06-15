from __future__ import annotations
r'''
    Module for monomial extensions on D-Algebra.

    Let `(K, (d_1,\ldots,d_n))` be a D-field (a field with several operations - both
    derivations and shifts). We say that `t` is a monomial over this D-field if it
    is a transcendental element over `K` and, for all `i =1,\ldots n`, `d_i(t) \in K[t]`.

    In this cases, we know that `d_i` are closed in `K[t]`: let `p(t) \in K[t]`, then

    * If `d` is a derivation, then `d(p(t)) = \partial_t(p(t)) + \kappa_d(p(t))`, where
        `\partial_t` is the partial derivative, and `\kappa_d` is the derivation where
        all coefficients are differentiated using `d` over `K`, but `t` remains intact.
    * If `d` is a shift, then `d(p(t)) = \kappa_d(p(t))(d(t))`.

    This module aims to provide a full implementation as univariate polynomials and their
    fraction fields of monomial extensions. It is of crucial importance that we can iterate
    this construction building a "tower of monomials".

    EXAMPLES::

    sage: from dalgebra.dmonomial import DMonomial
    sage: # Test (Q[x], dx)
    sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
    sage: x.derivative()
    1
    sage: # Test (Q[x], x -> x+1)
    sage: S.<x> = DMonomial(DifferenceRing(QQ), [x + 1])
    sage: x.difference()
    x + 1
    sage: # Tests (e^x, ln(x), tan(x))
    sage: T.<e> = DMonomial(DifferentialRing(QQ), ["e"])
    sage: e.derivative()
    e
    sage: U.<x,ln> = DMonomial(DifferentialRing(QQ), [1, "1/x"])
    sage: x.derivative()
    1
    sage: ln.derivative()
    1/x
    sage: V.<tn> = DMonomial(DifferentialRing(QQ), ["1 + tn"])
    sage: tn.derivative()
    1 + tn^2
    sage: # Test (x, ln(x), e^x, tan(x))
    sage: W.<x, ln, e, tn> = DMonomial(DifferentialRing(QQ), [1, 1/x, e, 1 + tn^2])
    sage: x.derivative()
    1
    sage: ln.derivative()
    1/x
    sage: e.derivative()
    e
    sage: tn.derivative()
    1 + tn^2
    sage: # Test (x!, factorial)
    sage: X.<x, f> = DMonomial(DifferenceRing(QQ), [x + 1, (x + 1) * f])
    sage: x.difference()
    x+1
    sage: f.difference()
    (x + 1)*f

    This module will also allow the mis of several operations. Let us consider the partial derivatives or a
    difference-differential ring::

    sage: # Partial case (Q[x,t], dx, dt)
    sage: Y.<x,t> = DMonomial(DifferentialRing(QQ, 0, 0), [[1,0], [0,1]])
    sage: x.derivative(0), x.derivative(1)
    (1, 0)
    sage: t.derivative(0), t.derivative(1)
    (0, 1)
    sage: (x^3*t + 2*x^2*t^2).derivative(0)
    3*x^2*t + 4*x*t^2
    sage: (x^3*t + 2*x^2*t^2).derivative(1)
    x^3 + 4*x^2*t
    sage: # Differential-Difference case (Q[x,t], x, x -> x+1)
    sage: Z.<x> = DMonomial(DifferenceRing(DifferentialRing(QQ)), [1, x + 1])
    sage: x.derivative()
    1
    sage: x.difference()
    x + 1
    sage: A.<x,e_x> = DMonomial(DifferenceRing(DifferentialRing(QQ['e'])).fraction_field(), [[1, x+1], [e_x, 'e*e_x']])
    sage: e_x.derivative()
    e_x
    sage: e_x.difference()
    e*e_x

    ::IGNORE AUDIT::

    TODO: For monomial
'''

import logging

from sage.arith.misc import GCD as gcd
from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.matrix.constructor import matrix
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex, latex_variable_name
from sage.misc.misc_c import prod
from sage.rings.ideal import Ideal_generic as Ideal, Ideal as ideal
from sage.rings.infinity import Infinity as oo, UnsignedInfinityRing
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.multi_polynomial_ring import MPolynomialRing_base
from sage.rings.polynomial.polynomial_ring import PolynomialRing_generic
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element, Matrix
from sage.structure.factorization import Factorization
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Iterator

from ..dring import AdditiveMap, DRings, DFractionField, DFractionFieldElement, IntegrationError, MorphismToLaurent

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)
uoo = UnsignedInfinityRing.an_element()

logger = logging.getLogger(__name__)

## Notes for module:
#    - DMonomial_Element -> implementation of a univariate polynomial.
#    - DMonomial_Parent -> implementation of the polynomial ring `K[t]`
#    - DMonomialFunctor -> ConstructionFunctor for D-monomial extensions.
#    - DMM_ParentToBase -> Conversion morphism from DMonomial_Parent to their bases
#    - DMM_BaseToPArent -> Coercion morphism from a base field to DMonomial_Parent
#    - DMM_BetweenBases -> Coercion morphism between two DMonomial_Parent with different bases
## After these classes, everything else should be done by SageMath code. Things to be checked
#    in the future
#    - Vectors -> free modules over these rings and fields
#    - Matrices -> matrices ring over these ring and fields
#    - DElliptic -> how these DMonomial interact with DElliptic?


class RequestName():
    r'''
        Class to request name uniquely during a full session of execution.
    '''
    names_given = set()
    base = "_t"
    gen = 0

    @staticmethod
    def get(*older_names: str) -> str:
        import re
        m = RequestName.gen
        for name in older_names:
            M = re.match(f"{RequestName.base}_(\\d+)", name)
            if M is not None:
                m = max(m, M.groups()[0]+1)
        output = f"{RequestName.base}_{m}"
        RequestName.gen = m+1
        return output


#####################################
### FACTORY CLASS
#####################################
class DMonomialFactory (UniqueFactory):
    r'''
        Factory to create a D-Extension.

        An extension requires a base field and a tuple of tuples such that for each variable we can get the
        corresponding operation. The way these tuple of tuples can be provided may change depending on how many
        variables we want to add and how many operations there are.
    '''
    def create_key(self, base, polynomial: str | Element, varname: str = None, *, names: tuple[str] = None, category=None):
        if names is None and varname is None:
            raise ValueError("The names of the variables must be provided")
        elif names is None:
            names = (varname,)

        if base not in _DRings or base not in _Fields:
            raise ValueError("The base must be a field that is also a d-ring")

        ## We process the argument polynomial
        if not isinstance(polynomial, (list,tuple)) and (len(names) != 1 or base.noperators() != 1):
            raise TypeError("The polynomial argument must be a list if there are more than one variable or more than one operator")
        elif not isinstance(polynomial, (list,tuple)): # case with 1 variable and 1 operator and 1 element
            polynomial = ((polynomial,),)

        ## Here polynomial is a list or tuple
        if any(not isinstance(p, (list,tuple)) for p in polynomial) and (len(names) != 1 and base.noperators() != 1):
            raise TypeError("The polynomial argument must be a list of lists if there are more than one variable and more than one operator")
        elif any(not isinstance(p, (list,tuple)) for p in polynomial):
            if len(names) == 1: # case with multiple operations and 1 variable
                polynomial = (polynomial,)
            else: # case with 1 operation and multiple variables
                polynomial = tuple((p,) for p in polynomial)

        ## Now we know that polynomial is a tuple of tuples
        polynomial = tuple(tuple(str(p) for p in poly) for poly in polynomial) # we make sure everything is a tuple of tuples of strings
        if len(polynomial) != len(names):
            raise ValueError("The number of variables and the number of polynomials must match")
        elif any(len(p) != base.noperators() for p in polynomial):
            raise ValueError("The number of operators must match the number of polynomials")

        ## We fix the arguments if the base was already a DExtension (iterative construction)
        if isinstance(base.base(), DMonomial_Parent):
                names = tuple(str(g) for g in base.base().tower_gens()) + names
                polynomial = tuple(tuple(str(el) for el in imgs) for imgs in base.base().tower_operations_for_gens()) + polynomial
                base = base.base().tower_base()

        ## We homogenize the images
        R = PolynomialRing(base.to_sage(), names=names).fraction_field()
        polynomial = tuple(tuple(str(R(el)) for el in imgs) for imgs in polynomial)

        logger.debug(f"key: ({base}, {names}, {polynomial}, {category})")
        return (base, names, polynomial, category)

    def create_object(self, _, key) -> DMonomial_Parent:
        base, names, polynomial, category = key

        if len(names) == 1: # one variable -- nothing to check
            return DMonomial_Parent(base, names[0], polynomial[0], category=category)
        else: # several variables -- we make a recursive build-up preserving the order
            base = DMonomial(base, polynomial[:-1], names=names[:-1], category=category)
            return DMonomial_Parent(base.fraction_field(), names[-1], polynomial[-1], category=category)


DMonomial = DMonomialFactory("dalgebra.dextension.dmonomial.DMonomial")


#####################################
### ELEMENT CLASS
#####################################
class DMonomial_Element (Element):
    r'''
        Implementation of a DMonomial Element

        This is a normal implementation of a univariate polynomial in dense
        representation, i.e., the coefficients are stored in a list
        where the empty coefficients are represented with zeros.

        INPUT:

        * ``parent``: the parent of this polynomial. It **has** to be a
            DMonomial_Parent.
        * ``data``: the coefficients of the polynomial. It can be a list/tuple of elements
            that will be interpreted as the coefficients sorted by degree; or a dictionary where
            the keys will be the degree and the values the corresponding coefficients. In any case
            the coefficients must be already casted into ``parent.base()``.
    '''
    def __init__(self, parent: DMonomial_Parent, data: list[Element] | tuple[Element] | dict[Element]):
        ## Initializing the Element structure
        super().__init__(parent)

        if isinstance(data, dict): # special case of dictionary
            degree = max(data)+1 if len(data) > 0 else 0
            data = tuple(data.get(i,self.parent().base().zero()) for i in range(degree+1))
        elif isinstance(data, str): # special case of string
            data = (data,)

        ## We clean the data if the coefficients are zero
        i = len(data)
        while i > 0 and data[i-1] == 0:
            i -= 1
        self.__coefficients = list(self.parent().base()(d) for d in data[:i])

    ## Getter and attribute methods
    def degree(self) -> int:
        if not self.__coefficients:
            return -oo
        return len(self.__coefficients)-1

    def leading_coefficient(self) -> Element:
        return self.__coefficients[-1]

    lc = leading_coefficient

    def monic(self) -> DMonomial_Element:
        return self / self.lc()

    def constant_coefficient(self) -> Element:
        return self.__coefficients[0]

    cc = constant_coefficient

    def monomials(self) -> tuple[DMonomial_Element]:
        v = self.parent().gen()
        return tuple(v**i for i,c in enumerate(self.__coefficients) if c != 0)

    def coefficients(self, sparse=True) -> tuple[Element]:
        if sparse:
            return tuple(c for c in self.__coefficients if c != 0)
        else:
            return tuple(self.__coefficients)

    def mons_cons_iter(self) -> Iterator[tuple[DMonomial_Element,Element]]:
        return zip(self.monomials(), self.coefficients())

    def coefficient(self, index: int) -> Element:
        try:
            return self.__coefficients[index]
        except IndexError:
            return self.parent().base().zero()

    def __getitem__(self, i: int) -> Element:
        return self.coefficient(i)

    def numerator(self) -> DMonomial_Element:
        return self

    def denominator(self) -> DMonomial_Element:
        return self.parent().one()

    def is_zero(self) -> bool:
        return not self.__coefficients

    def is_one(self) -> bool:
        return len(self.__coefficients) == 1 and self[0] == 1

    def is_unit(self) -> bool:
        return self in self.parent().base()

    def is_constant(self) -> bool:
        return len(self.__coefficients) <= 1

    def is_monomial(self) -> bool:
        coeffs = self.coefficients()
        return len(coeffs) == 1 and coeffs[0] == self.parent().base().one()

    def is_monic(self) -> bool:
        return self.lc() == 1

    @cached_method
    def algebraic(self) -> Element:
        return self.parent().to_sage()(self)

    def to_sage(self) -> Element:
        return self.algebraic()

    ## Useful derivation methods
    @cached_method
    def kappa(self, operation: int = 0) -> DMonomial_Element:
        return self.parent().element_class(
            self.parent(),
            [c.operation(operation) for c in self.__coefficients] # apply the operation to each coefficient
        )

    @cached_method
    def partial(self) -> DMonomial_Element:
        if self.is_constant():
            return self.parent().zero()
        return self.parent().element_class(
            self.parent(),
            [i*self.__coefficients[i] for i in range(1, self.degree()+1)]
        )

    ## Other operational methods
    def conditions_to_zero(self) -> tuple[tuple[DMonomial_Element,Element]]:
        return tuple((m,c.to_sage()) for (m,c) in self.mons_cons_iter())

    def factor(self) -> Factorization:
        f = self.algebraic().factor()
        return Factorization([(self.parent()(p), e) for (p,e) in f], self.parent().base()(f.unit()))

    def lcm(self, *others: DMonomial_Element) -> DMonomial_Element:
        if len(others) == 1 and isinstance(others[0], (list,tuple)):
            others = others[0]

        if len(others) == 0:
            return self
        else:
            from sage.arith.functions import lcm
            return self.parent()(lcm(self.algebraic(), *(o.algebraic() for o in others)))

    def content(self) -> Element:
        if self.is_zero():
            return self.parent().base().zero()
        return gcd(self.coefficients(sparse=True))

    def primitive(self) -> DMonomial_Element:
        if self.is_zero():
            return self.parent().zero()
        return self / self.content()

    def is_primitive(self) -> bool:
        return (not self.is_zero()) and self == self.primitive()

    def is_squarefree(self) -> bool:
        F = self.squarefree()
        return len(F) <= 1 and all(exp == 1 for (_,exp) in F)

    def wronskian(self, operation:int = 0, *other: DMonomial_Element) -> DMonomial_Element:
        r'''
            Compute the Wronskian of self with a set of polynomials for a given operation.
        '''
        return self.parent().wronskian(operation, self, *other)

    ## Arithmetic methods
    def _add_(self, other: DMonomial_Element) -> DMonomial_Element:
        if self.is_zero():
            return other
        elif other.is_zero():
            return self
        return self.parent().element_class(
            self.parent(),
            [self[i] + other[i] for i in range(max(self.degree(), other.degree())+1)])

    def _neg_(self) -> DMonomial_Element:
        return self.parent().element_class(
            self.parent(),
            [-c for c in self.coefficients(sparse=False)]
        )

    def _sub_(self, other: DMonomial_Element) -> DMonomial_Element:
        return self + (-other)

    def _mul_(self, other: DMonomial_Element) -> DMonomial_Element:
        # TODO: add a better implementation for multiplication of polynomials
        if self.is_zero() or other.is_zero():
            return self.parent().zero()
        elif self.is_one():
            return other
        elif other.is_one():
            return self
        elif other.is_constant():
            return self.parent().element_class(
                self.parent(),
                [c*other[0] for c in self.__coefficients]
            )
        elif other.is_monomial():
            other_degree = other.degree()
            return self.parent().element_class(
                self.parent(),
                {m.degree()+other_degree : c for m,c in self.mons_cons_iter()}
            )
        else:
            return sum(((self*m)*c for (m,c) in other.mons_cons_iter()), start=self.parent().zero())

    @cached_method
    def __pow__(self, power: int) -> DMonomial_Element:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            return (~self)**(-power)
        else:
            a,A = (self**(power//2 + power % 2), self**(power//2))
            return a*A

    def __invert__(self) -> DFractionFieldElement:
        if self.is_constant():
            return self.parent().element_class(self.parent(), [~self.lc()])
        return self.parent().fraction_field()._element_class(
            self.parent().fraction_field(),
            self.parent().one(),
            self
        )

    def _floordiv_(self, other: DMonomial_Element) -> DMonomial_Element:
        return self.quo_rem(other)[0]

    def _mod_(self, other: DMonomial_Element) -> DMonomial_Element:
        return self.quo_rem(other)[1]

    def __eq__(self, other) -> bool:
        if not isinstance(other, self.__class__) or other.parent() != self.parent():
            try:
                other = self.parent()(other)
            except Exception:
                return False

        return self.__coefficients == other.__coefficients

    def __ne__(self, other) -> bool:
        return not (self == other)

    def hash(self) -> int:
        return hash(self.__coefficients)

    def __call__(self, *args, **kwds):
        return self.parent()(self.to_sage()(*args, **kwds))

    ## Other functions
    def __repr__(self) -> str:
        return repr(self.algebraic())

    def __hash__(self) -> int:
        return hash(tuple(self.__coefficients))

    def _latex_(self) -> str:
        return latex(self.algebraic())

    ########################################
    ### Methods from Bronstein book
    ########################################
    ### CHAPTER 1: BASIC POLYNOMIAL METHODS
    def quo_rem(self, other: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element]:
        q,r = self.algebraic().quo_rem(other.algebraic())
        return self.parent()(q), self.parent()(r)

    def quo_rem_base(self, other: DMonomial_Element) -> tuple[DMonomial_Element,DMonomial_Element]:
        r'''
            Finds `Q` and `R` such that ``self = Q*other + R`` and ``deg(R) < deg(other)``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: A = 3*x^3 + x^2 + x + 5
                sage: B = 5*x^2 - 3*x + 1
                sage: Q, R = A.quo_rem_base(B)
                sage: A == B*Q + R
                True
                sage: Q
                14/25 + (3/5)*x
                sage: R
                111/25 + (52/25)*x
        '''
        Q = self.parent().zero()
        R = self
        x = self.parent().gen()
        delta = R.degree() - other.degree()
        while R != 0 and delta >= 0:
            T = R.lc()/other.lc() * x**delta
            Q += T
            R -= other*T
            delta = R.degree() - other.degree()

        return (Q,R)

    def pseudo_quo_rem(self, other: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element]:
        q,r = self.algebraic().pseudo_quo_rem(other.algebraic())
        return self.parent()(q), self.parent()(r)

    def pseudo_quo_rem_base(self, other: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element]:
        r'''
            Computes the pseudo-division of ``self`` and ``other``.

            In this case, if ``self`` and ``other`` are in `R[x]`, then all operations remain in `R[x]`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: A = 3*x^3 + x^2 + x + 5
                sage: B = 5*x^2 - 3*x + 1
                sage: Q,R = A.pseudo_quo_rem_base(B)
                sage: 25*A == B*Q + R
                True
                sage: Q
                14 + (15)*x
                sage: R
                111 + (52)*x
        '''
        b = other.lc()
        x = self.parent().gen()
        N = self.degree() - other.degree() + 1
        Q = self.parent().zero()
        R = self
        delta = R.degree() - other.degree()
        while R != 0 and delta >= 0:
            T = R.lc()*x**delta
            N = N-1
            Q = b*Q+T
            R = b*R-T*other
            delta = R.degree() - other.degree()
        return b**N*Q, b**N*R

    def gcd(self, other: DMonomial_Element) -> DMonomial_Element:
        return self.parent()(self.algebraic().gcd(other.algebraic()))

    def gcd_euclidean(self, other: DMonomial_Element) -> DMonomial_Element:
        r'''
            Computes the GCD of two polynomials using the Euclidean algorithm

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: b = x^3 + x^2 - 4*x -4
                sage: a.gcd_euclidean(b)
                5 + 5*x
        '''
        a, b = self, other
        while b != 0:
            a, b = b, a % b
        return a

    def gcd_extended_euclidean_basic(self, other: DMonomial_Element) -> tuple[DMonomial_Element,DMonomial_Element,DMonomial_Element]:
        r'''
            Computes the GCD of two polynomials using the Extended Euclidean algorithm.

            This means that this method returns three values `(s, t, g)` where ``s*self + t*other = g``
            and `g` is the ``gcd(self, other)``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: b = x^3 + x^2 - 4*x -4
                sage: s,t,g = a.gcd_extended_euclidean_basic(b)
                sage: a*s + b*t == g
                True
                sage: g
                5 + 5*x
                sage: s
                3 + (-1)*x
                sage: t
                10 + (-6)*x + x^2
        '''
        s = self.parent().one()
        t = self.parent().zero()
        b_1 = self.parent().zero()
        b_2 = self.parent().one()

        a,b = self, other
        while b != 0:
            q,r = a.quo_rem(b)
            a,b = b,r
            r_1,r_2 = s - q*b_1, t - q*b_2
            s,t,b_1,b_2 = b_1, b_2, r_1, r_2
        return (s,t,a)

    def gcd_half_extended_euclidean(self, other: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element]:
        r'''
            Computes two values `s, g` such that ``g = gcd(self, other)`` and ``s*self = g (mod other)``.
        '''
        s = self.parent().one()
        b_1 = self.parent().zero()
        a, b = self, other

        while b != 0:
            q, r = a.quo_rem(b)
            a, b = b, r
            r_1 = s - q*b_1
            s, b_1 = b_1, r_1

        return (s, a)

    def gcd_extended_euclidean(self, other: DMonomial_Element) -> tuple[DMonomial_Element,DMonomial_Element,DMonomial_Element]:
        r'''
            Computes the GCD of two polynomials using the Extended Euclidean algorithm.

            This means that this method returns three values `(s, t, g)` where ``s*self + t*other = g``
            and `g` is the ``gcd(self, other)``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: b = x^3 + x^2 - 4*x -4
                sage: s,t,g = a.gcd_extended_euclidean(other)
                sage: a*s + b*t == g
                True
                sage: g
                5 + 5*x
                sage: s
                3 + (-1)*x
                sage: t
                10 + (-6)*x + x^2
        '''
        s,g = self.gcd_half_extended_euclidean(other)

        t,r = (g - s*self).quo_rem(other)
        assert r == 0

        return s,t,g

    def diophantine_euclidean_basic(self,
                                    other: DMonomial_Element,
                                    goal: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element, DMonomial_Element]:
        r'''
            Computes elements `s,t` such that ``s*self + t*other == goal``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: b = x^3 + x^2 - 4*x -4
                sage: s,t = a.diophantine_euclidean_basic(b, x^2 - 1)
                sage: s*a + t*b == x^2 - 1
                True
                sage: s
                -3/5 + (4/5)*x + (-1/5)*x^2
                sage: t
                -2 + (16/5)*x + (-7/5)*x^2 + (1/5)*x^3
        '''
        s,t,g = self.gcd_extended_euclidean(other)
        q,r = goal.quo_rem(g)

        if r != 0:
            raise ValueError(f"The given goal ({goal}) is not in the ideal of {self} and {other}.")
        s,t = s*q, t*q
        if s != 0 and s.degree() >= other.degree():
            q,r = s.quo_rem(other)
            s, t = r, t + q*self

        return (s,t)

    def diophantine_half_euclidean(self,
                                   other: DMonomial_Element,
                                   goal: DMonomial_Element):
        r'''
            Computes a value `s` such that ``s*self = goal (mod other)``.
        '''
        s,g = self.gcd_half_extended_euclidean(other)
        q,r = goal.quo_rem(g)

        if r != 0:
            raise ValueError(f"The given goal ({goal}) is not in the ideal of {self} and {other}.")

        s = s*q

        if s != 0 and s.degree() >= other.degree():
            s = s % other
        return s

    def diophantine(self, other: DMonomial_Element, goal: DMonomial_Element) -> tuple[DMonomial_Element, DMonomial_Element]:
        r'''
            Computes elements `s,t` such that ``s*self + t*other == goal``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: b = x^3 + x^2 - 4*x -4
                sage: s,t = a.diophantine(b, x^2 - 1)
                sage: s*a + t*b == x^2 - 1
                True
                sage: s
                -3/5 + (4/5)*x + (-1/5)*x^2
                sage: t
                -2 + (16/5)*x + (-7/5)*x^2 + (1/5)*x^3
        '''
        s = self.diophantine_half_euclidean(other, goal)
        t,r = (goal - s*self).quo_rem(other)

        assert r == 0

        return (s,t)

    def partial_fraction(self, *denominators: DMonomial_Element) -> tuple[DMonomial_Element]:
        r'''
            Computes the Partial Fraction Decomposition of ``self / prod(denominators)``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^2 + 3*x
                sage: ds = [x+1, x^2 - 2*x +1]
                sage: r = a.partial_fraction(*ds)
                sage: r[0]
                0
                sage: r[1]
                -1/2
                sage: r[2]
                1/2 + (3/2)*x
        '''
        if not denominators:
            return (self,) # the denominator is 1

        a_0, r = self.quo_rem(prod(denominators))

        if len(denominators) == 1:
            return (a_0,r)

        a_1, t = prod(denominators[1:]).diophantine(denominators[0], r)
        recursion = t.partial_fraction(*denominators[1:])

        return (recursion[0] + a_0, a_1, *recursion[1:])

    def partial_fraction_extended(self, denominators: tuple[DMonomial_Element], exponents: tuple[int]) -> tuple[DMonomial_Element]:
        r'''
            Computes full partial fraction decomposition with exponents.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x> = DMonomial(DifferentialRing(QQ), [1])
                sage: a = x^2 + 3*x
                sage: d = x^3 - x^2 - x + 1
                sage: r = a.partial_fraction_extended(*list(zip(*d.factor())))
                sage: r[0]
                0
                sage: r[1]
                -1/2
                sage: r[2]
                3/2
                sage: r[3]
                2
        '''
        if not isinstance(denominators, (list,tuple)) or not isinstance(exponents, (list,tuple)):
            raise TypeError(f"The arguments 'denominators' and 'exponents' must be list or tuples")
        elif len(denominators) != len(exponents):
            raise ValueError(f"The arguments 'denominators' and 'exponents' must be of same length")

        partial_fraction = self.partial_fraction(*(d**e for (d,e) in zip(denominators, exponents)))
        result = list()
        a_0 = partial_fraction[0]
        for i,a in enumerate(partial_fraction[1:]):
            to_add = list()
            d, e = denominators[i], exponents[i]
            for _ in range(e, 0, -1):
                a, r = a.quo_rem(d)
                to_add = [r] + to_add
            result.extend(to_add)
            a_0 += a

        return [a_0] + result

        # TODO: Go on here

    def subresultant_sequence(self, other: DMonomial_Element) -> tuple[DMonomial_Element, tuple[DMonomial_Element]]:
        R = [self, other]
        gamma = [None, -1]
        delta = [None, self.degree() - other.degree()]
        beta = [None, (-1)**(delta[1]+1)]
        r = [None]
        while R[-1] != 0:
            r.append(R[-1].lc())
            _, _R = R[-2].pseudo_quo_rem(R[-1])
            R.append(_R//beta[-1])
            gamma.append((-r[-1])**delta[-1]*gamma[-1]**(1-delta[-1]))
            delta.append(R[-2].degree() - R[-1].degree() if R[-1] != 0 else R[-2].degree())
            delta.append(R[-2].degree() - R[-1].degree() if R[-1] != 0 else R[-2].degree())
            beta.append(-r[-1]*gamma[-1]**delta[-1])
        k = len(R) - 2
        PRS = tuple(R[:k+2])
        if R[k].degree() > 0:
            return (self.parent().zero(), PRS)
        elif R[k-1].degree() == 1:
            return (R[k], PRS)

        s, c = 1,1
        for j in range(1, k):
            if R[j-1].degree() % 2 and R[j].degree() % 2:
                s = -s
            c *= (beta[j]//r[j]**(1+delta[j]))**R[j].degree() * r[j]**(R[j-1].degree()-R[j+1].degree())

        return (s*c*R[k]**(R[k-1].degree()), PRS)

    def resultant(self, other: DMonomial_Element) -> DMonomial_Element:
        r'''
            Compute the resultant of two polynomials

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<t,x> = DMonomial(DifferentialRing(QQ), ["t", 1])
                sage: A = 3*t*x^2 - t^3 - 4
                sage: B = x^2 + t^3*x - 9
                sage: A.resultant(B)
                (-16 + (216)*t + (-729)*t^2 + (-8)*t^3 + (54)*t^4 + (-1)*t^6 + (12)*t^7 + 3*t^10)/(-1)
        '''
        return self.subresultant_sequence(other)[0]

    @cached_method
    def squarefree(self) -> Factorization:
        F = self.algebraic().squarefree_decomposition()
        return Factorization(
            ((self.parent()(el), i) for (el,i) in F),
            unit=self.parent().base()(F.unit())
            )

    @cached_method
    def squarefree_musser(self) -> Factorization:
        r'''
            Musser's squarefree factorization as in Bronstein's book (page 29)

            EXAMPLES::

            sage: from dalgebra import *
            sage: Q.<x> = DMonomial(DifferentialRing(QQ), [1])
            sage: A = x^8 + 6*x^6 + 12*x^4+8*x^2
            sage: F = A.squarefree_musser(); F
            x^2 * (x^2 + 2)^3
        '''
        c = self.content()
        S = self.primitive() ## this remains as a DMonomial_Element
        S_ = S.gcd(S.partial()).primitive()
        S__ = S // S_

        A = list()

        while S_.degree() > 0:
            Y = S__.gcd(S_).primitive()
            A.append(S__ // Y)
            S__, S_ = Y, S_ // Y
        A.append(S__)

        return Factorization(((el, i+1) for i,el in enumerate(A) if el != 1), unit=c*S_.cc())

    @cached_method
    def squarefree_yun(self) -> Factorization:
        r'''
            Yun's squarefree factorization as in Bronstein's book (page 32)

            EXAMPLES::

            sage: from dalgebra import *
            sage: Q.<x> = DMonomial(DifferentialRing(QQ), [1])
            sage: A = x^8 + 6*x^6 + 12*x^4+8*x^2
            sage: F = A.squarefree_yun(); F
            x^2 * (x^2 + 2)^3
        '''
        c = self.content()
        S = self.primitive()

        S_p = S.partial()
        S_ = S.gcd(S_p).primitive()
        S_star = S // S_
        Y = S_p // S_

        A = list()

        Z = Y - S_star.partial()
        while Z != 0:
            A.append(S_star.gcd(Z).primitive())
            S_star, Y = S_star // A[-1], Z // A[-1]

            Z = Y - S_star.partial()
        A.append(S_star)

        return Factorization(((el, i+1) for i,el in enumerate(A) if el != 1), unit=c)

    ### CHAPTER 3: MONOMIAL EXTENSION
    @cached_method
    def is_normal(self, operation: int = 0) -> bool:
        if self.parent().operator_types()[operation] != "derivation":
            raise TypeError("The operation must be a derivation")
        return self.gcd(self.operation(operation)) in self.parent().base()

    @cached_method
    def is_special(self, operation: int = 0) -> bool:
        if self.parent().operator_types()[operation] != "derivation":
            raise TypeError("The operation must be a derivation")

        if self.parent().is_primitive(operation): # special case with D(t) in self.base()
            return self.monic().operation(operation) == 0
        elif self.parent().is_hyperexponential(operation): # special case with D(t)/t in self.base()
            p = self.monic()
            x = self.parent().gen()
            d = p.degree()
            return p.operation(operation)*x**d == d*x**(d-1)*p
        return self.operation(operation) % self == 0

    @cached_method
    def is_simple(self) -> bool:
        return True # a polynomial has always a normal denominator (i.e., 1)

    @cached_method
    def is_reduced(self) -> bool:
        return True # a polynomial has always a special denominator (i.e., 1)

    @cached_method
    def splitting_factorization(self, operation: int = 0) -> tuple[DMonomial_Element, DMonomial_Element]:
        r'''
            Method to compute a splitting factorization of ``self``.

            A splitting factorization is a pair `(q_n, q_s)`, where all squarefree factors of `q_n` are normal and `q_s`
            is special (see methods :func:`squarefree`, :func:`is_normal` and :func:`is_special`), and such that
            `q_nq_s = self`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x,t> = DMonomial(DifferentialRing(QQ), [1, "-t^2 - 3/(2*x)*t + 1/(2*x)"])
                sage: # Bronstein Example 3.5.1
                sage: p = 4*x^4*t^5-4*x^3*(x+1)*t^4+x^2*(2*x-3)*t^3+x*(2*x^2+7*x+2)*t^2-(4*x^2+4*x-1)*t +2*x-1
                sage: q_n, q_s = p.splitting_factorization()
                sage: q_n
                4*x^4*t^3 + (-4*x^4 - 8*x^3)*t^2 + (8*x^3 + 4*x^2)*t - 4*x^2
                sage: q_s
                t^2 + 1/x*t + (-1/2*x + 1/4)/x^2

        '''
        if self.parent().operator_types()[operation] != "derivation":
            raise TypeError("The operation must be a derivation")

        S = self.gcd(self.operation(operation)).monic() // self.gcd(self.partial()).monic()
        if S.degree() == 0:
            return self, self.parent().one()
        q_n, q_s = (self // S).splitting_factorization(operation)
        return q_n, S*q_s

    @cached_method
    def splitting_factorization_squarefree(self, operation: int = 0) -> tuple[Factorization, Factorization]:
        r'''
            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<x,t> = DMonomial(DifferentialRing(QQ), [1, "-t^2 - 3/(2*x)*t + 1/(2*x)"])
                sage: # Bronstein Example 3.5.2
                sage: p = 4*x^4*t^5-4*x^3*(x+1)*t^4+x^2*(2*x-3)*t^3+x*(2*x^2+7*x+2)*t^2-(4*x^2+4*x-1)*t +2*x-1
                sage: p.splitting_factorization_squarefree()
        '''
        if self.parent().operator_types()[operation] != "derivation":
            raise TypeError("The operation must be a derivation")

        F = self.squarefree()
        normal, special = list(), list()
        for (f, exp) in F:
            S = f.gcd(f.operation(operation)).monic()
            normal.append((f // S, exp))
            special.append((S, exp))
        return (Factorization((factor for factor in normal if factor[0] != 1), unit=F.unit()),
                Factorization((factor for factor in special if factor[0] != 1)))

    ### CHAPTER 4: ORDER FUNCTION
    @cached_method
    def order_function(self) -> DMM_OrderFunction:
        return self.parent().order_function(self)

    def order(self, element: DMonomial_Element | DFractionFieldElement) -> int:
        return self.order_function()(element)

    def order_at(self, element: DMonomial_Element) -> int:
        return element.order_function()(self)

    @cached_method
    def value_function(self) -> DMM_ValueFunction:
        return self.parent().value_function(self)

    def value(self, element: DMonomial_Element | DFractionFieldElement) -> Element:
        return self.value_function()(element)

    def value_at(self, element: DMonomial_Element) -> Element:
        return self.parent().value_function(element)(self)

    def remainder(self, element: DMonomial_Element | DFractionFieldElement) -> DMonomial_Element:
        r'''
            Return the local remainder at ``self`` of ``element``.
        '''
        return self.parent()(self.value(element).lift())
        # From Bronstein page 113
        # c,_ = element.denominator().gcd_half_extended_euclidean(self)
        # return (element.numerator() * c) % self

    def remainder_at(self, element: DMonomial_Element) -> DMonomial_Element:
        r'''
            Return the local remainder at ``element`` of ``self``.
        '''
        value = self.value_at(element)
        if element is oo: # value at infinity returns element in self.parent().base()
            return self.parent()(value)
        else: # returns something in a quotient ring
            return self.parent()(value.lift())

    @cached_method
    def residue_function(self, operation: int = 0) -> DMM_ResidueFunction:
        return self.parent().residue_function(self, operation)

    def residue(self, element: DMonomial_Element | DFractionFieldElement, operation: int = 0) -> Element:
        return self.residue_function(operation)(element)

    def residue_at(self, element: DMonomial_Element, operation: int = 0) -> Element:
        return self.parent().residue_function(element, operation)(self)


#####################################
### PARENT CLASS
#####################################
class DMonomial_Parent (Parent):
    Element = DMonomial_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        if base.is_commutative():
            return [_DRings, Algebras(base).Commutative()] + ([category] if category is not None else [])
        else:
            return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, varname:str, gen_images: tuple[str], category=None):
        if base not in _Fields or base not in _DRings:
            raise TypeError(f"The base must be a field and have d-operations")

        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## Variables for cached attributes
        self.__varname = varname
        self.__algebraic = None
        self.__images = None
        self.__gen = None
        self.__operators = None
        self.__fraction_field = None

        self._initialize_algebraic()
        self._initialize_data(gen_images)

        ## Extending the operations of ``base``
        if any(el not in ("derivation", "homomorphism") for el in self.base().operator_types()):
            raise TypeError(f"DMonomial extension only valid for derivation and homomorphisms")
        self.__operators = [
            self.extend_derivation(i) if ttype == "derivation" else
            self.extend_homomorphism(i)
            for (i, ttype) in enumerate(self.base().operator_types())
        ]

        self.__constants = self._compute_constants()

    ## Initialization methods
    def _initialize_algebraic(self):
        ## We create the algebraic base structure
        # self.__algebraic = PolynomialRing(self.base().to_sage(), self.varname())
        if self.tower_depth() > 1:
            base_field = PolynomialRing(
                self.tower_base().to_sage(),
                self.tower_names()[:-1]).fraction_field()
        else:
            base_field = self.tower_base().to_sage()

        self.__algebraic = PolynomialRing(base_field, self.__varname)

        ## Adding coercion and conversion morphisms
        self.base().register_conversion(DMM_ParentToBase(self))
        self.register_coercion(DMM_BaseToParent(self))
        self.__algebraic.register_coercion(DMM_ParentToAlgebraic(self))
        self.register_coercion(DMM_AlgebraicToParent(self))

    def _initialize_data(self, images: tuple[str]):
        self.__images = tuple(self(self.to_sage()(img)) for img in images)

    def _compute_constants(self) -> tuple[Parent]:
        r'''
            Computes (if possible) the ring of constants (as algebraic structure) for each operation.

            If the computation can not be performed, ``None`` is stored.
        '''
        result = []
        for operation, otype in enumerate(self.operator_types()):
            if otype == "homomorphism":
                result.append(None)
            elif otype == "derivation":
                t = self.gen()
                if self.is_primitive(operation):
                    ## See Theorem 5.1.1 of Bronstein's book
                    try:
                        self.base()(t.operation(operation)).integrate(operation)
                        result.append(None) # We do not know the constants otherwise --> TODO: think about this
                    except IntegrationError:
                        # Dt is not the derivative of an element in self.base()
                        result.append(self.base().constant_ring(operation))
                    except NotImplementedError:
                        result.append(None)
                elif self.is_hyperexponential(operation):
                    ## See Theorem 5.1.2 of Bronstein's book
                    dt_t = self.base()(t.operation(operation)//t)
                    try:
                        if self.base().log_derivative_rad(dt_t, operation):
                            result.append(None) # we do not know
                        else:
                            result.append(self.base().constant_ring(operation))
                    except NotImplementedError:
                        result.append(None)
                    result.append(None) # Not implemented yet
                else:
                    result.append(None)
        return tuple(result)

    ## Attributes methods
    def varname(self) -> str:
        return self.__varname

    def gen(self) -> DMonomial_Element:
        if self.__gen is None:
            self.__gen = self.element_class(self, [self.base().zero(), self.base().one()])
        return self.__gen

    def gens(self) -> tuple[DMonomial_Element]:
        return (self.gen(),)

    def ngens(self) -> int:
        return 1

    def one(self) -> DMonomial_Element:
        return self.element_class(self, [self.base().one()])

    def zero(self) -> DMonomial_Element:
        return self.element_class(self, [self.base().zero()])

    def _first_ngens(self, amount: int) -> tuple[DMonomial_Element]:
        return self.tower_gens()[-amount:]

    def constant_ring(self, operation: int = 0) -> Parent:
        output = self.__constants[operation]
        if output is None:
            raise NotImplementedError(f"Constant ring for operation {operation} not yet implemented")
        return output

    @cached_method
    def tower_names(self) -> tuple[str]:
        r'''
            Returns the list of names of the generators of the tower of monomials
            in ascending order (as :func:`tower_gens`)
        '''
        result = (self.varname(),)
        current = self.base().base() # the first jump it the fraction field, then we go to the ring
        while isinstance(current, DMonomial_Parent):
            result = (current.varname(),)+result
            current = current.base().base()

        return result

    @cached_method
    def tower_gens(self) -> tuple[DMonomial_Element]:
        r'''
            Method to get the d-Monomial extension generators

            A tower of monomials is a chain of D-Monomial extensions. This method return a list of generators from bottom to top
            of the generators of the tower as element of ``self``.
        '''
        result = (self.gen(),)
        current = self.base().base() # the first jump it the fraction field, then we go to the ring
        while isinstance(current, DMonomial_Parent):
            result = (self(current.gen()),)+result
            current = current.base().base()

        return result

    def tower_gen(self, name: str) -> DMonomial_Element:
        gens = self.tower_gens()
        for g in gens:
            if str(g) == name:
                return g
        raise IndexError(f"Generator {name} not found")

    @cached_method
    def tower_gens_operation(self, operation: int) -> tuple[DMonomial_Element]:
        r'''
            Return the images of the tower generators for a given operation.

            A tower of monomials is a chain of D-Monomial extensions. This method return a list of images via an operation of generators from bottom to top
            of the generators of the tower as element of ``self``.
        '''
        return tuple(g.operation(operation) for g in self.tower_gens())

    @cached_method
    def tower_operations_for_gens(self) -> tuple[tuple[DMonomial_Element]]:
        return tuple(tuple(v.operation(i) for i in range(self.noperators())) for v in self.tower_gens())

    @cached_method
    def tower_base(self) -> Parent:
        r'''
            Return the base of the tower of monomials
        '''
        mid = self.base()
        current = mid.base()
        while isinstance(current, DMonomial_Parent):
            mid = current.base()
            current = mid.base()

        return mid

    def tower_depth(self) -> int:
        return len(self.tower_names())

    def tower_gen_lc(self, element: DMonomial_Element, gen: str) -> DFractionFieldElement:
        g = self.tower_gen(gen)
        shifted_gens = [G for G in self.tower_gens() if G != g] + [g]

        R = self.tower_change_order(*shifted_gens)
        return R(element).lc()

    def tower_gen_degree(self, element: DMonomial_Element, gen: str) -> DFractionFieldElement:
        g = self.tower_gen(gen)
        shifted_gens = [G for G in self.tower_gens() if G != g] + [g]

        R = self.tower_change_order(*shifted_gens)
        return R(element).degree()

    ## Other SageMath attribute methods for rings
    def is_field(self, _: bool = True) -> bool:
        return False

    def is_integral_domain(self, _: bool = True) -> bool:
        return True

    ## Derivation methods
    def extend_derivation(self, operation: int) -> AdditiveMap:
        def __derivation(element: DMonomial_Element) -> DMonomial_Element:
            return element.partial() * self.__images[operation] + element.kappa(operation)

        return AdditiveMap(self, __derivation)

    def extend_homomorphism(self, operation: int) -> AdditiveMap:
        def __homomorphism(element: DMonomial_Element) -> DMonomial_Element:
            return sum(
                (c.operation(operation)*self.__images[operation]**i
                for (i,c) in enumerate(element.coefficients(sparse=False))),
                start=self.zero()
            )

        return AdditiveMap(self, __homomorphism)

    def wronskian_matrix(self, operation: int = 0, *elements: DMonomial_Element) -> Matrix:
        if operation < 0 or operation >= self.noperators():
            raise ValueError(f"Invalid operation provided")
        elif self.operator_types()[operation] != "derivation":
            raise ValueError(f"The operation provided is not a derivation")

        return matrix([[el.operation(operation, times=i) for el in elements] for i in range(len(elements))])

    def wronskian(self, operation: int = 0, *elements: DMonomial_Element) -> DMonomial_Element:
        if operation < 0 or operation >= self.noperators():
            raise ValueError(f"Invalid operation provided")
        elif self.operator_types()[operation] != "derivation":
            raise ValueError(f"The operation provided is not a derivation")

        M = self.wronskian_matrix(operation, *elements)
        return M.determinant()

    def d_degree(self, operation: int = 0) -> int:
        return self.gen().operation(operation).degree()

    def d_leading_coefficient(self, operation: int = 0) -> Element:
        return self.gen().operation(operation).lc()

    d_lc = d_leading_coefficient

    def is_primitive(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] == "derivation":
            return self.d_degree(operation) == 0
        elif self.operator_types()[operation] == "homomorphism":
            raise NotImplementedError(f"Primitive test not yet implemented for homomorphisms")
        else:
            raise ValueError(f"Invalid operation provided")

    def is_hyper(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] in ("derivation", "homomorphism"):
            Dt = self.gen().operation(operation)
            q,r = Dt.quo_rem(self.gen())
            return r == 0 and q in self.base()
        else:
            raise ValueError(f"Invalid operation provided")

    def is_hyperexponential(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Invalid operation provided")
        return self.is_hyper(operation)

    def is_hypergeometric(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] != "homomorphism":
            raise ValueError(f"Invalid operation provided")
        return self.is_hyper(operation)

    def is_hypertangent(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Invalid operation provided")
        if self.d_degree(operation) == 2:
            t = self.gen()
            Dt = t.operation(operation)
            return Dt/(t**2 + 1) in self.base()
        return False

    def is_tangent(self, operation: int = 0) -> bool:
        if self.is_hypertangent(self, operation):
            t = self.gen()
            Dt = t.operation(operation)
            quot = self.base()(Dt/(t**2 + 1))

            try:
                quot.integrate()
                return True
            except (NotImplementedError, IntegrationError):
                return False

    def is_logarithm(self, operation: int = 0) -> bool:
        r'''
            `D(t)` is the logarithmic derivative on an element in ``self.base()``.
        '''
        if self.operator_types()[operation] != "derivation":
            raise NotImplementedError(f"Logarithm test not yet implemented for homomorphisms")
        t = self.gen()
        if self.is_primitive(operation):
            try:
                return bool(self.base().log_derivative(self.base()(t.operation(operation))))
            except NotImplementedError:
                return False
        return False

    def is_exponential(self, operation: int = 0) -> bool:
        if self.operator_types()[operation] != "derivation":
            raise NotImplementedError(f"Exponential test not yet implemented for homomorphisms")
        t = self.gen()
        if self.is_hyperexponential(operation):
            try:
                self.base()(t.derivative(operation)).integrate(operation)
                return True
            except (IntegrationError, NotImplementedError):
                return False
        return False

    def is_liouvillian(self, operation:int = 0) -> bool:
        r'''
            Checks whether the monomial is Liouvillian.

            A monomial is called Liouvillian if it is primitive or hyperexponential (see :func:`is_primitive` and :func:`is_hyperexponential`)
            and it preserve the constants of the base ring.
        '''
        if self.operator_types()[operation] != "derivation":
            raise NotImplementedError(f"Liouvillian test not yet implemented for homomorphisms")
        t = self.gen()
        return ((self.is_primitive(t) or self.is_hyperexponential(t)) and
                self.constant_ring(operation) == self.base().constant_ring())

    @cached_method
    def tower_is_liouvillian(self, operation: int = 0) -> bool:
        r'''
            Checks if the tower of monomial is all liouvillian.
        '''
        if self.is_liouvillian(operation):
            base = self.base().base()
            return (not isinstance(base, DMonomial_Parent)) or base.tower_is_liouvillian(operation)

    def is_elementary(self, operation: int = 0) -> bool:
        return self.is_liouvillian(operation) and (self.is_logarithm(operation) or self.is_exponential(operation))

    @cached_method
    def tower_is_elementary(self, operation: int = 0) -> bool:
        if self.is_elementary(operation):
            base = self.base().base()
            return (not isinstance(base, DMonomial_Parent)) or base.tower_is_elementary(operation)

    def is_simple_element(self, element: DMonomial_Element | DFractionFieldElement, operation: int = 0) -> bool:
        if element in self:
            return True
        elif element in self.fraction_field():
            return element.denominator().is_normal(operation)
        else:
            raise ValueError(f"Invalid element provided {element} for the parent {self}")

    def is_reduced_element(self, element: DMonomial_Element | DFractionFieldElement, operation: int = 0) -> bool:
        if element in self:
            return True
        elif element in self.fraction_field():
            return element.denominator().is_special(operation)
        else:
            raise ValueError(f"Invalid element provided {element} for the parent {self}")

    def canonical_representation(self,
                                 element: DMonomial_Element | DFractionFieldElement,
                                 operation: int = 0
    ) -> tuple[DMonomial_Element, DFractionFieldElement, DFractionFieldElement]:
        r'''
            Computes the canonical representation of an element in the field of fractions.

            This is algorithm CanonicalRepresentation described in Bronstein's book (page 101).

            Given an element on the field of fractions, this method returns a triple `(q, b, c)` such that
            ``self == q + b + c`` where
            * Denominator of `b` is a special polynomial.
            * Squarefree factors of the denominator of `c` are normal polynomials.
        '''
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Invalid operation provided")
        if isinstance(element, DFractionFieldElement):
            num, den = element.numerator(), element.denominator()
        elif isinstance(element, DMonomial_Element):
            num, den = element, self.one()
        else:
            raise TypeError(f"Invalid type for the element provided")

        num : DMonomial_Element = self(num)
        den : DMonomial_Element = self(den)

        if not den.is_monic(): # We guarantee `den` is monic
            num, den = num/den.lc(), den.monic()

        q,r = num.quo_rem(den)
        d_n, d_s = den.splitting_factorization(operation)
        b,c = d_n.diophantine(d_s, r) # deg(b) < deg(d_s)

        return (q, b/d_s, c/d_n)

    @cached_method
    def order_function(self, element: DMonomial_Element) -> DMM_OrderFunction:
        return DMM_OrderFunction(self, element)

    def order(self, base_element: DMonomial_Element, element: DMonomial_Element | DFractionFieldElement) -> int:
        return self.order_function(base_element)(element)

    @cached_method
    def value_function(self, element: DMonomial_Element) -> DMM_ValueFunction:
        return DMM_ValueFunction(self, element)

    def value(self, base_element: DMonomial_Element, element: DMonomial_Element | DFractionFieldElement) -> Element:
        return self.value_function(base_element)(element)

    @cached_method
    def residue_function(self, element: DMonomial_Element, operation: int = 0) -> DMM_ResidueFunction:
        return DMM_ResidueFunction(self, element, operation)

    def residue(self, base_element: DMonomial_Element, element: DMonomial_Element | DFractionFieldElement, operation: int = 0) -> Element:
        return self.residue_function(base_element, operation)(element)

    def rothstein_trager(self, element: DMonomial_Element | DFractionFieldElement, operation: int = 0, *, var_name: str) -> Element:
        r'''
            Computes the Rothstein-Trager resultant of an element in ``self.fraction_field()`` with respect to the operation provided.

            We uses the definition from Bronstein's book (page 122):

            .. MATH::

                \text{RT}(f) = \text{resultant}_t(a - z*D(d), d)

            where `f = p + a/d` is the element in the field of fractions, `D` is the derivation given by ``operation`` and `z` is a new variable (given with ``var_name``).
        '''
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Invalid operation provided: {operation} is {self.operator_types()[operation]}")
        elif not self.is_simple_element(element, operation):
            raise ValueError(f"Rothstein-Trager resultant defined only for simple elements.")

        _, _, fr = self.canonical_representation(element, operation) # first not relevant, second is zero since it is the special part
        a, d = fr.numerator(), fr.denominator()

        output_parent = PolynomialRing(self.to_sage().base(), [self.varname(), var_name])
        z = output_parent(var_name)
        first = output_parent(a.algebraic() - z*d.operation(operation).algebraic())
        second = output_parent(d.algebraic())
        return first.resultant(second)

    ## Coercion methods
    def _coerce_map_from_base_ring(self) -> Morphism:
        return DMM_BaseToParent(self)

    def construction(self) -> tuple[ConstructionFunctor, Parent]:
        return DMonomialFunctor(self.__varname, tuple(self.__images)), self.base()

    def fraction_field(self) -> DFractionField:
        if self.__fraction_field is None:
            self.__fraction_field = DFractionField(self)
        return self.__fraction_field

    def change_ring(self, new_base: Parent) -> DMonomial_Parent:
        old_base = self.base()
        if isinstance(old_base, DMonomial_Parent) and (not isinstance(new_base, DMonomial_Parent)):
            new_base = old_base.change_ring(new_base)

        output = DMonomial(new_base, tuple(str(img) for img in self.__images), self.varname())
        # coercion old -> new
        coercion = new_base.coerce_map_from(self.base())
        if coercion is not None:
            try:
                output.register_coercion(DMM_BetweenBases(self, output, coercion))
            except AssertionError:
                pass # the ring was already created
        # coercion new -> old
        coercion = self.base().coerce_map_from(new_base)
        if coercion is not None:
            try:
                self.register_coercion(DMM_BetweenBases(output, self, coercion))
            except AssertionError:
                pass # the ring was already created
        # conversion old -> new
        conversion = new_base.convert_map_from(self.base())
        if conversion is not None:
            try:
                output.register_conversion(DMM_BetweenBases(self, output, conversion))
            except AssertionError:
                pass # the ring was already created
        # conversion new -> old
        conversion = self.base().convert_map_from(new_base)
        if conversion is not None:
            try:
                self.register_conversion(DMM_BetweenBases(output, self, conversion))
            except AssertionError:
                pass # the ring was already created

        return output

    def tower_change_order(self, *new_variable_order: DMonomial_Element) -> DMonomial_Parent:
        tower_gens = self.tower_gens()
        if any(el not in tower_gens for el in new_variable_order) or len(tower_gens) != len(new_variable_order):
            raise ValueError(f"Impossible to reshape the tower of Monomials: bad data provided")

        images = tuple(tuple(str(v.operation(i)) for i in range(self.noperators())) for v in new_variable_order)
        try:
            output = DMonomial(self.tower_base(), images, names=tuple(str(v) for v in new_variable_order))
        except TypeError:
            raise ValueError(f"Impossible to reshape the tower of Monomials: the order is not valid")

        try:
            self.register_coercion(DMM_BetweenTowersReorder(output, self))
            output.register_coercion(DMM_BetweenTowersReorder(self, output))
        except AssertionError: # the coercion already existed
            pass

        return output

    ## Representation methods
    def __repr__(self) -> str:
        if self.tower_depth() == 1:
            return f"D-Monomial extension of {self.base()} with variable {self.varname()} where:\n\t* {self.varname()} -> {self.__images}"
        else:
            return f"Tower of D-Monomials over {self.tower_base()} with following monomials:\n\t* " + "\n\t* ".join(
                f"{v} -> {imgs}" for (v,imgs) in zip(self.tower_gens(), self.tower_operations_for_gens())
            )

    def _latex_(self) -> str:
        return (latex(self.base()) +
                        r"[" + latex_variable_name(self.varname()) +
                        r"\mapsto (" + ", ".join(latex(img) for img in self.__images) +
                        r")]")

    ## DRing category methods
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> DMonomial_Parent:
        return self.change_ring(self.base().add_constants(*new_constants))

    def _laurent_morphism(self, imgs, constant=None) -> MorphismToLaurent:
        r'''
            Internal implementation for :func:`DRings.ParentMethods.laurent_morphism`.
        '''
        # //TODO: Implement Laurent morphism
        raise NotImplementedError("Laurent morphism not implemented for DMonomial_Parent")

    def linear_operator_ring(self) -> DMonomial_Parent:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DMonomial_Element, operation: int = 0) -> DMonomial_Element:
        if self.operator_types()[operation] == "derivation":
            result = self.risch_de(self.zero(), element)
            if result is None:
                raise IntegrationError(f"The element {element} do not have an integral in-field.")
            return result
        raise NotImplementedError(f"The integration in these fields is not yet implemented")

    def _lcm_denominators(self, *_: DMonomial_Element) -> DMonomial_Element:
        return self.parent().one() # no denominators in this ring

    def to_sage(self):
        return self.__algebraic

    ########################################
    ### Methods from Bronstein book
    ########################################
    ### CHAPTER 5: INTEGRATION OF TRANSCENDENTAL FUNCTIONS
    def symbolic_integral(self, element: DFractionFieldElement, operation: int = 0) -> DMonomial_Element:
        partial, valid = self._symbolic_integral(element, operation)
        remainder = element - partial.operation(operation)
        if not valid:
            raise IntegrationError(f"Could not reduce to the base field\n\t-Start: {element}\n\t-Part.: {partial}\n\t-Remd.: {remainder}")
        remainder = self.base()(remainder)
        integral = self.base().symbolic_integral(remainder, operation)
        return integral + partial

    def _symbolic_integral(self, element: DFractionFieldElement, operation: int = 0) -> tuple[DMonomial_Element, tuple]:
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Symbolic integration only defined for derivations")

        f = self.fraction_field()(element) # must be a rational function

        g_1, h, r = self.hermite_reduce(f, operation) # reduces partial_integral, simple and reduced parts
        g_2, valid = self.residue_reduce(h, operation) # computes partial integral with `h - D(g_2)` polynomial
        if not valid:
            return (g_1 + g_2, valid)
        q, valid = self.polynomial_integration(h - g_2.operation(operation) + r, operation)
        return (g_1 + g_2 + q, valid)

    def hermite_reduce(self,
                       f: DFractionFieldElement,
                       D: int = 0
    ) -> tuple[DFractionFieldElement,DFractionFieldElement,DFractionFieldElement]:
        r'''
            Computes the Hermite reduction of an element in ``self.fraction_field()``.

            Given a derivation and an ``f=element`` in ``self.fraction_field()``, this method computes
            three values `g, h, r` in the same field such that

            .. MATH::

                f = D(g) + h + r

            and `h` is simple and `r` is reduced.
        '''
        p, s, n = self.canonical_representation(f, D)
        a, d = n.numerator(), n.denominator()
        ## We check `d` is monic
        if not d.is_monic():
            a, d = a/d.lc(), d.monic()

        F = d.squarefree()
        g = self.zero()

        for (d_i, i) in F:
            v = d_i
            u = d // d_i**i # this is an exact division since `d_i^i` is a factor of `d`
            for j in range(i-1, 0, -1):
                b,c = (u*v.derivative(D)).diophantine(v, -a/j)
                g += b/v**j
                a -= (j*c + u*b.derivative(D))
            d = u*v
        q,r = a.quo_rem(u*v)

        return (g, r/(u*v), q+p+s)

    def residue_reduce_base(self,
                       f: DFractionFieldElement,
                       D: int = 0
    ) -> tuple[DMonomial_Element, bool]:
        r'''
            Method that applies the Rothstein-Trager resultant reduction (page 147 of Bronstein's book)

            This method takes a simple element ``f = element`` in ``self.fraction_field()``, together with a
            derivation and returns a tuple `g, \beta` where `g` is an elementary function over ``self`` (includes
            some logarithms) and a boolean `\beta` such that

            * `\beta` is True if `f - D(g)` is an element of ``self``.
            * `\beta` is False if for any special element `h` in ``self.fraction_field()``, `f + h - D(g)` do not
              have an elementary integral.
        '''
        vname = f"__{self.gen()}"
        d = f.denominator()
        _,_,A = self.canonical_representation(f, D)
        a = A.numerator()

        r = self.rothstein_trager(f, D, vname) # algebraic polynomial in __t
        ## We create the differential structure to manipulate r
        E = DMonomial(self.base(), [0 for _ in range(self.noperators())], vname) # this is the \kappa_D
        r = E(r)
        r_n, r_s = r.splitting_factorization(D)
        F = r_s.factor() # factorization into irreducible factors of `r_s`
        monomials = [] # list of pairs (name, derivative, root) to be added
        for s_i,_ in F:
            for (alpha,_) in s_i.roots():
                nvar = RequestName.get(*[str(g) for g in self.tower_gens()])
                g = d.gcd(a - alpha*d.derivative(D))
                monomials.append((nvar, g.derivative(D)/g,alpha))

        E = DMonomial(self,
                      [[0 if i != D else m[1] for i in range(self.noperators())] for m in monomials],
                      [m[0] for m in monomials])
        result = sum(m[2]*E.tower_gen(m[0]) for m in monomials)

        return result, r_n in self.base()

    def residue_reduce(self,
                       f: DFractionFieldElement,
                       D: int = 0
    ) -> tuple[DMonomial_Element, bool]:
        r'''
            Method that applies the Lazard-Rioboo-Rothstein-Trager resultant reduction (page 149 of Bronstein's book)

            This method takes a simple element ``f = element`` in ``self.fraction_field()``, together with a
            derivation and returns a tuple `g, \beta` where `g` is an elementary function over ``self`` (includes
            some logarithms) and a boolean `\beta` such that

            * `\beta` is True if `f - D(g)` is an element of ``self``.
            * `\beta` is False if for any special element `h` in ``self.fraction_field()``, `f + h - D(g)` do not
              have an elementary integral.
        '''
        t = self.gen()
        d = self(f.denominator())
        p,a = self(f.numerator()).quo_rem(d) # f = p + a/d and `a` is normal

        AR = DMonomial(self, [0 for _ in range(self.noperators())], "__z") # we add new variable with \kappa_D
        z = AR.gen()
        if d.derivative(D).degree() <= d.degree():
            r, R = AR(d).subresultant_sequence(a-z*d.derivative(D))
        else:
            r, R = (a - z*d.derivative(D)).subresultant_sequence(d)

        r : DMonomial_Element
        Fn,Fs = r.splitting_factorization_squarefree(D)
        n = Fn.expand()

        S = dict()
        monomials = []
        for s,e in Fs: # for each factor on Fs
            if e == d.degree():
                for m in range(1,len(R)-1):
                    if self.tower_gen_degree(R[m], t) == e:
                        S[e] = R[m]
                A = self.tower_gen_lc(S[e], t).numerator().squarefree()
                for (a,e2) in A:
                    S[e] = S[e]//a.gcd(s)**e2
            for (alpha,_) in s.roots():
                b = self(S[e].algebraic()(**{"__z": alpha}))
                monomials.append((RequestName.get(*[str(g) for g in self.tower_gens()]), b.derivative(D)/b, alpha))

        E = DMonomial(self,
                      [[0 if i != D else m[1] for i in range(self.noperators())] for m in monomials],
                      [m[0] for m in monomials])
        result = sum(m[2]*E.tower_gen(m[0]) for m in monomials)

        return result, n in self.base()

    def polynomial_integration(self, element: DMonomial_Element, operation: int = 0) -> tuple[DMonomial_Element,bool]:
        if self.is_primitive(operation):
            return self._primitive_polynomial_integration(element, operation)
        elif self.is_hyperexponential(operation):
            return self._hyperexponential_polynomial_integration(element, operation)
        elif self.is_hypertangent(operation):
            return self._hypertangent_polynomial_integration(element, operation)
        elif self.d_degree(operation) > 1:
            logger.warning(f"[polynomial-integration] Case of non-linear monomial: we assume no special polynomials exists")
            return self._nonlinear_nospecial_polynomial_integration(element, operation)
        raise ValueError(f"Impossible error reached")

    def _primitive_polynomial_integration(self, p: DMonomial_Element, D: int = 0) -> tuple[DMonomial_Element,bool]:
        if p.degree() == 0:
            return self.zero(), True
        t = self.gen()
        a = p.lc()
        sol = self.base().base().limited_integrate(a, t.derivative(D), D=D)
        if sol is None:
            return self.zero(), False
        b,(c,) = sol # a = D(b) + cD(t) --> c is constant
        m = p.degree()
        q_0 = c*t**(m+1)/(m+1) + b*t**m
        q,valid = self._primitive_polynomial_integration(p - q_0.derivative(D), D)

        return q+q_0, valid

    def _hyperexponential_polynomial_integration(self, p: DMonomial_Element, D: int = 0) -> tuple[DMonomial_Element,bool]:
        q = 0
        valid = True
        t = self.gen()
        k = self.base()(t.derivative(D)/t)

        for i in range(t.order(p), -self.order_function(uoo)(p)+1):
            if i != 0:
                a = p.coefficient(i)
                ## Risch Differential Equation
                v = self.base().base().risch_de(i*k, a, D)
                if v is None:
                    valid = False
                else:
                    q += v*t**i
        return q, valid

    def _hypertangent_polynomial_integration(self, p: DMonomial_Element, D: int = 0) -> tuple[DMonomial_Element,bool]:
        q_1, valid = self._hypertangent_reduced_integration(p, D)
        if not valid:
            return q_1, valid
        q_2, c = self._hypertangent_polynomial_integration_pure(p - q_1.derivative(D), D)
        if c.derivative(D) == 0:
            t = self.gen()
            k = self.base()(t.derivative(D) / (t**2-1))
            new_var = RequestName.get(*[str(g) for g in self.tower_gens()])
            E = DMonomial(self, ["0" if i == D else f"2*{t}*{k}" for i in range(self.noperators())], new_var)
            log_t2_1 = E.gen()
            return q_1+q_2+c*log_t2_1, True
        else:
            return q_1+q_2, False

    def _hypertangent_polynomial_integration_pure(self,
                                                  p: DMonomial_Element,
                                                  D: int = 0
    ) -> tuple[DMonomial_Element,DFractionFieldElement]:
        r'''
            Method to integrate a pure polynomial for hypertangent monomials.

            Given a polynomial `p(t) \in k[t]` (`k[t]` is ``self``), this method computes
            a polynomial `q(t) \in k[t]` and an element `c \in k` such that

            .. MATH::

                p - D(q) - c \frac{D(t^2 + 1)}{t^2 + 1} \in k

            and `p - D(q)` has an elementary integral over `k(t)` if and only if `D(c) = 0`.
        '''
        q,r = self.polynomial_reduce(p, D)
        t = self.gen()
        k = self.base()(t.derivative(D) / (t**2 + 1))
        c = r.coefficient(1)/2*k
        return q, c

    def _hypertangent_reduced_integration(self, p: DMonomial_Element, D: int = 0) -> tuple[DMonomial_Element,bool]:
        t = self.gen()
        td = t**2 + 1
        m = td.order(t)
        if m <= 0:
            return 0, True

        h = self(td**m * p) # h is now a polynomial in `t`
        r = h % td # deg(r) <= 1
        a = r.coefficient(1) # a = coeff(r, t)
        b = r.cc() # b = coeff(r, 1) = r - a*t
        k = self.base()(t.derivative(D) / td)

        sol = self.base().coupled_de_system(0, 2*m*k, a, b, D)
        if sol is None: # no solution to coupled system
            return self.zero(), False
        c,d = sol # D(c) - 2m D(t)/(t^2+1) d = a,   D(d) + 2m D(t)/(t^2+1)c = b

        q_0 = (c*t + d)/(t**2+1)**m
        q, valid = self._hypertangent_reduced_integration(p - q_0.derivative(D), D)
        return (q+q_0, valid)

    def _nonlinear_nospecial_polynomial_integration(self, p: DMonomial_Element, D: int = 0) -> tuple[DMonomial_Element,bool]:
        q_1, q_2 = self.polynomial_reduce(p, D)

        return q_1, q_2 in self.base()

    def polynomial_reduce(self,
                       p: DMonomial_Element,
                       D: int = 0
    ) -> tuple[DMonomial_Element,DMonomial_Element]:
        r'''
            Computes a polynomial reduction.

            Given a polynomial `p(t) \in k[t]` (where `k[t]` is ``self``) where `t` is a nonlinear monomial,
            this method computes two polynomials `q(t), r(t) \in k[t]` such that `p = D(q) + r` and
            `deg(r) < deg(D(t))`.

            This method looks like an Euclidean division but using now the derivative of the monomial.
        '''
        p = self(p)
        if p.degree() < self.d_degree(D):
            return self.zero(), p

        m = p.degree() - self.d_degree(D) + 1
        q_0 = (p.lc() / (m*self.d_lc(D))) * self.gen()**m
        q, r = self.polynomial_reduce(p - q_0.derivative(D), D)

        return q_0 + q, r

    ### CHAPTER 6: Risch Differential Equation
    def risch_de(self, f: DFractionFieldElement, g: DFractionFieldElement, D:int = 0) -> DFractionFieldElement:
        ## Checking the input of the algorithm
        f = self.fraction_field()(f)
        g = self.fraction_field()(g)

        if self.operator_types()[D] != "derivation":
            raise ValueError(f"The given operator is not a derivation")

        ## We first weakly normalize the element `f`
        q = self._weak_normalizer(f, D)
        f = f - q.derivative(D)/q
        g = g*q
        ## We now solve the equation D(z) + (f-D(q)/q) z = qg and the solution y is z/q
        ## We compute the normal part of the denominator
        normal = self._rde_normal_denominator(f,g,D)
        if normal is None:
            return None

        a,b,c,dn = normal
        ## We now solve the equation aD(w) + b w = c for reduced solutions and the solution z is w/dn
        ## We compute the special part of the denominator
        special = self._rde_special_denominator(a,b,c,D)
        if special is None:
            return None
        a,b,c,ds = special
        ## We now solve the equation aD(v) + b v = c for polynomial solutions and the solution w is v/ds
        ## We compute now the degree bound for a polynomial solution
        deg_bound = self._rde_degree_bound(a,b,c,D)

        ## We now reduce back to a Risch Differential Equation with polynomials
        spde = self._rde_spde(a,b,c,deg_bound,D)
        if spde is None:
            return None
        b,c,m,alpha,beta = spde
        ## We now solve the equation D(u) + bu = c for polynomial solutions and the solution v is alpha*u + beta
        ## with bounded degree m
        u = self._rde_polynomial(b,c,m,D)
        if u is None:
            return None

        ## Now we reconstruct all the way back
        v = alpha*u + beta
        w = v/ds
        z = w/dn
        y = z/q

        return y

    def _weak_normalizer(self, f: DFractionField, D: int = 0) -> DMonomial_Element:
        r'''
            Given a derivation `D` and a rational function `f(t) \in K(t)` (where ``self`` is `K[t]`), this method computes
            a polynomial `q(t) \in K[t]` such that `f(t) - D(q(t))/q(t)` is weakly normalized.

            Definition: a rational function `f(t) \in K(t)` is weakly normalized if its residue is not a positive integer for
            any normal irreducible `p(t) \in K[t]` such that `f(t)` has order at least `-1`.

            Note: let `f(t) = n(t)/d(t)` with `(n(t), d(t)) = 1`. Let `p(t)` be a normal polynomial (i.e., `(p,D(p)) = 1`)
            that we consider for this definition (i.e., the order of `f(t)` is at least -1). Then we have two cases:
            * `f(t) \in \mathcal{O}_p`, i.e., the order is at least 0. Then the residue is exactly 0 (no problem).
            * `p(t)` divides exactly once to `d(t)`. Then, we can write `d(t) = q(t)p(t)` with `q(t)` coprime with `p(t)`.
              In this case, the residue is the class of `n(t)/(D(p(t))q(t))`.

            So the only normal polynomials that we need to consider are those that divides the denominator of self exactly once,
            or said differently, those normal factors of the degree 1 factor from the squarefree factorization of ``d(t)``.
            This fact allows to focus on these factors to compute a weakly normalized element from ``f(t)`` by subtracting
            a logarithmic derivative of a polynomial.
        '''
        dn,_ = f.denominator().splitting_factorization(D)
        g = dn.gcd(dn.partial()) # gcd(d_n, d(d_n)/dt)
        d_ = dn//g # exact division
        d_1 = d_//d_.gcd(g)

        a = (f.denominator()//d_1).diophantine_half_euclidean(d_1, f.numerator())

        E = DMonomial(self, [0 for _ in range(self.noperators())], "__z") # added new variable with the `kappa_D` derivation
        t = self.gen()
        z = E.gen()
        gs = E.tower_gens()[:-2]
        Et = E.tower_change_order(*gs, z, t)
        p = Et(a - z*d_1.derivative(D))
        r = p.resultant(Et(d_1))
        ## Taking positive integer roots
        roots = r.to_sage().roots()
        roots = [r for r,_ in roots if (r in ZZ and r > 0)]

        return prod(d_1.gcd(a-r*d_1.derivative(D))**r for r in roots)

    def _rde_normal_denominator(self,
                                f: DFractionFieldElement,
                                g: DFractionFieldElement,
                                D: int = 0
    ) -> None | tuple[DMonomial_Element, DFractionFieldElement, DFractionFieldElement, DMonomial_Element]:
        r'''
            Method to compute the normal part of the denominator for a solution to a Risch Differential Equation.

            Let us consider the Risch Differential Equation `D(y) + fy = g` for given `f(t), g(t) \in K(t)` (note
            that ``self`` is `K[t]`) where `f(t)` is weakly normalized (see :func:`_weak_normalizer`).

            This method returns either ``None`` if there is no solution to this Risch Differential Equation or
            a tuple of elements `a(t), b(t), c(t), h(t)` where:
            * `a(t), h(t)` are elements of ``self`` (i.e., `K[t]`),
            * `b(t), c(t)` are reduced rational functions (i.e., their denominators are special polynomials),
            such that for any rational solution `y(t)` to the Risch Differential Equation defined by `f(t)` and
            `g(t)`, then `q(t) = y(t)h(t)` is a reduced rational function solution to `aD(q) + bq = c`.

            EXAMPLE::

            sage: from dalgebra import *
            sage: R.<t> = DMonomial(DifferentialRing(QQ), [1]) # D = d/dt
            sage: R._rde_normal_denominator(1, 1/t) is None
            True
            sage: R.<x,t> = DMonomial(DifferentialRing(QQ), [1, "1+t^2"]) # D(x) = 1, D(t) = 1 + t^2
            sage: R._rde_normal_denominator(t^2 + 1, 1/t^2)
            (t, t^3 - t^2 + t - 1, 1, t)
        '''
        dn,_ = f.denominator().splitting_factorization(D)
        en,_ = g.denominator().splitting_factorization(D)
        p = dn.gcd(en)
        h = en.gcd(en.partial())/p.gcd(p.partial())

        if (dn*h**2) % en != 0:
            return None
        return (dn*h, dn*h*f - dn*h.derivative(D), dn*h**2*g, h)

    def _rde_special_denominator(self,
                                 a: DMonomial_Element, # leading coefficient of the diff. equation
                                 b: DFractionFieldElement, # reduced coefficient multiplying the function
                                 c: DFractionFieldElement, # reduced inhomogeneous term
                                 D: int = 0 # derivation
    ) -> None | tuple[DMonomial_Element,DMonomial_Element,DMonomial_Element,DMonomial_Element]:
        r'''
            Computes the special part of the denominator of a solution.

            Given elements `a(t) \in K[t]` and `b(t),c(t) \in K(t)` (both reduced rational functions), this method
            computes new elements `\tilde{a}(t), \tilde{b}(t), \tilde{c}(t), h(t) \in K[t]` such that for any reduced solution
            `y(t)` to the equation

            .. MATH::

                a(t)D(y(t)) + b(t)y(t) = c(t),

            the function `q(t) = y(t)h(t)` is a polynomial solution to the differential equation

            .. MATH::

                \tilde{a}(t)D(q(t)) \tilde{b}(t)q(t) = \tilde{c}(t).

            If no such solution exists, the method returns ``None``.
        '''
        if self.is_primitive(D):
            ## This case there are no special polynomials --> we are already in the polynomial case
            return (self(a), self(b), self(c), self.one())
        elif self.is_hyperexponential(D): # hyperexponential case
            ## See page 186 of Bronstein's book
            t = self.gen()
            Dt_t = self.base()(t.derivative(D)/t)
            nu_t = t.order_function()
            n_b, n_c = nu_t(b), nu_t(c)
            n = min(0, n_c - min(0,n-b))

            if n_b == 0: # possible cancellation case
                alpha = t.remainder(-b/a) # alpha in self.base()
                ## We check if \alpha = m Dt/t + Dz/z for some z in self.base()
                ## That is a parametric logarithmic derivative problem
                par_log_der = self.base().log_derivative_param(alpha, t)
                if par_log_der is not None and par_log_der[1] == 1:
                    n = min(n, par_log_der[2])
            N = max(0, -n_b, n - n_c)
            return (a*t**N, (b+n*a*Dt_t)*t**N, c*t**(N-n), t**(-n))
        elif self.is_hypertangent(D): # hypertangent case
            raise NotImplementedError(f"[Special Part RDE] Hypertangent case not yet implemented. Look into page 188 of Bronstein's book")
        else:
            raise NotImplementedError(f"[Special Part RDE] The case of a monomial {self.gen()} -> {self.gen().derivative()} is not implemented")

    def _rde_degree_bound(self,
                          a: DMonomial_Element,
                          b: DMonomial_Element,
                          c: DMonomial_Element,
                          D: int = 0
    ) -> int:
        r'''
            Computes degree bound for polynomial solution of the reduced Risch Differential Equation.

            Given polynomials `a(t), b(t), c(t) \in K[t]` this method computes a degree bound `m`
            such that all polynomial solution `y(t)` to the equation `a(t)D(y(t)) + b(t)y(t) = c(t)`
            has a degree bounded by `m`.
        '''
        t = self.gen()
        d_a, d_b, d_c = a.degree(), b.degree(), c.degree()
        if self.is_primitive(D):
            if t.derivative(D) == 1 and self.constant_ring(D) == self.base(): # special case where derivation is just standard derivation w.r.t. t
                n = max(0, d_c - max(d_b, d_a - 1))
                if d_b == d_a - 1: ## possible cancellation
                    m = -b.lc()/a.lc()
                    if m in ZZ:
                        n = max(0, m, d_c - d_b)
            else: # generic primitive case
                n = max(0, d_c-d_b) if d_b > d_a else max(0, d_c - d_a + 1)
                if d_b == d_a - 1: ## possible cancellation
                    alpha = -b.lc()/a.lc()
                    Dt = t.derivative(D)
                    lim_int = self.base().limited_integration(alpha, Dt)
                    if lim_int is not None and lim_int[1][0] in ZZ:
                        n = max(n,lim_int[1][0])
                elif d_b == d_a:
                    alpha = -b.lc()/a.lc()
                    z = self.base().log_derivative(alpha)
                    if z is not None:
                        beta = -(a*z.derivative(D) + b*z).lc() / (z*a.lc())
                        lim_int = self.base().limited_integration(beta, Dt)
                        if lim_int is not None and lim_int[1][0] in ZZ:
                            n = max(n,lim_int[1][0])
        elif self.is_hyperexponential(D): # hyperexponential case
            n = max(0, d_c - max(d_b, d_a))
            if d_a == d_b: ## possible cancellation
                alpha = -b.lc() / a.lc()
                par_log_der = self.base().log_derivative_param(alpha, t)
                if par_log_der is not None and par_log_der[1] == 1:
                    n = max(par_log_der[2], n)
        else:
            n = max(0, d_c - max(d_a+self.d_degree(D)-1, d_b))
            if d_b == d_a + self.d_degree(D) - 1: # possible cancellation
                m = -b.lc()/(self.d_lc()*a.lc())
                if m in ZZ:
                    n = max(0, ZZ(m), d_c - d_b)
        return n

    def _rde_spde(self,
                  a: DMonomial_Element,
                  b: DMonomial_Element,
                  c: DMonomial_Element,
                  n: int,
                  D: int = 0
    ) -> None | tuple[DMonomial_Element, DMonomial_Element, int, DMonomial_Element, DMonomial_Element]:
        r'''
            Reduces the SPDE problem to a polynomial Risch Differential Equation.

            Given polynomials `a(t), b(t), c(t) \in K[t]` and a degree bound `n`, this method computes new
            elements `\tilde{b}(t), \tilde{c}(t) \in K[t]`, a new bound `m \in \mathbb{N}` and elements
            `\alpha(t),\beta(t) \in K[t]` such that any polynomial solution `y(t)` to

            .. MATH::

                a(t) D(y(t)) + b(t)y(t) = c(t)

            of degree bounded by `n`, can be written as `y(t) = \alpha(t) q(t) + \beta(t)`, where `q(t)` is
            a solution to a polynomial Risch Differential Equation

            .. MATH::

                D(q(t)) + \tilde{b}(t)q(t) = \tilde{c}(t)

            with degree bounded by `m`.

            This method returns ``None`` if there is no such type of solutions.
        '''
        if n < 0:
            if c == 0:
                return (self.zero(), self.zero(), 0, self.zero(), self.zero())
            else:
                return None

        g = a.gcd(b)
        if c % g != 0:
            return None

        a, b, c = a//g, b//g, c//g

        if a.degree() == 0:
            return (b/a.lc(), c/a.lc(), n, self.one(), self.zero())

        r, z = b.diophantine(a, c)
        u = self._rde_spde(a, b+a.derivative(D), z - r.derivative(D), n-a.degree(), D)
        if u is None:
            return None

        B,C,M,alpha,beta = u
        return (B, C, M, a*alpha, a*beta + r)

    def _rde_polynomial(self,
                        b: DMonomial_Element,
                        c: DMonomial_Element,
                        n: int,
                        D: int = 0
    ) -> None | DMonomial_Element:
        r'''
            Method that solves the polynomial Risch Differential Equation for given degree bound.

            Let `b(t), c(t)\in K[t]` be two polynomials and `n` a non-negative integer. This method computes
            a solution (or ``None`` if it does not exits) to the Risch Differential Equation

            .. MATH::

                D(y(t)) + b(t) y(t) = c(t),

            for `y(t) \in K[t]` of degree bounded by `n`.
        '''
        ## We check if this is a cancellation case
        ## The cancellation may happen when deg(D(y(t))) = deg(b) + deg(y)
        ## Since D(y(t)) = kappa_D(y(t)) + D(t)*partial_t(y), then
        ## deg(D(y(t))) <= max(deg(y(t)), deg(y(t)+deg(D(t))-1)) (with equality for non-linear monomials)
        ## Going back to our equation, we can not have cancellation if
        ## the degree of b(t) is too big (> max(0, deg(D(t))-1)),
        ## or if it is too small (in the non-linear case, < max(0, deg(D(t))-1))
        if self.d_degree(D) >= 2 or b.degree() > max(0, self.d_degree(D) - 1):
            return self._rde_polynomial_no_cancellation(b,c,n,D)
        else:
            return self._rde_polynomial_cancellation(b,c,n,D)

    def _rde_polynomial_no_cancellation(self,
                                        b: DMonomial_Element,
                                        c: DMonomial_Element,
                                        n: int = uoo,
                                        D: int = 0
    ) -> None | DMonomial_Element:
        t = self.gen()
        q = self.zero()
        if b.degree() > max(0, self.d_degree(D) - 1): ## deg(b) is too big
            while c != 0:
                m = c.degree() - b.degree()
                if n < 0 or m < 0 or m > n:
                    return None
                p = (c.lc()/b.lc())*t**m
                q += p
                n = m-1
                c -= (p.derivative(D) + b*p)
        elif b.degree() < self.d_degree(D) - 1: ## we know deg(D(t)) > 1, and now deg(b) is too small
            while c != 0:
                m = 0 if n == 0 else c.degree() - self.d_degree(D) + 1
                if n < 0 or m < 0 or m > n:
                    return None
                if m > 0:
                    p = (c.lc()/(m*self.d_lc()))*t**m
                else: # m == 0
                    if b.degree() != c.degree():
                        return None
                    elif b.degree() == 0:
                        ## Solution on base field here
                        y = self.base().risch_de(self.base()(b),self.base()(c))
                        return y + q
                    p = c.lc()/b.lc()
                q += p
                n = m - 1
                c -= (p.derivative(D) + b*p)
        else: # case with non-linear and deg(b) == deg(D(t))
            N = -b.lc()/self.d_lc()
            M = N if N in ZZ and ZZ(N) >= 0 else -1

            while c != 0:
                m = max(M, c.degree() - self.d_degree(D) + 1)
                if n < 0 or m < 0 or m > n:
                    return None
                u = m*self.d_lc() + b.lc()
                if u == 0:
                    ## Recursion of the Risch D.E.
                    return self._rde_polynomial(b, c, m, D)
                if m > 0:
                    p = (c.lc()/u)*t**m
                else:
                    if c.degree() != self.d_degree(D) - 1:
                        return None
                    p = c.lc()/b.lc()
                q += p
                n = m - 1
                c -= (p.derivative(D) + b*p)
        return q

    def _rde_polynomial_cancellation(self,
                                        b: DMonomial_Element,
                                        c: DMonomial_Element,
                                        n: int = uoo,
                                        D: int = 0
    ) -> None | DMonomial_Element:
        t = self.gen()
        q = self.zero()
        if self.is_primitive(D):
            ## in this case we know that `b` is in self.base()
            z = self.base().log_derivative(self.base()(b))
            if z is not None:
                p = self._rde_polynomial(self.zero(), z*c, n, D)
                if p is not None:
                    return p/z
                return None
            if c == 0:
                return self.zero()
            if n < c.degree():
                return None

            while c != 0:
                m = c.degree()
                if n < m:
                    return None
                s = self.base().risch_de(self.base()(b), c.lc(), D)
                if s is None:
                    return None
                q += s*t**m
                n = m - 1
                c -= (b*s*t**m + (s*t**m).derivative(D))
        elif self.is_hyperexponential(D):
            log_der_param = self.log_derivative_rad_param(self.base()(b), self.base()(t.derivative(D)/t), D)
            if log_der_param is not None:
                z, N, m = log_der_param
                if N == 1 and m in ZZ:
                    p = self.risch_de(self.zero(), c*z*t**m, D)
                    if p is not None and self.is_reduced_element(p, D):
                        try:
                            q = self(p/z*t**m)
                            if q.degree() <= n:
                                return q
                        except Exception:
                            pass
                    else:
                        return None
            if c == 0:
                return self.zero()
            if n < c.degree():
                return None
            while c != 0:
                m = c.degree()
                if n < m:
                    return None
                s = self.base().risch_de(self.base()(b + m*t.derivative(D)/t), c.lc())
                if s is None:
                    return None
                q += s*t**m
                n = m - 1
                c -= (b*s*t**m + (s*t**m).derivative(D))
        else:
            raise NotImplementedError(f"[Poly R.D.E. Cancellation] Non-linear case not yet implemented")
        return q
    ### CHAPTER 7: Parametric Problems
    def limited_integrate(self, f, *w, D: int = 0) -> tuple[DMonomial_Element, tuple[DMonomial_Element]]:
        raise NotImplementedError(f"Method of limited integration not yet implemented")

    ### CHAPTER 8: The Coupled Differential System
    def coupled_de_system_generic(self,
                                  a: DFractionFieldElement, # must be constant
                                  b1: DFractionFieldElement, b2: DFractionFieldElement, # coefficients of the system
                                  c1: DFractionFieldElement, c2: DFractionFieldElement, # inhomogeneous part
                                  D: int = 0, # derivative we are integrating
                                  n: int = uoo # bound for degree of solutions
    ) -> tuple[DMonomial_Element, DMonomial_Element]:
        raise NotImplementedError(f"Generic coupled DE System not yet implemented.")


#####################################
### FUNCTOR CLASS
#####################################
class DMonomialFunctor (ConstructionFunctor):
    r'''
        Class for a functor that creates a d-monomial extension.

        It receives the name of the new added variable and the images of the variable
        in a string/element format.
    '''
    def __init__(self, varname: str, images: tuple[str | Element]):
        super().__init__(_DRings,_DRings)
        self.rank = 10 # just below DPolyRingFunctor

        self.__varname = varname
        self.__images = images

    def _apply_functor(self, x):
        return DMonomial(x, self.__images, self.__varname)

    def _repr_(self) -> str:
        return f"DMonomial(*, {self.__images}, {self.__varname})"

    def __eq__(self, other) -> bool:
        if not isinstance(other, DMonomialFunctor):
            return False
        return self.__varname == other.__varname and self.__images == other.__images


class DMonomialLaurentMorphism(MorphismToLaurent):
    r'''
        Laurent morphism class associated with :class:`DMonomial_Parent`.
    '''
    # //TODO: Implement DMonomialLaurentMorphism
    pass


#####################################
### MORPHISM CLASSES
#####################################
### COERCIONS / CONVERSIONS MORPHISMS
class DMM_ParentToBase (Morphism):
    def __init__(self, parent):
        super().__init__(parent, parent.base())

    def _call_(self, element: DMonomial_Element) -> Element:
        if not element.degree() == 0:
            raise ValueError(f"{element} is not a constant element")
        return element[0]


class DMM_BaseToParent (Morphism):
    def __init__(self, parent):
        super().__init__(parent.base(), parent)

    def _call_(self, element: Element) -> DMonomial_Element:
        return self.codomain().element_class(self.codomain(), [element])


class DMM_ParentToAlgebraic (Morphism):
    def __init__(self, domain: DMonomial_Parent):
        super().__init__(domain, domain.to_sage())

    def _call_(self, element: DMonomial_Element) -> Element:
        v = self.codomain()(self.domain().varname())
        return sum(
            (self.codomain().base()(c.to_sage())*v**m.degree() for (m,c) in element.mons_cons_iter()),
            start=self.codomain().zero()
        )


class DMM_AlgebraicToParent (Morphism):
    def __init__(self, codomain: DMonomial_Parent):
        super().__init__(codomain.to_sage(), codomain)

    def _call_(self, element: Element) -> DMonomial_Element:
        if isinstance(self.domain(), MPolynomialRing_base):
            element = element.polynomial(self.codomain()(self.domain().varname()))
        elif not isinstance(self.domain(), PolynomialRing_generic):
            raise TypeError(f"Weird algebraic ring for a d-Monomial extension")

        return self.codomain().element_class(
            self.codomain(),
            [
                self.codomain().base()(c)
                for c in element.coefficients(sparse=False)
            ]
        )


class DMM_BetweenBases (Morphism):
    def __init__(self,
                             domain: DMonomial_Parent,
                             codomain: DMonomial_Parent,
                             map_bases: Morphism):
        if not (map_bases.domain() == domain.base() and map_bases.codomain() == codomain.base()):
            raise TypeError(f"Incompatible map given for coercion between bases")
        self.__map_bases = map_bases
        super().__init__(domain, codomain)

    def _call_(self, element: DMonomial_Element) -> DMonomial_Element:
        return self.codomain().element_class(
            self.codomain(),
            [
                self.__map_bases(c) for c in element.coefficients(sparse=False)
            ]
        )


class DMM_BetweenTowersReorder (Morphism):
    def __init__(self,
                         domain: DMonomial_Parent,
                         codomain: DMonomial_Parent):
        if set(str(v) for v in domain.tower_gens()) != set(str(v) for v in codomain.tower_gens()):
            raise ValueError(f"The two tower of monomials do not have the same variables")

        super().__init__(domain, codomain)

        ## We check if the operations are the same
        for v in domain.tower_gens():
            if any(self(v).operation(i) != self(v.operation(i)) for i in range(domain.noperators())):
                raise ValueError(f"The operation of variable {v} do not match")

    def _call_(self, element: DMonomial_Element) -> DMonomial_Element:
        return self.codomain()(self.codomain().to_sage()(str(element)))


### ORDER MORPHISMS
class DMM_OrderFunction (Morphism):
    def __init__(self, parent: DMonomial_Parent, element: DMonomial_Element):
        from sage.categories.sets_cat import cartesian_product
        super().__init__(parent.fraction_field(), cartesian_product([ZZ,UnsignedInfinityRing]))
        self.__a = oo if element is oo else parent(element)

    def _call_(self, element: DFractionFieldElement) -> int:
        no,ns = self.order(element.numerator()) # ns may be infinite
        do,_ = self.order(element.denominator()) # ds can not be infinite
        return self.codomain()((no-do, UnsignedInfinityRing(ns+no-do)))

    @cached_method
    def order(self, element: DMonomial_Element) -> int:
        if self.__a is oo: # case of order at infinity
            output = -element.degree()
        elif self.__a.is_unit():
            output = oo
        else: # case of order at a fixed element `a`
            if element == 0:
                output = oo # order of zero is infinity
            else:
                q, r = element.quo_rem(self.__a)
                order = 0

                while r == 0:
                    order += 1
                    q,r = q.quo_rem(self.__a)

                output = ZZ(order)
        return self.codomain()((ZZ(output) if output is not oo else ZZ(0), UnsignedInfinityRing(output)))


class DMM_ValueFunction (Morphism):
    def __init__(self, parent: DMonomial_Parent, element: DMonomial_Element):
        if element is oo:
            self.__I = None
            self.__a = oo
            self.__parent = parent
            super().__init__(parent.fraction_field(), parent.base().fraction_field())
        else:
            self.__I : Ideal = ideal(element.algebraic())
            self.__a = parent(element)
            self.__parent = parent
            super().__init__(parent.fraction_field(), parent.to_sage().quotient(self.__I))

    def _call_(self, element: DFractionFieldElement) -> Element:
        order_element = self.__parent.order_function(self.__a)(element)
        if order_element[1] != uoo and order_element[0] < 0:
            raise ValueError(f"Value function only valid for elements with positive order at {self.__a}")
        if self.__a is oo:
            if order_element[0] > 0:
                return self.codomain().zero()
            else:
                return element.numerator().lc() / element.denominator().lc()
        else:
            b = element.numerator()
            d,_ = element.denominator().gcd_half_extended_euclidean(self.__a)
            return self.codomain()((b*d).algebraic())


class DMM_ResidueFunction (Morphism):
    def __init__(self, parent: DMonomial_Parent, element: DMonomial_Element, operation: int = 0):
        if parent.operator_types()[operation] != "derivation":
            raise TypeError(f"The operation must be a derivation (given {operation}: {parent.operator_types()[operation]})")
        if element is oo:
            raise NotImplementedError(f"Residue function not yet implemented for infinity")
        else:
            if not element.is_normal():
                raise ValueError(f"Residue function only valid for normal elements")
            self.__a = parent(element)
            self.__operation = operation
            self.__value_function = parent.value_function(element)
            super().__init__(parent.fraction_field(), self.__value_function.codomain())

    def _call_(self, element: DFractionFieldElement) -> Element:
        return self.__value_function(element * self.__a / self.__a.operation(self.__operation))


__all__ = ["DMonomial", "DMM_ValueFunction"]