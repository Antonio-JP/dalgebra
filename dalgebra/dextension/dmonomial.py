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

from ..dring import AdditiveMap, DRings, DFractionField, DFractionFieldElement

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
    def create_key(self, base, polynomial: str | Element, varname: str = None, *, names: tuple[str] = None, category = None):
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
        return tuple((m,c) for (m,c) in self.mons_cons_iter())

    def factor(self) -> Factorization:
        f = self.algebraic().factor()
        return Factorization([(self.parent()(p), e) for (p,e) in f], self.parent().base()(f.unit()))

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

    ## Other functions
    def __repr__(self) -> str:
        return repr(self.algebraic())
    
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
            s, t = r, t+ q*self
        
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
            s = s%other
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

        assert r==0

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
            1 * x^2 * (x^2 + 2)^3
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
            1 * x^2 * (x^2 + 2)^3
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

    def order(self, element: DMonomial_Element) -> int:
        return element.order_function()(self)
    
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
        if not base in _Fields or not base in _DRings:
            raise TypeError(f"The base must be a field and have d-operations")
        
        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## Variables for cached attributes
        self.__varname = varname
        self.__algebraic = None
        self.__images = None
        self.__gen = None
        self.__operators = None

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
        self.__algebraic.register_coercion(DMM_ParentToAlgebraic(self))
        self.register_coercion(DMM_AlgebraicToParent(self))

    def _initialize_data(self, images: tuple[str]):
        self.__images = tuple(self(self.to_sage()(img)) for img in images)

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
                start = self.zero()
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
            return self.gen().operation(operation) in self.base()
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
        
    def is_hyperexponential(self, operation) -> bool:
        if self.operator_types()[operation] != "derivation":
            raise ValueError(f"Invalid operation provided")
        return self.is_hyper(operation)
    
    def is_hypergeometric(self, operation) -> bool:
        if self.operator_types()[operation] != "homomorphism":
            raise ValueError(f"Invalid operation provided")
        return self.is_hyper(operation)
    
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
    
    def order(self, base_element: DMonomial_Element, element: Element) -> int:
        return self.order_function(base_element)(element)

    ## Coercion methods
    def _coerce_map_from_base_ring(self) -> Morphism:
        return DMM_BaseToParent(self)
    
    def construction(self) -> tuple[ConstructionFunctor, Parent]:
        return DMonomialFunctor(self.__varname, tuple(self.__images)), self.base()
    
    def fraction_field(self) -> DFractionField:
        return DFractionField(self)
    
    def change_ring(self, new_base: Parent) -> DMonomial_Parent:
        old_base = self.base()
        if isinstance(old_base, DMonomial_Parent) and (not isinstance(new_base, DMonomial_Parent)):
            new_base = old_base.change_ring(new_base)
        
        output = DMonomial(new_base, self.varname(), tuple(str(img) for img in self.__images))
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
                output.register_coercion(DMM_BetweenBases(output, self, coercion))
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
                output.register_conversion(DMM_BetweenBases(output, self, conversion))
            except AssertionError:
                pass # the ring was already created
    
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
        return self.change_base(self.base().add_constants(*new_constants))
    
    def linear_operator_ring(self) -> DMonomial_Parent:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DMonomial_Element, operation: int = 0) -> DMonomial_Element:
        raise NotImplementedError(f"The integration in these fields is not yet implemented")
        
    def _lcm_denominators(self, *_: DMonomial_Element) -> DMonomial_Element:
        return self.parent().one() # no denominators in this ring

    def to_sage(self):
        return self.__algebraic
    
#####################################
### FUNCTOR CLASS
#####################################
class DMonomialFunctor (ConstructionFunctor):
    r'''
        Class for a functor that creates a d-monomial extension.

        It receives the name of the new added variable and the images of the variable
        in a string/element format.
    '''
    def __init__(self, varname: str, images: tuple[str|Element]):
        super().__init__(_DRings,_DRings)
        self.rank = 10 # just below DPolyRingFunctor

        self.__varname = varname
        self.__images = images

    def _apply_functor(self, x):
        return DMonomial(x, self.__varname, self.__images)
    
    def _repr_(self) -> str:
        return f"DMonomial(*, {self.__varname}, {self.__images})"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, DMonomialFunctor):
            return False
        return self.__varname == other.__varname and self.__images == other.__images

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
        super().__init__(domain, codomain)

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
    
__all__ = ["DMonomial"]