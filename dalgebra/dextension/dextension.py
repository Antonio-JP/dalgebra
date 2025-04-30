from __future__ import annotations
r'''
    Module to create D-extensions for D-fields.

    Let `(K, (d_1,\ldots,d_n))` be a d-Field with multiple difference-differential operators.
    It is very common to add an element `x` and impose some conditions on the derivative in
    order to extend the field.

    In this case we will consider the most trivial case where the new element is always a
    transcendental element. Moreover, the operations of the new element is a rational function
    on the new field.

    These types of extensions are very common in the literature. They include many special functions
    such us the exponential function, the logarithm, the trigonometric functions, etc. For example,
    for the exponential function we add a new element `e` that satisfies the condition `d(e) = e`, for
    the logarithm, we start from the field `\mathbb{Q}(x)` and add a new element `L` that satisfies
    `d(L) = 1/x`.

    ## The case of derivations

    A derivation is an operation that satisfies the Leibniz rule. In particular, if we have one of
    these d-Extensions, let `d_x` be the derivative of the new added variable `x`. Then we can write
    the derivative of any polynomial `p(x)` as:

    .. MATH::

        d(p(x)) = \kappa_d(p(x)) + \partial_x(p(x)) d_x,

    where `\kappa_d(p(x))` is the polynomial `p(x)` where all the coefficients are derivated, while
    `\partial_x(p(x))` is the derivative of `p(x)` with respect to `x`.

    Hence, knowing the value of `d_x` is enough to compute the derivative of any polynomial.

    ## The case of differences

    A difference operator is an operation that is an homomorphism, i.e., `\sigma(pq)=\sigma(p)\sigma(q)`.
    In particular, if we have one of these d-Extensions, let `s_x` be the difference of the new added
    variable `x`. Then we can write the difference of any polynomial `p(x)` as:

    .. MATH::

        \sigma(p(x)) = \kappa_s(p(x))(s_x),

    where, again, `\kappa_s(p(x))` is the polynomial `p(x)` where all the coefficients are shifted. Hence,
    knowing the value of `s_x` is enough to compute the shifted of any polynomial.

    ## The case of several variables

    D-Extensions can be built incrementally, meaning we add one variable at a time. This is the most common
    setting, but it is not the only one. For example, when adding the sine and cosine functions, we need
    two variables at the same time, `s` and `c`, that satisfy the conditions `d(s) = c` and `d(c) = -s`.
    We can not achieve this by adding one variable at a time. This is why we will provide a general
    implementation that allow this additional case.

    ## Monomial extension and tower of monomials.

    Following the content of Bronstein's book, Symbolic Integration I: Transcendental Functions, we can
    define a monomial `t` over a differential field `(K,\partial)` as a transcendental element that satisfies
    that `\partial(t) = p(t)` for some polynomial `p \in K[t]`.

    When managing d-Extensions, the variables will be sorted in a poset, where we see the dependencies
    as field extensions between different variables. Looking into this poset, we can define equivalent
    d-Extensions that are built in a different order. Moreover, if this construction never uses two variables
    at once, we say we are managing a tower of monomials.

    ## Basic examples

    There are several basic examples of d-Extensions that we are going to use for testing:

    * The exponential function: we start from the basic field of constants `\mathbb{Q}` and add a new element
      `e` that satisfies `d(e) = e`. It only involves a derivation.
    * The natural polynomial shift: we start from the basic field of constants `\mathbb{Q}` and add a new element
      `n` that satisfies `s(n) = n+1`. It only involves a difference.
    * The factorial sequence: building over the natural polynomial shift, we add a new element `f` that satisfies
      `s(f) = f*(n+1)`. It involves only a difference, but it can be seen as a tower of monomials.
    * The sine and cosine functions: we start from the basic field of constants `\mathbb{Q}` and add two new elements
      `s` and `c` that satisfy `d(s) = c` and `d(c) = -s`. It involves a derivation and it can not be seen as a tower
      of monomials.
    * A diff-diff case: we can also create the field of rational functions with both the derivative and the
      shift operator. This is a more complex case that involves both a derivation and a difference.
    * Non-trivial tower of monomials: let us consider the mix case using the exponential function, the logarithm
      and the variable `x`. It has 3 different ways to be built, because the exponential can be added at any
      possible step. We must check that all the constructions are equivalent.

    EXAMPLES:

        sage: from dalgebra import *
        sage: ## Exponential function
        sage: Q_e.<e> = DExtension(DifferentialField(QQ), "e")
        sage: e.derivative()
        e
        sage: (e^2 - 1)/(e.derivative() + 1)
        e - 1
        sage: Q_e.is_differential()
        True
        sage: Q_e.is_tower_of_monomials()
        True
        sage: Q_e.monomial_poset()
        {e: []}
        sage: ## Natural polynomial shift
        sage: Q_n.<n> = DExtension(DifferenceField(QQ), "n + 1")
        sage: n.shift()
        n + 1
        sage: (n^2 - 1)/(n.shift())
        n - 1
        sage: Q_n.is_difference()
        True
        sage: Q_n.is_tower_of_monomials()
        True
        sage: Q_n.monomial_poset()
        {n: []}
        sage: ## Factorial sequence
        sage: Q_f.<f> = DExtension(Q_n, "f*(n+1)")
        sage: f.shift()
        f*(n + 1)
        sage: (f.shift() - (n+1))/(n+1)
        f-1
        sage: Q_f.is_difference()
        True
        sage: Q_f.is_tower_of_monomials()
        True
        sage: Q_f.monomial_poset()
        {n: [], f: [n]}
        sage: ## Sine and cosine functions
        sage: Q_sc.<s,c> = DExtension(DifferentialField(QQ), ["c", "-s"])
        sage: s.derivative()
        c
        sage: c.derivative()
        -s
        sage: (s^2 + c^2 - 1) ## This can not be checked with this extension
        s^2 + c^2 - 1
        sage: Q_sc.is_differential()
        True
        sage: Q_sc.is_tower_of_monomials()
        False
        sage: Q_sc.monomial_poset()
        {(s,c): []}
        sage: ## Diff-diff case
        sage: Q_dd.<x> = DExtension(DifferentialField(DifferenceField(QQ)), ["x+1", "1"]))
        sage: x.derivative()
        1
        sage: x.shift()
        x + 1
        sage: (1/3*(x^3).derivative() - 1)/(x.shift())
        x - 1
        sage: Q_dd.is_differential()
        False
        sage: Q_dd.is_difference()
        False
        sage: Q_dd.is_tower_of_monomials()
        True
        sage: Q_dd.monomial_poset()
        {x: []}
        sage: ## Non-trivial tower of monomials
        sage: Q_t.<x,l,e> = DExtension(DifferentialField(QQ), ["1", "1/x", "e"])
        sage: l.derivative()
        1/x
        sage: e.derivative()
        e
        sage: (l^2 + e^2 - 1)/(l.derivative() * x)
        l^2 + e^2 - 1
        sage: Q_t.is_differential()
        True
        sage: Q_t.is_tower_of_monomials()
        True
        sage: Q_t.monomial_poset()
        {x: [], l: [x], e: []}
        sage: Q_t2.<e> = DExtension(DExtension(QQ_x, "1/x", names=("l",)), "e")
        sage: Q_t == Q_t2
        True
        sage: Q_t3.<l> = DExtension(DExtension(QQ_x, "e", names=("e",)), "1/x")
        sage: Q_t == Q_t3
        True
        sage: Q_t4.<x,l> = DExtension(QQ_e, ["1", "1/x"])
        sage: Q_t == Q_t4
        True

    LIMITATIONS:

    * This structure do not allow to have algebraic relations between variables. Other classes
      such as :class:`~dalgebra.dextension.delliptic.DElliptic` will be used for this purpose.
'''

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.misc.latex import latex_variable_name
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection

from ..dring import AdditiveMap, DRings


_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)


#########################################################################
### UNIQUE FACTORY TO CREATE EXTENSIONS
#########################################################################
class DExtensionFactory(UniqueFactory):
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
        polynomial = tuple(tuple(str(p) for p in poly) for poly in polynomial) # we make sure everything is a tuple
        if len(polynomial) != len(names):
            raise ValueError("The number of variables and the number of polynomials must match")
        elif any(len(p) != base.noperators() for p in polynomial):
            raise ValueError("The number of operators must match the number of polynomials")

        ## We fix the arguments if the base was already a DExtension (iterative construction)
        if isinstance(base, DExtension_Field):
            names = (str(g) for g in base.gens()) + names
            polynomial = base.gens_imgs() + polynomial
            base = base.base()

        return (base, names, polynomial, category)

    def create_object(self, _, key) -> DExtension_Field:
        base, names, polynomial, category = key

        return DExtension_Field(base, polynomial, names=names, category=category)


DExtension = DExtensionFactory("dalgebra.dextension.dextension.DExtension")


#########################################################################
### ELEMENT AND PARENT CLASSES FOR EXTENSIONS
#########################################################################
class DExtension_Element(Element):
    def __init__(self, parent: DExtension_Field, value: Element):
        pass


class DExtension_Field(Parent):
    Element = DExtension_Element

    def _set_categories(self, base : Parent, category=None) -> list[Category]:
        return [_DRings, Algebras(base), _Fields] + ([category] if category is not None else [])

    def __init__(self,
                 base : Parent, polynomial: tuple[tuple[str | Element]], varname:str = None,
                 names:tuple[str] = None, category=None):
        ## Checking that varname is not set
        if varname is not None:
            raise ValueError("The varname argument is not allowed for this class")

        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## We create the inner sage structures
        self.__algebraic_base = base.to_sage()
        ## TODO: Go on here
        pass


#########################################################################
### CONSTRUCTIONS FUNCTOR FOR EXTENSIONS
#########################################################################
class DExtensionFunctor(ConstructionFunctor):
    def __init__(self, polynomial: str | Element, varname: str):
        pass

    def _apply_functor(self, x):
        pass

    def _repr_(self):
        pass

    def __eq__(self, other):
        pass


#########################################################################
### COERCIONS AND CONVERSION MORPHISMS FOR EXTENSIONS
#########################################################################
class MapDExtensionToField(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element: DExtension_Element):
        pass


class MapFieldToDExtension(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element):
        pass


class MapDExtensionToPoly(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element: DExtension_Element):
        pass


class MapPolyToDExtension(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element):
        pass


class MapDExtensionToAlgebraic(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element: DExtension_Element):
        pass


class MapAlgebraicToDExtension(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element):
        pass


class CoerceFromBase_DExtension(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element):
        pass


class ConversionToBase_DExtension(Morphism):
    def __init__(self, domain, codomain):
        pass

    def _call_(self, element: DExtension_Element):
        pass


class CoerceBetweenBases_DExtension(Morphism):
    def __init__(self, domain, codomain, coerce_map):
        pass

    def _call_(self, element: DExtension_Element) -> DExtension_Element:
        pass


__all__ = ["DExtension"]
