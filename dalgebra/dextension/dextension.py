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

    where `\kappa_d(p(x))` is the polynomial `p(x)` where all the coefficients are differentiated, while
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

    When managing d-Extensions, the variables will be sorted in a directed graph, where we see the dependencies 
    as field extensions between different variables. Looking into this graph, we can define equivalent 
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
from sage.combinat.posets.posets import FinitePoset
from sage.graphs.digraph import DiGraph
from sage.misc.latex import latex_variable_name
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.polynomial.multi_polynomial_element import MPolynomial_polydict as PolyDict
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection

from ..dring import AdditiveMap, DRings, DFractionField

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

        return DExtension_PolyRing(base, polynomial, names=names, category=category)
    
class DExtensionFieldFactory(DExtensionFactory):
    def create_object(self, _, key) -> DExtension_Field:
        base, names, polynomial, category = key

        return DExtension_Field(base, polynomial, names=names, category=category)


DExtensionRing = DExtensionFactory("dalgebra.dextension.dextension.DExtensionRing")
DExtension = DExtensionFieldFactory("dalgebra.dextension.dextension.DExtension")

#########################################################################
### ELEMENT AND PARENT CLASSES FOR EXTENSIONS
#########################################################################
class DExtension_PolyDict(PolyDict):
    def __init__(self, parent: DExtension_Field, data: dict[tuple[int],Element]):
        super().__init__(parent, data)

        self.__algebraic = None # cached value for the algebraic equivalent

        self._exponents = sorted(self.element().dict(), reverse=True) if self.parent().ngens() == 1 else sorted(self.element().dict(), key=self.parent().term_order().sortkey, reverse=True)

    def kappa(self, operation:int = 0) -> DExtension_PolyDict:
        result = {m.degrees() : c.operation(operation) for (m,c) in zip(self.monomials(), self.coefficients())}
        return self.parent().element_class(self.parent(), {k:v for (k,v) in result.items() if v != 0})
    
    def partial(self, variable: DExtension_PolyDict) -> DExtension_PolyDict:
        ## Index of the variable to compute the partial
        variable = self.parent().gens().index(variable)

        result = dict()
        for (m,c) in zip(self.monomials(), self.coefficients()):
            m = m.degrees()
            for i,e in enumerate(m):
                if e > 0:
                    monomial = tuple(m[j] if j != i else e-1 for j in range(len(m)))
                    result[monomial] = result.get(monomial, self.parent().base().zero()) + c*e
        return self.parent().element_class(self.parent(), result)
    
    def algebraic(self) -> Element:
        if self.is_monomial():
            exponents = self.degrees()
            vars = self.parent().to_sage().gens()
            result = self.parent().to_sage().one()
            for (e,v) in zip(exponents, vars):
                if e > 0:
                    result *= v**e
            return result
        return sum(c.to_sage()*m.algebraic() for (m,c) in zip(self.monomials(), self.coefficients()))
    
    
    @lazy_attribute
    def _exponents(self):
        """
        Return the exponents of the monomials appearing in ``self`` for
        internal use only.

        EXAMPLES::

            sage: R.<a,b,c> = PolynomialRing(QQbar, 3)                                  # needs sage.rings.number_field
            sage: f = a^3 + b + 2*b^2                                                   # needs sage.rings.number_field
            sage: f._exponents                                                          # needs sage.rings.number_field
            [(3, 0, 0), (0, 2, 0), (0, 1, 0)]
        """
        if self.parent().ngens() == 1:
            return 

class DExtension_Element(Element):
    def __init__(self, parent: DExtension_Field, value: Element):
        super().__init__(parent)

        self.__algebraic = self.parent().to_sage()(value)

    #############################################################
    ### Arithmetic methods
    #############################################################
    def _add_(self, other: DExtension_Element) -> DExtension_Element:
        return self.parent()(self.algebraic() + other.algebraic())
    def _mul_(self, other: DExtension_Element) -> DExtension_Element:
        return self.parent()(self.algebraic() * other.algebraic())
    def __invert__(self) -> DExtension_Element:
        return self.parent()(~self.algebraic())


    def algebraic(self) -> Element:
        return self.__algebraic

    def numerator(self) -> DExtension_Element:
        return self.parent()(self.algebraic().numerator())
    
    def denominator(self) -> DExtension_Element:
        return self.parent()(self.algebraic().denominator())

    def is_polynomial(self) -> bool:
        return self.denominator() == 1

    def kappa(self, operator: int) -> DExtension_Element:
        if not self.is_polynomial():
            raise NotPolynomialError(self)
        
        return sum(c.derivative(operator)*m for (c,m) in zip(self.coefficients(), self.monomials()))

    def partial(self, variable: DExtension_Element) -> DExtension_Element:
        if not self.is_polynomial():
            raise NotPolynomialError(self)
        der = self.parent().partial(variable)
        return self.parent()(der(self.algebraic()))

    def coefficients(self) -> tuple[Element]:
        if not self.is_polynomial():
            raise NotPolynomialError(self)
        
        return tuple(self.parent().base()(c) for c in self.algebraic().numerator().coefficients())
    
    def monomials(self) -> tuple[DExtension_Element]:
        if not self.is_polynomial():
            raise NotPolynomialError(self)
        
        return tuple(self.parent()(m) for m in self.algebraic().numerator().monomials())

    def degree(self, variable: DExtension_Element | str = None) -> int:
        if not self.is_polynomial():
            raise NotPolynomialError(self)
        
        self.algebraic().numerator().degree(self.parent().algebraic_poly()(str(variable) if variable is not None else None))

    def variables(self) -> tuple[DExtension_Element]:
        var_n = tuple(self.parent()(v) for v in self.parent().algebraic_poly().gens() if self.algebraic().numerator().degree(v) > 0)
        var_d = tuple(self.parent()(v) for v in self.parent().algebraic_poly().gens() if self.algebraic().denominator().degree(v) > 0)

        return tuple(set(var_n+var_d))

    def __eq__(self, other: DExtension_Element) -> bool:
        try:
            other = self.parent()(other)
            return self.algebraic() == other.algebraic()
        except:
            return False
        
    @cached_method
    def __gen_method(self, method):
        def new_method(*args, **kwds):
            output = method(*args, **kwds)
            if output in self.parent().to_sage():
                return self.parent().element_class(self.parent(), output)                    
            return output
        return new_method
            
    def __getattr__(self, name: str):
        output = self.__algebraic.__getattribute__(name)
        return self.__gen_method(output)
        
    def __hash__(self) -> int:
        return hash(self.algebraic())

    def __repr__(self) -> str:
        return repr(self.algebraic())
    
    def __ne__(self, other) -> bool:
        return not self == other

class DExtension_PolyRing(Parent):
    Element = DExtension_PolyDict
    
    def _set_categories(self, base : Parent, category=None) -> list[Category]: 
        return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, 
                 base : Parent, polynomial: tuple[tuple[str | Element]], varname:str = None, 
                 names:tuple[str] = None, category=None):
        ## Checking that varname is not set
        if varname is not None:
            raise ValueError("The varname argument is not allowed for this class")
        
        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = None
        self._names = tuple(names)

        ## We create the inner sage structures
        self.__algebraic_base = base.to_sage() # field F without d-operations -- used to communicate with sage
        self.__algebraic_ring = PolynomialRing(self.__algebraic_base, names=names) # polynomial ring over F with the variables of ``self``
        
        ## We add our own coercions with the new structure
        self.register_coercions_conversions()
        
        ## We store the values for the operations of generators
        self.__operations_gens = tuple(tuple(self(self.__algebraic_ring(p)) for p in poly) for poly in polynomial) # self.__operations_gens[i][j] is the image of the j-th operation on the i-th generator
        self.__operators = [self.extend_operator(i, base.operator_types()[i], [self.__operations_gens[j][i] for j in range(len(names))]) for i in range(base.noperators())] 

        ## We build the graph of dependencies
        dgraphs = [{g : tuple(v for v in g.operation(i).variables() if v != g) for g in self.gens()} for i in range(self.noperators())]
        self.__dependency_graphs = [DiGraph(dgraph, format='dict_of_lists') for dgraph in dgraphs]

    #############################################################
    ### Getter methods for a DExtension_Field
    #############################################################
    def varnames(self) -> tuple[str]:
        r'''
            Returns the names of the variables of the extension.
        '''
        return self._names
    
    def ngens(self) -> int:
        return len(self._names)
    
    def gens(self) -> tuple[DExtension_PolyDict]:
        r'''
            Returns the generators of the extension.
        '''
        if self.__gens is None:
            self.__gens = tuple(
                self.element_class(self, {
                    tuple(0 if i != j else 1 for j in range(self.ngens())) : self.base().one()
                }) for i in range(self.ngens())
            )

        return self.__gens
    
    def gen(self, index:str) -> DExtension_PolyDict:
        r'''
            Returns the generator with the given name.
        '''
        if isinstance(index, str):
            return self.gen(self.varnames().index(index))
        return self.__gens[index]
    
    def algebraic(self) -> Parent:
        r'''
            Returns the algebraic field without the operations.
        '''
        return self.__algebraic_ring
    
    def algebraic_base(self) -> Parent:
        r'''
            Returns the base field without the operations.
        '''
        return self.__algebraic_base

    def one(self) -> DExtension_PolyDict:
        r'''
            Returns the multiplicative identity of the extension.
        '''
        return self.element_class(self, {tuple(0 for _ in range(self.ngens())): 1})
    
    def zero(self) -> DExtension_PolyDict:
        r'''
            Returns the multiplicative identity of the extension.
        '''
        return self.element_class(self, dict())

    #############################################################
    ### DExtension methods
    #############################################################
    def dependency_graph(self, operation: int = 0) -> DiGraph:
        return self.__dependency_graphs[operation]

    def is_tower_of_monomials(self, operation: int = 0) -> bool:
        return self.dependency_graph(operation).is_directed_acyclic()
    
    def tower_of_monomials(self, operation: int = 0) -> tuple[DExtension_PolyDict]:
        P = FinitePoset(self.dependency_graph(operation))
        
        from itertools import product
        inclusion_order = []
        while len(P) > 0:
            # we pick the maximal element with minimal amount of children
            intervals = [el for el in (P.interval(m,M) for (m,M) in product(P.minimal_elements(), P.maximal_elements())) if el != []]
            inclusion_order.append(min(P.maximal_elements(), key=lambda v : sum(len(el) for el in intervals if el[-1] == v)))
            P = P.subposet([v for v in P._elements if v != inclusion_order[-1]])
        return inclusion_order
    
    #############################################################
    ### Coercion methods
    #############################################################
    def register_coercions_conversions(self):
        r'''
            This method (called only once) registers the coercions and conversions between the the extension and all 
            related SageMath structures generated in the process.
        '''
        self.__algebraic_ring.register_coercion(MapDExtensionToRing(self)) # coercion from ``self`` to `F[gens]`
        self.register_coercion(MapRingToDExtension(self)) # coercion from `F[self]` to ``self``
    
    def _coerce_map_from_base_ring(self):
        return CoerceFromBase_DExtension_PolyRing(self)

    def construction(self) -> tuple[DExtension_PolyRingFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return DExtension_PolyRingFunctor([[str(el) for el in imgs] for imgs in self.__operations_gens], self.varnames()), self.base()

    def fraction_field(self):
        return DFractionField(self)

    def change_base(self, R) -> DExtension_Field:
        new_ring = DExtension(R, self.__operations_gens, names=self.varnames())
        ## Creating the coercion map if possible
        try:
            M = CoerceBetweenBases_DExtensionPolyRing(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    def extend_operator(self, operator: int, otype: str, images: Collection[Element]) -> AdditiveMap:
        r'''
            Given an operator and the images of the generators, this method returns the operator extended to the new field.

            There are two main cases: when the operator is a derivation (i.e., `otype = "derivation"`) and when the operator is a difference
            (i.e., `otype = "difference"`). In the first case, the operator is extended by the Leibniz rule, while in the second case, the operator
            is extended by the homomorphism property.
        '''
        if otype == "derivation":
            def __derivation(element: DExtension_PolyDict) -> DExtension_PolyDict:
                kappa = element.kappa(operator)
                partials = tuple(element.partial(g) for g in self.gens())
                return sum((partials[i] * images[i] for i in range(len(self.gens()))), kappa)

            return AdditiveMap(self, __derivation)

        elif otype == "homomorphism":
            ## We create the homomorphism in the algebraic field
            def __homomorphism(element: DExtension_PolyDict) -> DExtension_PolyDict:
                return element.kappa(operator)(
                    **{vname : self.__operations_gens[i][operator] for (i,vname) in enumerate(self.varnames())}
                ) ## It is the evaluation (as polynomial) of the kappa of the operator.
            return AdditiveMap(self, __homomorphism)
        else:
            raise NotImplementedError("The operator type must be either 'derivation' or 'homomorphism'")

    #############################################################
    ### Representation methods for Python
    #############################################################
    def __repr__(self):
        return f"D-Extension of {self.base()} with elements {self.gens()} whose images are \n\t" + ",\n\t".join([
            f"{self.gens()[i]} --> [" + ", ".join([str(el) for el in imgs]) + "]" for i,imgs in enumerate(self.__operations_gens)
        ])

    def _latex_(self):
        ## TODO write latex method
        pass

    ##################################################
    #### Method from DRing category
    ##################################################
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> DExtension_Field:
        return self.change_base(self.base().add_constants(*new_constants))

    def linear_operator_ring(self) -> DExtension_Field:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DExtension_Element, operation: int = 0) -> DExtension_Element:
        ## If the operation is a derivation, this would be the place to include symbolic integration methods
        raise NotImplementedError(f"The integration in these fields is not yet implemented")
    
    def _lcm_denominators(self, *elements: DExtension_Element) -> DExtension_Element:
        raise NotImplementedError(f"The integration in these fields is not yet implemented")

    def to_sage(self):
        return self.__algebraic_ring

class DExtension_Field(Parent):
    Element = DExtension_Element
    
    def _set_categories(self, base : Parent, category=None) -> list[Category]: 
        return [_DRings, Algebras(base), _DRings, _Fields] + ([category] if category is not None else [])

    def __init__(self, 
                 base : Parent, polynomial: tuple[tuple[str | Element]], varname:str = None, 
                 names:tuple[str] = None, category=None):
        ## Checking that varname is not set
        if varname is not None:
            raise ValueError("The varname argument is not allowed for this class")
        
        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## We create the inner sage structures
        self.__algebraic_base = base.to_sage() # field F without d-operations -- used to communicate with sage
        self.__algebraic_ring = PolynomialRing(self.__algebraic_base, names=names) # polynomial ring over F with the variables of ``self``
        self.__algebraic_self = self.__algebraic_ring.fraction_field() # fraction field of the polynomial ring -- equivalent to ``self`` but in SageMath

        ## We add our own coercions with the new structure
        self.register_coercions_conversions()
        
        ## We store the values for the operations of generators
        self.__operations_gens = tuple(tuple(self(self.__algebraic_ring(p)) for p in poly) for poly in polynomial) # self.__operations_gens[i][j] is the image of the j-th operation on the i-th generator
        self.__operators = [self.extend_operator(i, base.operator_types()[i], [self.__operations_gens[j][i] for j in range(len(names))]) for i in range(base.noperators())] 

        ## We build the graph of dependencies
        dgraphs = [{g : tuple(v for v in g.operation(i).variables() if v != g) for g in self.gens()} for i in range(self.noperators())]
        self.__dependency_graphs = [DiGraph(dgraph, format='dict_of_lists') for dgraph in dgraphs]

    #############################################################
    ### Getter methods for a DExtension_Field
    #############################################################
    def varnames(self) -> tuple[str]:
        r'''
            Returns the names of the variables of the extension.
        '''
        return tuple(str(g) for g in self.gens())
    
    def gens(self) -> tuple[DExtension_Element]:
        r'''
            Returns the generators of the extension.
        '''
        return tuple(self(v) for v in self.__algebraic_self.gens())
    
    def gen(self, name:str) -> DExtension_Element:
        r'''
            Returns the generator with the given name.
        '''
        return self.gens()[self.varnames().index(name)]
    
    def algebraic_self(self) -> Parent:
        r'''
            Returns the algebraic field without the operations.
        '''
        return self.__algebraic_self
    
    def algebraic_poly(self) -> Parent:
        r'''
            Returns the polynomial ring over the algebraic field.
        '''
        return self.__algebraic_ring
    
    def algebraic_base(self) -> Parent:
        r'''
            Returns the base field without the operations.
        '''
        return self.__algebraic_base

    def partial(self, variable: DExtension_Element):
        r'''
            Method that creates the partial derivative with respect to one variable at algebraic level
        '''
        derivation_module = self.algebraic_poly().derivation_module()
        i = self.varnames().index(str(variable))

        coefficients = [0 for _ in range(len(self.gens()))]
        coefficients[i] = 1

        return derivation_module(coefficients)

    def one(self) -> DExtension_Element:
        r'''
            Returns the multiplicative identity of the extension.
        '''
        return self.element_class(self, self.__algebraic_self.one())
    
    def zero(self) -> DExtension_Element:
        r'''
            Returns the multiplicative identity of the extension.
        '''
        return self.element_class(self, self.__algebraic_self.zero())

    #############################################################
    ### DExtension methods
    #############################################################
    def dependency_graph(self, operation: int = 0) -> DiGraph:
        return self.__dependency_graphs[operation]

    def is_tower_of_monomials(self, operation: int = 0) -> bool:
        return self.dependency_graph(operation).is_directed_acyclic()
    
    def tower_of_monomials(self, operation: int = 0) -> tuple[DExtension_Element]:
        P = FinitePoset(self.dependency_graph(operation))
        
        from itertools import product
        inclusion_order = []
        while len(P) > 0:
            # we pick the maximal element with minimal amount of children
            intervals = [el for el in (P.interval(m,M) for (m,M) in product(P.minimal_elements(), P.maximal_elements())) if el != []]
            inclusion_order.append(min(P.maximal_elements(), key=lambda v : sum(len(el) for el in intervals if el[-1] == v)))
            P = P.subposet([v for v in P._elements if v != inclusion_order[-1]])
        return inclusion_order
    
    #############################################################
    ### Coercion methods
    #############################################################
    def register_coercions_conversions(self):
        r'''
            This method (called only once) registers the coercions and conversions between the the extension and all 
            related SageMath structures generated in the process.
        '''
        self.__algebraic_self.register_coercion(MapDExtensionToField(self)) # coercion from ``self`` to `F(gens)`
        self.register_coercion(MapFieldToDExtension(self)) # coercion from `F(self)` to ``self``
        # conversion from ``self`` to `F[gens]`
        # conversion from ``self`` to `F`
        
        ## TODO: Check if this is enough. In theory, if we have a coercion between ``self`` and `F(gens)`, then a conversion from ``self``
        ## to `F[gens]` can be induced from the known conversion from `F(gens)` to `F[gens]`. The same for the conversion from ``self`` to `F`.

    def _coerce_map_from_base_ring(self):
        return CoerceFromBase_DExtension(self)

    def construction(self) -> tuple[DExtensionFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return DExtensionFunctor([[str(el) for el in imgs] for imgs in self.__operations_gens], self.varnames()), self.base()

    def fraction_field(self):
        return self ## self is already a field

    def change_base(self, R) -> DExtension_Field:
        new_ring = DExtension(R, self.__operations_gens, names=self.varnames())
        ## Creating the coercion map if possible
        try:
            M = CoerceBetweenBases_DExtension(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    def extend_operator(self, operator: int, otype: str, images: Collection[Element]) -> AdditiveMap:
        r'''
            Given an operator and the images of the generators, this method returns the operator extended to the new field.

            There are two main cases: when the operator is a derivation (i.e., `otype = "derivation"`) and when the operator is a difference
            (i.e., `otype = "difference"`). In the first case, the operator is extended by the Leibniz rule, while in the second case, the operator
            is extended by the homomorphism property.
        '''
        if otype == "derivation":
            def __derivation_poly(element: DExtension_Element) -> DExtension_Element:
                kappa = element.kappa(operator)
                partials = tuple(element.partial(g) for g in self.gens())
                return sum((partials[i] * images[i] for i in range(len(self.gens()))), kappa)
            def __derivation(element: DExtension_Element) -> DExtension_Element:
                n, d = element.numerator(), element.denominator()
                dn, dd = __derivation_poly(n), __derivation_poly(d)

                return (dn*d - n*dd)/(d**2)
            return AdditiveMap(self, __derivation)

        elif otype == "homomorphism":
            ## We create the homomorphism in the algebraic field
            self_to_aself = self.__algebraic_self.coerce_map_from(self)
            aself_to_self = self.coerce_map_from(self.__algebraic_self)
            base_morphism = aself_to_self*self.operators()[operator]*self_to_aself
            homomorphism = self.__algebraic_self.hom([el.algebraic() for el in images], base_map=base_morphism)
            return AdditiveMap(self, lambda x : self(homomorphism(x.algebraic())))
        else:
            raise NotImplementedError("The operator type must be either 'derivation' or 'homomorphism'")

    #############################################################
    ### Representation methods for Python
    #############################################################
    def __repr__(self):
        return f"D-Extension of {self.base()} with elements {self.gens()} whose images are \n\t[" + ",\n\t".join([
            f"{self.gens()[i]} --> [" + ", ".join([str(el) for el in imgs]) + "]" for i,imgs in enumerate(self.__operations_gens)
        ])

    def _latex_(self):
        ## TODO write latex method
        pass

    ##################################################
    #### Method from DRing category
    ##################################################
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> DExtension_Field:
        return self.change_base(self.base().add_constants(*new_constants))

    def linear_operator_ring(self) -> DExtension_Field:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DExtension_Element, operation: int = 0) -> DExtension_Element:
        ## If the operation is a derivation, this would be the place to include symbolic integration methods
        raise NotImplementedError(f"The integration in these fields is not yet implemented")
    
    def _lcm_denominators(self, *elements: DExtension_Element) -> DExtension_Element:
        raise NotImplementedError(f"The integration in these fields is not yet implemented")

    def to_sage(self):
        return self.__algebraic_self

#########################################################################
### CONSTRUCTIONS FUNCTOR FOR EXTENSIONS
#########################################################################
class DExtensionFunctor(ConstructionFunctor):
    def __init__(self, polynomial: tuple[tuple[str]], names: tuple[str]):
        if len(polynomial) != len(names):
            raise ValueError(f"The images and the variables must be of the same length")

        self.__polynomials = polynomial
        self.__names = names

    def _apply_functor(self, x):
        return DExtension(x, self.__polynomials, names=self.__names)

    def _repr_(self):
        return f"Construction functor for DExtensions with names {self.__names} and {len(self.__polynomials[0])} operations"

    def __eq__(self, other: DExtensionFunctor):
        if not isinstance(other, DExtensionFunctor):
            return False
        return self.__polynomials == other.__polynomials and self.__names == other.__names

class DExtension_PolyRingFunctor(ConstructionFunctor):
    def __init__(self, polynomial: tuple[tuple[str]], names: tuple[str]):
        if len(polynomial) != len(names):
            raise ValueError(f"The images and the variables must be of the same length")

        self.__polynomials = polynomial
        self.__names = names

    def _apply_functor(self, x):
        return DExtensionRing(x, self.__polynomials, names=self.__names)

    def _repr_(self):
        return f"Construction functor for DExtensions with names {self.__names} and {len(self.__polynomials[0])} operations"

    def __eq__(self, other: DExtension_PolyRingFunctor):
        if not isinstance(other, DExtension_PolyRingFunctor):
            return False
        return self.__polynomials == other.__polynomials and self.__names == other.__names

#########################################################################
### COERCIONS AND CONVERSION MORPHISMS FOR EXTENSIONS
#########################################################################
class MapDExtensionToField(Morphism):
    def __init__(self, domain: DExtension_Field):
        super().__init__(domain, domain.to_sage())

    def _call_(self, element: DExtension_Element) -> Element:
        return element.algebraic()

class MapFieldToDExtension(Morphism):
    def __init__(self, codomain: DExtension_Field):
        super().__init__(codomain.to_sage(), codomain)

    def _call_(self, element: Element) -> DExtension_Element:
        return self.codomain().element_class(self.codomain(), element)
    
class MapDExtensionToRing(Morphism):
    def __init__(self, domain: DExtension_PolyRing):
        super().__init__(domain, domain.to_sage())

    def _call_(self, element: DExtension_PolyDict) -> Element:
        return element.algebraic()

class MapRingToDExtension(Morphism):
    def __init__(self, codomain: DExtension_PolyRing):
        super().__init__(codomain.to_sage(), codomain)

    def _call_(self, element: Element) -> DExtension_PolyDict:
        if self.codomain().ngens() == 1: # polynomial case
            if element == 0:
                return self.codomain().zero()
            else:
                return self.codomain().element_class(
                    self.codomain(), {
                        (i,) : c for i,c in enumerate(element.coefficients(sparse=False)) if c != 0
                        })
        else: # multivariate polynomial case - we can use degrees
            return self.codomain().element_class(
                self.codomain(), {
                    m.degrees() : c for (c,m) in zip(element.coefficients(), element.monomials())
                    })

class CoerceFromBase_DExtension(Morphism):
    def __init__(self, codomain: DExtension_Field):
        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> DExtension_Element:
        return self.codomain().element_class(self.codomain(), self.codomain().to_sage()(element.to_sage()))

class ConversionToBase_DExtension(Morphism):
    def __init__(self, domain: DExtension_Field):
        super().__init__(domain, domain.base())

    def _call_(self, element: DExtension_PolyDict) -> Element:
        return element.constant_coefficient()
    
class CoerceFromBase_DExtension_PolyRing(Morphism):
    def __init__(self, codomain: DExtension_PolyRing):
        super().__init__(codomain.base(), codomain)

    def _call_(self, element: Element) -> DExtension_Element:
        return self.codomain().element_class(
            self.codomain(), 
            {tuple(0 for _ in range(self.codomain().ngens())) : element}
        )
    
class ConversionToBase_DExtension_PolyRing(Morphism):
    def __init__(self, domain: DExtension_PolyRing):
        super().__init__(domain, domain.base())

    def _call_(self, element: DExtension_Element) -> Element:
        n,d = element.numerator().algebraic(), element.denominator().algebraic()

        if n.degree() == 0 and d.degree() == 0: # both are in the base
            return self.codomain()(n/d)
        
        raise TypeError(f"{element} is not an element in {self.codomain()}")

class CoerceBetweenBases_DExtension(Morphism):
    def __init__(self, domain: DExtension_Field, codomain: DExtension_Field, coerce_map: Morphism):
        super().__init__(domain,codomain)
        if not (coerce_map.domain() is domain.base() and coerce_map.codomain() is codomain.base()):
            raise TypeError(f"Given coercion between bases is not valid")
        self.__coerce_map = coerce_map

    def _call_(self, element: DExtension_Element) -> DExtension_Element:
        if element.is_polynomial():    
            result = self.codomain().zero()
            
            for (c,m) in zip(element.coefficients(), element.monomials()):
                new_mon = self.codomain().one()
                for v in m.variables():
                    new_mon *= self.codomain().gen(str(v))**m.degree(v)
                result += self.__coerce_map(c)*new_mon
            
            return result
        else:
            return self(element.numerator())/self(element.denominator())

class CoerceBetweenBases_DExtensionPolyRing(Morphism):
    def __init__(self, domain: DExtension_PolyRing, codomain: DExtension_PolyRing, coerce_map: Morphism):
        super().__init__(domain,codomain)
        if not (coerce_map.domain() is domain.base() and coerce_map.codomain() is codomain.base()):
            raise TypeError(f"Given coercion between bases is not valid")
        self.__coerce_map = coerce_map

    def _call_(self, element: DExtension_Element) -> DExtension_Element:
        result = self.codomain().zero()
        
        for (c,m) in zip(element.coefficients(), element.monomials()):
            new_mon = self.codomain().one()
            for v in m.variables():
                new_mon *= self.codomain().gen(str(v))**m.degree(v)
            result += self.__coerce_map(c)*new_mon
        
        return result

#########################################################################
### EXCEPTIONS FOR THIS MODULE
#########################################################################
class NotPolynomialError(TypeError):
    def __init__(self, element: DExtension_Element):
        super().__init__(f"Element {element} is not a polynomial.")

__all__ = ["DExtension", "DExtensionRing"]
