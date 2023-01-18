r'''
Module with all structures for defining rings with operators.

Let `\sigma: R \rightarrow R` be an additive homomorphism, i.e., for all elements `r,s \in R`,
the map satisfies `\sigma(r+s) = \sigma(r) + \sigma(s)`. We define the *ring `R` with operator
`\sigma`* as the pair `(R, \sigma)`. 

Similarly, if we have a set of additive maps `\sigma_1,\ldots,\sigma_n : R \rightarrow R` that 
commute among themselves (i.e., for all `i,j`, `\sigma_i \circ \sigma_j = \sigma_j \circ \sigma_i`).
Then we define the *ring `R` with operators `(\sigma_1,\ldots,\sigma_n)`* as the tuple 
`(R, (\sigma_1,\ldots,\sigma_n))`.

This module provides the framework to define this type of rings with as many operators as 
the user wants and we also provide a Wrapper class so we can extend existing ring structures that 
already exist in SageMath. 

The factory :func:`RingWithOperator` allows the creation of these rings with operators and will determine 
automatically in which specified category a ring will belong. For example, we can create the differential
ring `(\mathbb{Q}[x], \partial_x)` or the difference ring `(\mathbb{Q}[x], x \mapsto x + 1)` with this module::

    sage: from dalgebra.ring_w_operator.ring_w_operator import RingWithOperators
    sage: dQx = RingWithOperators(QQ[x], lambda p : p.derivative())
    sage: sQx = RingWithOperators(QQ[x], lambda p : p(x=QQ[x].gens()[0] + 1))

Once the rings are created, we can create elements within the ring and apply the corresponding operator::

    sage: x = dQx(x)
    sage: x.operation()
    1
    sage: x = sQx(x)
    sage: x.operation()
    x + 1

We can also create the same ring with both operators together::

    sage: dsQx = RingWithOperator(QQ[x], [lambda p : p.derivative(), lambda p : p(x=QQ[x].gens()[0] + 1)])
    sage: x = dsQx(x)
    sage: x.operation(0)
    1
    sage: x.operation(1)
    x + 1

AUTHORS:

    - Antonio Jimenez-Pastor [GitHub](https://github.com/Antonio-JP)
'''
from __future__ import annotations

from typing import Collection
from sage.all import ZZ, latex
from sage.categories.all import Morphism, Category, Rings, CommutativeRings, CommutativeAdditiveGroups
from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.misc.abstract_method import abstract_method
from sage.rings.ring import Ring, CommutativeRing
from sage.structure.element import parent, Element #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module
from sage.symbolic.ring import SR #pylint: disable=no-name-in-module

_Rings = Rings.__classcall__(Rings)
_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)
_CommutativeAdditiveGroups = CommutativeAdditiveGroups.__classcall__(CommutativeAdditiveGroups)

####################################################################################################
###
### DEFINING THE CATEGORY FOR RINGS WITH OPERATORS
###
####################################################################################################
class RingsWithOperators(Category):
    r'''
        Category for representing rings with operators.

        Let `\sigma: R \rightarrow R` be an additive homomorphism, i.e., for all elements `r,s \in R`,
        the map satisfies `\sigma(r+s) = \sigma(r) + \sigma(s)`. We define the *ring `R` with operator
        `\sigma`* as the pair `(R, \sigma)`. 

        Similarly, if we have a set of additive maps `\sigma_1,\ldots,\sigma_n : R \rightarrow R` that 
        commute among themselves (i.e., for all `i,j`, `\sigma_i \circ \sigma_j = \sigma_j \circ \sigma_i`).
        Then we define the *ring `R` with operators `(\sigma_1,\ldots,\sigma_n)`* as the tuple 
        `(R, (\sigma_1,\ldots,\sigma_n))`.

        This category defines the basic methods for these rings.
    '''
    ## Defining a super-category
    def super_categories(self):
        return [_Rings]

    ## Defining methods for the Parent structures of this category
    class ParentMethods:
        @abstract_method
        def operators(self) -> tuple[Map]:
            r'''
                Method to get the collection of operators that are defined over the ring.

                These operators are maps from ``self`` to ``self`` that compute the application
                of each operator over the elements of ``self``.
            '''
            raise NotImplementedError("Method 'operators' need to be implemented")

        def noperators(self) -> int:
            r'''
                Method to get the number of operators defined over a ring
            '''
            return len(self.operators())

        def operation(self, element : Element, operator : int = 0) -> Element:
            r'''
                Method to apply an operator over an element.

                This method takes an element of ``self`` and applies one of the operators defined over ``self``
                over such element. This operator is given by its index, hence raising a :class:`IndexError` if
                the index is not in the valid range.

                INPUT:

                * ``element``: an element over the operator of this ring will be applied.
                * ``operator`` (`0` by default) the index of the operator that will be applied.

                OUTPUT:

                If the index is incorrect, an :class:`IndexError` is raised. Otherwise this method 
                returns `f(x)` where `x` is the ``element`` and `f` is the operator defined by ``operator``.

                EXAMPLES::

                    sage: from dalgebra.ring_w_operator.ring_w_operator import RingWithOperators
                    sage: dQx = RingWithOperators(QQ[x], lambda p : p.derivative())
                    sage: sQx = RingWithOperators(QQ[x], lambda p : p(x=QQ[x].gens()[0] + 1))
                    sage: sdQx = RingWithOperators(QQ[x], lambda p : p(x=QQ[x].gens()[0] + 1), lambda p : p.derivative())
                    sage: p = QQ[x](x^3 - 3*x^2 + 3*x - 1)
                    sage: dQx.operation(p)
                    3*x^2 - 6*x + 3
                    sage: sQx.operation(p)
                    x^3
                    sage: sdQx.operation(p)
                    x^3
                    sage: sdQx.operation(p, 1)
                    3*x^2 - 6*x + 3
                    sage: sdQx.operation(p, 2)
                    Traceback (most recent call last):
                    ...
                    IndexError: ... index out of range
            '''
            return self.operators()[operator](element)

        @abstract_method
        def operator_types(self) -> tuple[str]:
            r'''
                Method to get the types of the operators.

                The only condition for `\sigma: R \rightarrow R` to be a valid operator is that it is 
                an additive homomorphism. However, the behavior of `\sigma` with respect to the multiplication
                of `R` categorize `\sigma` into several possibilities:

                * "none": no condition is known over this method. This will disallow some extension operations.
                * "homomorphism": the map `\sigma` is an homomorphism, i.e., for all `r, s \in R` it satisfies
                  `\sigma(rs) = \sigma(r)\sigma(s)`.
                * "derivative": the map `\sigma` satisfies Leibniz rule, i.e., for all `r, s \in R` it satisfies
                  `\sigma(rs) = \sigma(r)s + r\sigma(s)`.
                * "skew": the map `\sigma` satisfies the skew-Leibniz rule, i.e., there is an homomorphism `\delta` 
                  such for all `r, s \in R` it satisfies `\sigma(rs) = \sigma(r)s + \delta(r)\sigma(s)`.

                This method returns a tuple (sorted as the output of :func:`operators`) with the types of each of the 
                operators.
            '''
            raise NotImplementedError("Method 'operator_types' need to be implemented")

        @abstract_method
        def operator_ring(self) -> Ring:
            r'''
                Method to get the operator ring of ``self``.

                When we consider a ring with operators, we can always consider a new (usually non-commuttative)
                ring where we extend ``self`` polynomially with all the operators and its elements represent
                new operators created from the operators defined over ``self``.

                This method return this new structure.
            '''
            raise NotImplementedError("Method 'operator_ring' need to be implemented")

    ## Defining methods for the Element structures of this category
    class ElementMethods:
        def operation(self, times : int = 1, operation : int = 0) -> Element:
            r'''
                Apply an operation to ``self`` a given amount of times.

                This method applies repeteadly an operation defined in the parent of ``self``.
                See :func:`~RingsWithOperators.ParentMethods.operation` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().operation(self, operation)
            else:
                return self.operation(times=times-1,operation=operation).operation(operation=operation)

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

####################################################################################################
###
### DEFINING THE FACTORY FOR THE CREATION OF WRAPPED RINGS
###
####################################################################################################
class RingWithOperatorFactory(UniqueFactory):
    r'''
        Factory to create wrappers around exising rings.

        The :class:`RingsWithOperatorFactory` allows to create wrapper around existing rings
        with a predefined set of operators. For doing so, we have two possibilities:

        1. The base ring is given as a named argument and the operators are in the ``*args`` part of the input.
        2. The base ring is the FIRST part of the unnamed arguments of the input and the rest are the operators.

        **Important**: there must be always at least one operator. Otherwise a :class:`TypeError` is returned.
    '''
#     def create_key(self, *args, **kwds):
#         r'''
#             Method to create a key from the input of the factory.
#         '''
#         print(f"{args=} -- {kwds=}")
#         if "base" in kwds:
#             base = kwds["base"]
#             operators = args
#         else:
#             base = args[0]
#             operators = args[1:]
        
#         if not isinstance(operators,(list,tuple)):
#             operators = [operators]

#         if len(operators) == 0:
#             raise TypeError("No operators were given")

#         return (base, operators)

#     def create_object(self, _, key):
#         r'''
#             Method to create an object from a given key
#         '''
#         base, operators = key

#         if base in RingsWithOperators:
#             if base.noperators() != len(operators):
#                 raise ValueError("The number of operators does not match!")
#             return base

#         new_operators = []
#         for operator in operators:
#             if isinstance(operator, Map):
#                 try:
#                     domain_po = pushout(operator.domain(), base)
#                     codomain_po = pushout(operator.codomain(), base) 
#                     if not domain_po == base:
#                         raise TypeError(f"The domain [{operator.domain()}] must be something to be coerced into {base}")
#                     if not codomain_po == base:
#                         raise TypeError(f"The codomain [{operator.codomain()}] must be something to be coerced into {base}")

#                     if domain_po != operator.domain() or codomain_po != operator.codomain():
#                         new_operator = CallableMap(lambda p : operator(p), base, base)
#                     else:
#                         new_operator = operator
#                 except:
#                     raise ValueError(f"{operator.domain()} or {operator.codomain()} could not be pushed into common parent with {base}")
#             elif callable(operator):
#                 new_operator = CallableMap(operator, base, base)
#             new_operators.append(new_operator)
        
#         return RingWithOperators_Wrapper(base, new_operators)
    pass # TODO: Implement the factory

RingWithOperators = RingWithOperatorFactory("dalgebra.ring_w_operator.ring_w_operator.RingWithOperator")

####################################################################################################
###
### DEFINING THE ELEMENT AND PARENT FOR WRAPPED RINGS
###
####################################################################################################
class RingWithOperators_WrapperElement(Element):
#     def __init__(self, parent, element):
#         if(not isinstance(parent, RingWithOperators_Wrapper)):
#             raise TypeError("An element created from a non-wrapper parent")
#         elif(not element in parent.wrapped):
#             raise TypeError("An element outside the parent [%s] is requested" %parent)

#         Element.__init__(self, parent=parent)
#         self.__wrapped = element

#     @property
#     def wrapped(self): return self.__wrapped

#     # Arithmetic methods
#     def _add_(self, x):
#         return self.parent().element_class(self.parent(), self.wrapped + x.wrapped)
#     def _sub_(self, x):
#         return self.parent().element_class(self.parent(), self.wrapped - x.wrapped)
#     def _neg_(self):
#         return self.parent().element_class(self.parent(), -self.wrapped)
#     def _mul_(self, x):
#         return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
#     def _rmul_(self, x):
#         return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
#     def _lmul_(self, x):
#         return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
#     def __pow__(self, n):
#         return self.parent().element_class(self.parent(), self.wrapped ** n)

#     def __eq__(self, x) -> bool:
#         if x is None: 
#             return False
#         r = pushout(self.parent(), parent(x))
#         s, x = r(self), r(x)
#         if isinstance(s.parent(), RingWithOperators_Wrapper):
#             return s.wrapped == x.wrapped
#         else:
#             return s == x

#     def is_zero(self) -> bool:
#         return self.wrapped == 0
#     def is_one(self) -> bool:
#         return self.wrapped == 1

#     ## Other magic methods
#     def __hash__(self) -> int:
#         return hash(self.wrapped)
#     def __str__(self) -> str:
#         return str(self.wrapped)
#     def __repr__(self) -> str:
#         return repr(self.wrapped)
#     def _latex_(self) -> str:
#         return latex(self.wrapped)
    pass # TODO: Implement the element class

class RingWithOperators_Wrapper(CommutativeRing):
    r'''
        Class for wrapping a Commutative ring and add operators over it.

        This class allows the user to translate a Commutative ring with some operations to 
        the category of :class:`RingsWithOperators` preserving as many operations and properties
        of the original ring as possible, but adding the new functionality in the category.

        We do not recomend to use this class by itself. It should be created using the 
        corresponding factory (see :class:`RingWithOperatorFactory` and its defined instance in 
        ``dalgebra.ring_w_operator.ring_w_operator.RingWithOperators``).

        INPUT:

        * ``base``: the :class:`CommutativeRing` that will be wrapped.
        * ``operators``: a valid :class:`sage.categories.map.Map` to define an operator over ``self``.
        * ``types`` (optional): a list with the types (see :func:`RingsWithOperators.ParentMethods.operator_types` 
          for further information). If nothing is given, the list will be automatically computed.
        * ``category`` (optional): argument from the category framework to allow further flexibility.
    '''
    Element = RingWithOperators_WrapperElement

    def __init__(self, 
        base : CommutativeRing, 
        operators : Map | Collection[Map], 
        types : Collection[str] = None, 
        category = None
    ):
        #########################################################################################################
        ### CHECKING THE ARGUMENTS
        ### 'base'
        if not base in _CommutativeRings:
            raise TypeError("Only commutative rings can be wrapped as RingWithOperators")

        ### 'operators'
        if not isinstance(operators, (list,tuple)):
            operators = [operators]
        if any(not isinstance(operator, Map) for operator in operators):
            raise TypeError("All the given operators must be Maps")
        if any(operator.domain() != operator.codomain() or operator.domain() != base for operator in operators):
            raise TypeError("The operators must bu maps from and to the commutative ring given by 'base'")

        ### 'types'
        if types is None: # we compute the types using the maps
            types = []
            for operator in operators:
                if isinstance(operator, DerivationMap): types.append("derivation")
                elif isinstance(operator, SkewMap): types.append("skew")
                elif operator.category_for().is_subcategory(_CommutativeRings): types.append("homomorphism")
                else: types.append("none")
        else: # we check the operators behave as requested
            if not isinstance(types, (list, tuple)) or len(types) != len(operators):
                raise TypeError("The types must be a list of the same length of the operators")
            for operator, ttype in zip(operators, types):
                if ttype == "none" and not operator.category_for().is_subcategory(_CommutativeAdditiveGroups):
                    raise ValueError(f"An operator invalid for type 'none' -> {operator}")
                elif ttype == "homomorphism" and not operator.category_for().is_subcategory(_CommutativeRings):
                    raise ValueError(f"An operator invalid for type 'homomorphism' -> {operator}")
                elif ttype == "derivation" and not isinstance(operator, DerivationMap):
                    raise ValueError(f"An operator invalid for type 'derivation' -> {operator}")
                elif ttype == "skew" and not isinstance(operator, SkewMap):
                    raise ValueError(f"An operator invalid for type 'skew' -> {operator}")
                else:
                    raise ValueError(f"Invalid type provided -> {ttype}")

        self.__types = tuple(types)

        #########################################################################################################
        ### CREATING THE NEW OPERATORS FOR THE CORRECT STRUCTURE
        self.__operators = tuple([WrappedMap(operator, self, self) for operator in operators])

        #########################################################################################################
        # CREATING CATEGORIES
        categories = [RingsWithOperators(), base.category()]
        if(isinstance(category, (list, tuple))):
            categories += list(category)
        elif(category != None): 
            categories.append(category) 

        #########################################################################################################
        ### CALLING THE SUPER AND ARRANGING SOME CONVERSIONS
        super().__init__(base.base(), category=tuple(categories))
        self.__wrapped = base

        # registering conversion to simpler structures
        current = self.base()
        morph = RingWithOperators_Wrapper_SimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = RingWithOperators_Wrapper_SimpleMorphism(self, current)
            current.register_conversion(morph)

    @property
    def wrapped(self) -> CommutativeRing: return self.__wrapped

    def operators(self) -> tuple[Map]: return self.__operators

    def operator_types(self): return self.__types

    ## Coercion methods
    def _has_coerce_map_from(self, S):
        r'''
            Return ``True`` if it is possible to have a coercion map from `S` to ``self``.
        '''
        if isinstance(S, RingWithOperators_Wrapper):
            return self.wrapped._has_coerce_map_from(S.wrapped) # the operators do not matter for coercing elements
        else:
            return self.wrapped._has_coerce_map_from(S)

    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.
        '''
        if x in SR: 
            # conversion from symbolic ring --> using its string representation
            x = str(x)
        elif isinstance(parent(x), RingWithOperators_Wrapper): 
            # conversion from other wrapped rings with operators --> we convert the element within
            x = x.wrapped
        p = self.wrapped._element_constructor_(x)
        return self.element_class(self, p)

    def _is_valid_homomorphism_(self, codomain, im_gens, base_map=None):
        return self.wrapped._is_valid_homomorphism_(codomain, im_gens, base_map)

    # def __contains__(self, element):
    #     if(parent(element) in self.category()):
    #         return parent(element) == self
    #     try:
    #         self(element)
    #         return True
    #     except:
    #         return element in self.wrapped        

    def construction(self):
        return RingWithOperatorsFunctor([operator.wrapped for operator in self.operators()]), self.wrapped

    # Rings methods
    def characteristic(self):
        return self.wrapped.characteristic()

    def gens(self):
        return tuple([self.element_class(self, gen) for gen in self.wrapped.gens()])

    def ngens(self):
        return self.wrapped.ngens()

    ## Representation methods
    def __repr__(self) -> str:
        return f"Ring [{self.wrapped}] with operator [{repr(self.operators())}]"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        return r"\left(" + latex(self.wrapped) + ", " + latex(self.operators()) + r"\right)"

    ## Element generation
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], diff)
                sage: R.one()
                1
        '''
        return self.element_class(self, self.wrapped(1))
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], lambda p : diff(p))
                sage: R.zero()
                0
        '''
        return self.element_class(self, self.wrapped(0))
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a random element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        p = self.wrapped.random_element(*args,**kwds)
        return self(p)

####################################################################################################
###
### DEFINING THE CONSTRUCTION FUNCTOR AND SIMPLE MORPHISM
###
####################################################################################################
class RingWithOperatorsFunctor(ConstructionFunctor):
    # def __init__(self, operators):
    #     self.__operators = operators
    #     super().__init__(RingsWithOperators(),RingsWithOperators())
        
    # ### Methods to implement
    # def _coerce_into_domain(self, x):
    #     if(x not in self.domain()):
    #         raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
    #     return x
        
    # def _apply_functor(self, x):
    #     return RingWithOperators(x,self.__operators)
        
    # def _repr_(self):
    #     return "RingWithOperators(*,[%s])" %(repr(self.__operators))
        
    # def __eq__(self, other):
    #     if(other.__class__ == self.__class__):
    #         return (other.__operators == self.__operators)

    # def merge(self, other):
    #     pass

    # def operators(self):
    #     return self.__operators
    pass # TODO: Implement this functor

class RingWithOperators_Wrapper_SimpleMorphism(Morphism):
#     r'''
#         Class representing maps to simpler rings.

#         This map allows the coercion system to detect that some elements in a 
#         :class:`RingWithOperator_Wrapper` are included in simpler rings.
#     '''
#     def __init__(self, domain, codomain):
#         super().__init__(domain, codomain)
        
#     def _call_(self, p):
#         return self.codomain()(p.wrapped)
    pass # TODO Implement this morphism

####################################################################################################
###
### DEFINING THE REQUIRED MAPS FOR THIS MODULE
###
####################################################################################################
class SkewMap(Map):
    pass # TODO: Implement this type of map

class DerivationMap(SkewMap):
    pass # TODO: Implement this type of map

class WrappedMap(Map):
#     def __init__(self, function, domain, codomain):
#         super().__init__(domain, codomain)
#         if not callable(function):
#             raise TypeError("The argument function must be callable")
#         self.__method = function
#         try:
#             self.__name__ = function.__name__
#         except AttributeError:
#             self.__name__ = str(function)

#     def _call_(self, element):
#         return self.codomain()(self.__method(element))

#     def __str__(self):
#         return self.__repr__() + f"\n\tFrom {self.domain()}\n\tTo {self.codomain()}"

#     def __repr__(self):
#         return f"Map from callable {self.__name__}"

#     def _latex_(self):
#         out = r"\begin{array}{rcl}"
#         out += r"\\".join([latex(el) + r"\mapsto" + latex(self(el)) for el in self.domain().gens()])
#         out += r"\end{array}"
#         return out
    pass # TODO: Implement this class

__all__ = ["RingsWithOperators", "RingWithOperators"]