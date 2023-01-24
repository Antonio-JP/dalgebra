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

    sage: dsQx = RingWithOperators(QQ[x], [lambda p : p.derivative(), lambda p : p(x=QQ[x].gens()[0] + 1)])
    sage: x = dsQx(x)
    sage: x.operation(0)
    1
    sage: x.operation(1)
    x + 1

AUTHORS:

    - Antonio Jimenez-Pastor [GitHub](https://github.com/Antonio-JP)
'''

# ****************************************************************************
#  Copyright (C) 2023 Antonio Jimenez-Pastor <ajpa@cs.aau.dk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import annotations

from typing import Callable, Collection
from sage.all import ZZ, latex, Parent
from sage.categories.all import Morphism, Category, Rings, CommutativeRings, CommutativeAdditiveGroups
from sage.categories.morphism import SetMorphism # pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.misc.all import abstract_method, cached_method
from sage.rings.ring import Ring, CommutativeRing
from sage.rings.derivation import RingDerivationModule
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
        def operators(self) -> Collection[Morphism]:
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

        @cached_method
        def derivations(self) -> Collection[DerivationMap]:
            r'''
                Method to filter the derivations out of a ring with operators.

                Derivations are a particular type of operators. With this method we 
                provide a similar interface as with the generic operators but just with
                derivation.

                Similarly, this class offers access to homomorphisms and skew derivations.

                When no derivation is declared for a ring, an empty tuple is returned.
            '''
            return tuple([operator for (operator, ttype) in zip(self.operators(), self.operator_types()) if ttype == "derivation"])

        def nderivations(self) -> int:
            r'''
                Method to get the number of derivations defined over a ring
            '''
            return len(self.derivations())

        def has_derivations(self) -> bool:
            r'''
                Method to know if there are derivations defined over the ring.
            '''
            return self.nderivations() > 0

        def is_differential(self) -> bool:
            r'''
                Method to check whether a ring is differential, i.e, all operators are derivations.
            '''
            return self.noperators() == self.nderivations()

        def derivation(self, element: Element, derivation: int = 0) -> Element:
            r'''
                Method to apply a derivation over an element.

                This method applies a derivation over a given element in the same way an operator
                is applied by the method :func:`~RingsWithOperators.ParentMethods.operation`.
            '''
            return self.derivations()[derivation](element)

        @cached_method
        def differences(self) -> Collection[Morphism]:
            r'''
                Method to filter the differences out of a ring with operators.

                Differences are a particular type of operators. With this method we 
                provide a similar interface as with the generic operators but just with
                difference.

                Similarly, this class offers access to derivations and skew derivations.

                When no difference is declared for a ring, an empty tuple is returned.
            '''
            return tuple([operator for (operator, ttype) in zip(self.operators(), self.operator_types()) if ttype == "homomorphism"])

        def ndifferences(self) -> int:
            r'''
                Method to get the number of differences defined over a ring
            '''
            return len(self.differences())

        def has_differences(self) -> bool:
            r'''
                Method to know if there are differences defined over the ring.
            '''
            return self.ndifferences() > 0

        def is_difference(self) -> bool:
            r'''
                Method to check whether a ring is difference, i.e, all operators are homomorphisms.
            '''
            return self.noperators() == self.ndifferences()

        def difference(self, element: Element, difference: int = 0) -> Element:
            r'''
                Method to apply a difference over an element.

                This method applies a difference over a given element in the same way an operator
                is applied by the method :func:`~RingsWithOperators.ParentMethods.operation`.
            '''
            return self.differences()[difference](element)
        
        def shift(self, element: Element, shift: int = 0) -> Element:
            r'''
                Alias for :func:`~RingsWithOperators.ParentMethods.difference`.
            '''
            return self.difference(element, shift)

        @abstract_method
        def operator_ring(self) -> Ring:
            r'''
                Method to get the operator ring of ``self``.

                When we consider a ring with operators, we can always consider a new (usually non-commutative)
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

                This method applies repeatedly an operation defined in the parent of ``self``.
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

        def derivative(self, times: int = 1, derivation: int = 0) -> Element:
            r'''
                Apply a derivation to ``self`` a given amount of times.

                This method applies repeatedly a derivation defined in the parent of ``self``.
                See :func:`~RingsWithOperators.ParentMethods.derivation` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().derivation(self, derivation)
            else:
                return self.derivation(times=times-1,derivation=derivation).operation(derivation=derivation)

        def difference(self, times: int = 1, difference: int = 0) -> Element:
            r'''
                Apply a difference to ``self`` a given amount of times.

                This method applies repeatedly a difference defined in the parent of ``self``.
                See :func:`~RingsWithOperators.ParentMethods.difference` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().difference(self, difference)
            else:
                return self.difference(times=times-1,difference=difference).operation(difference=difference)
                
        def shift(self, times: int = 1, shift: int = 0) -> Element:
            r'''
                Alias for :func:`~RingsWithOperators.ElementMethods.difference`.
            '''
            return self.difference(times, shift)

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

_RingsWithOperators = RingsWithOperators.__classcall__(RingsWithOperators)
####################################################################################################
###
### DEFINING THE FACTORY FOR THE CREATION OF WRAPPED RINGS
###
####################################################################################################
class RingWithOperatorFactory(UniqueFactory):
    r'''
        Factory to create wrappers around existing rings.

        The :class:`RingsWithOperatorFactory` allows to create wrapper around existing rings
        with a predefined set of operators. For doing so, we have two possibilities:

        INPUT:

        * ``base``: a commutative ring to which we will add operators.
        * ``operators``: a list with operators that will be added to ``base``. It may be one of the following:
          - An additive callable: a :class:`AdditiveMap` will be created for it.
          - An additive homomorphism: a :class:`Morphism` with appropriate domain and codomain.
          - A ring homomorphism: a :class:`Morphism` in the appropriate Hom set.
          - A (skew)-derivation: an element of a module of (skew)-derivations. The corresponding :class:`SkewMap`
            will be created for it.
        * ``types`` (optional): if given, it must be a list with the corresponding types of the operators.
          We will use this information to create different types of :class:`Morphism`.

        SPECIAL CASES:

        If this is used over another wrapped ring, this Factory will create an extended version where the 
        new operators are concatenated to the previous operators.

        OUTPUT:

        A :class:`RingWithOperators_Wrapper` with the new ring with operators.
    '''
    def create_key(self, base : CommutativeRing, *operators : Callable, **kwds):
        # checking the arguments
        if len(operators) < 1:
            raise ValueError("At least one operator must be given.")
        elif len(operators) == 1 and isinstance(operators[0], Collection):
            operators = operators[0]
        operators = list(operators)
        types = list(kwds.pop("types", len(operators)*["none"]))

        if isinstance(base, RingWithOperators_Wrapper):
            operators = list(base.construction().operators) + operators
            types = list(base.construction().types) + types
            base = base.wrapped
        
        # we convert the input into a common standard to create an appropriate key
        for (i, (operator, ttype)) in enumerate(zip(operators, types)):
            if ttype == "none":
                ## We decide the structure depending on the type of object
                if operator in base.Hom(base): # it is an homomorphism - we do nothing
                    types[i] = "homomorphism"
                elif isinstance(parent(operator), RingDerivationModule):
                    if operator.parent().twisting_morphism() is None: # derivation without twist
                        new_operator = DerivationMap(
                            base,
                            operator
                        )
                        types[i] = "derivation"
                    else:
                        new_operator = SkewMap(
                            base,
                            operator.parent().twisting_morphism(),
                            operator
                        )
                        types[i] = "skew"
                elif isinstance(operator, Callable):
                    new_operator = AdditiveMap(
                        base,
                        operator
                    )
                else:
                    raise TypeError(f"All operators must be callables. Found {operator}")
            elif ttype == "homomorphism":
                def hom_from_callable(base, func):
                    if base.ngens() > 0 and (not 1 in base.gens()):
                        base_map = hom_from_callable(base.base(), func)
                    else:
                        base_map = None
                    hom_set = base.Hom(base)
                    return hom_set([base(func(gen)) for gen in base.gens()], base_map = base_map)
                new_operator = hom_from_callable(base, operator)
            elif ttype == "derivation":
                der_module = base.derivation_module()
                new_operator = DerivationMap(
                    base, 
                    sum((operator(base_gen)*der_gen for (base_gen,der_gen) in zip(base.gens(),der_module.gens())), der_module.zero())
                )
            elif ttype == "skew":
                raise NotImplementedError("Building skew-derivation from callable not implemented")

            if new_operator != operator:
                operators[i] = new_operator
        return tuple([base, tuple(operators), tuple(types)])
            
    def create_object(self, _, key):
        base, operators, types = key

        return RingWithOperators_Wrapper(base, *operators, types=types)
RingWithOperators = RingWithOperatorFactory("dalgebra.ring_w_operator.ring_w_operator.RingWithOperator")

class DifferentialRingFactory(RingWithOperatorFactory):
    r'''
        Factory to create differential wrappers around existing rings.
    '''
    def create_key(self, base : CommutativeRing, *operators : Callable):
        # checking the arguments
        if len(operators) < 1:
            raise ValueError("At least one operator must be given.")
        elif len(operators) == 1 and isinstance(operators[0], Collection):
            operators = operators[0]

        return super().create_key(base, *operators, types=len(operators)*["derivation"])
DifferentialRing = DifferentialRingFactory("dalgebra.ring_w_operator.ring_w_operator.DifferentialRingFactory")

class DifferenceRingFactory(RingWithOperatorFactory):
    r'''
        Factory to create differential wrappers around existing rings.
    '''
    def create_key(self, base : CommutativeRing, *operators : Callable):
        # checking the arguments
        if len(operators) < 1:
            raise ValueError("At least one operator must be given.")
        elif len(operators) == 1 and isinstance(operators[0], Collection):
            operators = operators[0]

        return super().create_key(base, *operators, types=len(operators)*["homomorphism"])
DifferenceRing = DifferenceRingFactory("dalgebra.ring_w_operator.ring_w_operator.DifferenceRingFactory")
####################################################################################################
###
### DEFINING THE ELEMENT AND PARENT FOR WRAPPED RINGS
###
####################################################################################################
class RingWithOperators_WrapperElement(Element):
    def __init__(self, parent, element):
        if(not isinstance(parent, RingWithOperators_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        Element.__init__(self, parent=parent)
        self.wrapped = element

    # Arithmetic methods
    def _add_(self, x) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped + x.wrapped)
    def _sub_(self, x) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped - x.wrapped)
    def _neg_(self) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), -self.wrapped)
    def _mul_(self, x) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _rmul_(self, x) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _lmul_(self, x) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def __pow__(self, n) -> RingWithOperators_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped ** n)

    def __eq__(self, x) -> bool:
        if x is None: return False

        r = pushout(self.parent(), parent(x))
        if isinstance(r, RingWithOperators_Wrapper):
            return self.wrapped == r(x).wrapped
        return r(self) == r(x)

    def is_zero(self) -> bool:
        return self.wrapped == 0
    def is_one(self) -> bool:
        return self.wrapped == 1

    ## Other magic methods
    def __hash__(self) -> int:
        return hash(self.wrapped)
    def __str__(self) -> str:
        return str(self.wrapped)
    def __repr__(self) -> str:
        return repr(self.wrapped)
    def _latex_(self) -> str:
        return latex(self.wrapped)

class RingWithOperators_Wrapper(CommutativeRing):
    r'''
        Class for wrapping a Commutative ring and add operators over it.

        This class allows the user to translate a Commutative ring with some operations to 
        the category of :class:`RingsWithOperators` preserving as many operations and properties
        of the original ring as possible, but adding the new functionality in the category.

        We do not recommend to use this class by itself. It should be created using the 
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
        *operators : Morphism | Collection[Morphism],
        types : Collection[str] = None, 
        category = None
    ):
        #########################################################################################################
        ### CHECKING THE ARGUMENTS
        ### 'base'
        if not base in _CommutativeRings:
            raise TypeError("Only commutative rings can be wrapped as RingWithOperators")

        ### 'operators'
        if len(operators) == 1 and isinstance(operators[0], (list,tuple)):
            operators = operators[0]
        if any(not isinstance(operator, Morphism) for operator in operators):
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
                if ttype == "none":
                    if not operator.category_for().is_subcategory(_CommutativeAdditiveGroups):
                        raise ValueError(f"An operator invalid for type 'none' -> {operator}")
                elif ttype == "homomorphism":
                    if not operator.category_for().is_subcategory(_CommutativeRings):
                        raise ValueError(f"An operator invalid for type 'homomorphism' -> {operator}")
                elif ttype == "derivation":
                    if not isinstance(operator, DerivationMap):
                        raise ValueError(f"An operator invalid for type 'derivation' -> {operator}")
                elif ttype == "skew":
                    if not isinstance(operator, SkewMap):
                        raise ValueError(f"An operator invalid for type 'skew' -> {operator}")
                else:
                    raise ValueError(f"Invalid type provided -> {ttype}")

        self.__types = tuple(types)

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

        #########################################################################################################
        ### CREATING THE NEW OPERATORS FOR THE CORRECT STRUCTURE
        self.__operators : tuple[WrappedMap] = tuple([WrappedMap(self, operator) for operator in operators])

    @property
    def wrapped(self) -> CommutativeRing: return self.__wrapped

    def operators(self) -> tuple[WrappedMap]: return self.__operators

    def operator_types(self) -> tuple[str]: return self.__types

    ## Coercion methods
    def _has_coerce_map_from(self, S) -> bool:
        r'''
            Return ``True`` if it is possible to have a coercion map from `S` to ``self``.
        '''
        if isinstance(S, RingWithOperators_Wrapper):
            return self.wrapped._has_coerce_map_from(S.wrapped) # the operators do not matter for coercing elements
        else:
            return self.wrapped._has_coerce_map_from(S)

    def _element_constructor_(self, x) -> RingWithOperators_WrapperElement:
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

    def _is_valid_homomorphism_(self, codomain, im_gens, base_map=None) -> bool:
        return self.wrapped._is_valid_homomorphism_(codomain, im_gens, base_map)

    def construction(self) -> RingWithOperatorsFunctor:
        return RingWithOperatorsFunctor([operator.function for operator in self.operators()], self.operator_types()), self.wrapped

    # Rings methods
    def characteristic(self) -> int:
        return self.wrapped.characteristic()

    def gens(self) -> tuple[RingWithOperators_WrapperElement]:
        return tuple([self.element_class(self, gen) for gen in self.wrapped.gens()])

    def ngens(self) -> int:
        return self.wrapped.ngens()

    ## Representation methods
    def __repr__(self) -> str:
        begin = "Differential" if self.is_differential() else "Difference" if self.is_difference() else ""
        return f"{begin} Ring [[{self.wrapped}], {repr(self.operators())}]"

    def __str__(self) -> str:
        return repr(self)

    def _latex_(self) -> str:
        return r"\left(" + latex(self.wrapped) + ", " + latex(self.operators()) + r"\right)"

    ## Element generation
    def one(self) -> RingWithOperators_WrapperElement:
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], diff)
                sage: R.one()
                1
        '''
        return self.element_class(self, self.wrapped(1))
    
    def zero(self) -> RingWithOperators_WrapperElement:
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], lambda p : diff(p))
                sage: R.zero()
                0
        '''
        return self.element_class(self, self.wrapped(0))
    
    def random_element(self,*args,**kwds) -> RingWithOperators_WrapperElement:
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
    def __init__(self, operators: Collection[Morphism], types: Collection[str]):
        if len(operators) != len(types):
            raise ValueError("The length of the operators and types must coincide.")
        self.__operators = tuple(operators)
        self.__types = tuple(types)

        super().__init__(_CommutativeRings, _RingsWithOperators)
    
    ### Methods to implement
    def _coerce_into_domain(self, x: Element) -> Element:
        if not x in self.domain():
            raise TypeError(f"The object [{x}] is not an element of [{self.domain()}]")
            
    def _apply_functor(self, x):
        return RingWithOperators(x, self.__operators, self.__types)
        
    def _repr_(self):
        return f"RingWithOperators(*,{self.__operators}])"
        
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__operators == other.__operators and self.__types == other.__types

    def merge(self, other):
        if isinstance(other, RingWithOperatorsFunctor):
            return RingWithOperatorsFunctor(self.__operators + other.__operators, self.__types + other.__types)
        else:
            raise NotImplementedError(f"{self} can only be merged with other RingWithOperatorsFunctor")

    @property
    def operators(self) -> Collection[Morphism]:  return self.__operators
    @property
    def types(self): return self.__types

class RingWithOperators_Wrapper_SimpleMorphism(Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`RingWithOperator_Wrapper` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        return self.codomain()(p.wrapped)

####################################################################################################
###
### DEFINING THE REQUIRED MAPS FOR THIS MODULE
###
####################################################################################################
class AdditiveMap(SetMorphism):
    def __init__(self, domain : Parent, function : Callable):
        # We create the appropriate Hom set
        hom = domain.Hom(domain, category=_CommutativeAdditiveGroups)
        self.function = function
        super().__init__(hom, function)

    def __str__(self) -> str:
        return f"Additive Map [{repr(self)}]\n\t- From: {self.domain()}\n\t- To  : {self.codomain()}"

    def __repr__(self) -> str:
        return f"{self.function}"

    def __eq__(self, other) -> bool:
        return isinstance(other, AdditiveMap) and self.domain() == other.domain() and self.function == other.function

    def __hash__(self) -> int:
        return self.function.__hash__()

class SkewMap(AdditiveMap):
    def __init__(self, domain : Parent, twist : Morphism, function : Callable):
        # we check the input
        if not twist in domain.Hom(domain):
            raise TypeError("The twist for a skew derivation must be an homomorphism.")
        tw_der_module = domain.derivation_module(twist=twist)
        if not function in tw_der_module:
            raise TypeError("The function for a skew derivation must be in the corresponding module")
        self.twist = twist
        super().__init__(domain, function)

    def __str__(self) -> str:
        return f"Skew Derivation [{repr(self)}] over (({self.domain()}))"

class DerivationMap(SkewMap):
    def __init__(self, domain, function : Callable):
        super().__init__(domain, domain.Hom(domain).one(), function)

    def __str__(self) -> str:
        return f"Derivation [{repr(self)}] over (({self.domain()}))"

class WrappedMap(AdditiveMap):
    def __init__(self, domain : RingWithOperators_Wrapper, function : Morphism):
        if not isinstance(domain, RingWithOperators_Wrapper):
            raise TypeError("A WrappedMap can only be created for a 'RingWithOperators_Wrapper'")

        if function.domain() != domain.wrapped:
            raise ValueError(f"The map to be wrapped must have appropriate domain: ({domain.wrapped}) instead of ({function.domain()})")

        self.__wrapped = function

        super().__init__(domain, lambda p : domain(function(p.wrapped)))

    def __repr__(self) -> str:
        return repr(self.__wrapped)

    def __str__(self) -> str:
        return f"Wrapped [{repr(self)}] over (({self.domain()}))"

__all__ = ["RingsWithOperators", "RingWithOperators", "DifferentialRing", "DifferenceRing"]