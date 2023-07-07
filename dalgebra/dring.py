r'''
    Module with all structures for defining rings with operators.

    Let `\sigma: R \rightarrow R` be an additive homomorphism, i.e., for all elements `r,s \in R`,
    the map satisfies `\sigma(r+s) = \sigma(r) + \sigma(s)`. We define the pair `(R, \sigma)` as a *d-ring*. 

    Similarly, if we have a set of additive maps `\sigma_1,\ldots,\sigma_n : R \rightarrow R`,
    we define the *ring* `R` *with operators* `(\sigma_1,\ldots,\sigma_n)` (or simply, *d-ring*) as the tuple 
    `(R, \{\sigma_1,\ldots,\sigma_n\})`.

    This module provides the framework to define d-rings with as many operators as 
    the user wants and we also provide a Wrapper class so we can extend existing ring structures that 
    already exist in `SageMath <https://www.sagemath.org>`_. 

    The factory :func:`DRing` allows the creation of these rings with operators and will determine 
    automatically in which specified category a ring will belong. For example, we can create the differential
    ring `(\mathbb{Q}[x], \partial_x)` or the difference ring `(\mathbb{Q}[x], x \mapsto x + 1)` with the 
    following code::

        sage: from dalgebra import *
        sage: dQx = DRing(QQ[x], lambda p : p.derivative())
        sage: sQx = DRing(QQ[x], lambda p : QQ[x](p)(x=QQ[x].gens()[0] + 1))

    Once the rings are created, we can create elements within the ring and apply the corresponding operator::

        sage: x = dQx(x)
        sage: x.operation()
        1
        sage: x = sQx(x)
        sage: x.operation()
        x + 1

    We can also create the same ring with both operators together::

        sage: dsQx = DRing(QQ[x], lambda p : p.derivative(), lambda p : QQ[x](p)(x=QQ[x].gens()[0] + 1))
        sage: x = dsQx(x)
        sage: x.operation(operation=0)
        1
        sage: x.operation(operation=1)
        x + 1

    However, these operators have no structure by themselves: `SageMath`_ is not able to distinguish the type 
    of the operators if they are defined using lambda expressions or callables. This can be seen by the fact that
    the factory can not detect the equality on two identical rings::

        sage: dQx is DRing(QQ[x], lambda p : p.derivative())
        False

    To avoid this behavior, we can set the types by providing an optional list called ``types`` whose elements are 
    strings with values:

    * ``homomorphism``: the operator is interpret as a homomorphism/shift/difference operator.
    * ``derivation``: the operator is considered as a derivation.
    * ``skew``: the operator is considered as a skew-derivation.
    * ``none``: the operator will only be considered as an additive Map without further structure.

    We can see that, when setting this value, the ring is detected to be equal::

        sage: dQx = DRing(QQ[x], lambda p : p.derivative(), types=["derivation"])
        sage: dQx is DRing(QQ[x], lambda p : p.derivative(), types=["derivation"])
        True
        sage: # Since we have one variable, the built-in `diff` also work
        sage: dQx is DRing(QQ[x], diff, types=["derivation"])
        True
        sage: # We can also use elements in the derivation module
        sage: dQx is DRing(QQ[x], QQ[x].derivation_module().gens()[0], types=["derivation"])
        True

    Also, we can detect this equality when adding operators sequentially instead of at once::

        sage: dsQx = DRing(QQ[x], 
        ....:     lambda p : p.derivative(), 
        ....:     lambda p : QQ[x](p)(x=QQ[x].gens()[0] + 1), 
        ....:     types = ["derivation", "homomorphism"]
        ....: )
        sage: dsQx is DRing(dQx, lambda p : QQ[x](p)(x=QQ[x].gens()[0] + 1), types=["homomorphism"])
        True

    For specific types of operators as *derivations* or *homomorphism*, there are other functions where the ``types`` argument can be skipped
    taking the corresponding value by default::

        sage: dQx is DifferentialRing(QQ[x], lambda p : p.derivative())
        True
        sage: dsQx is DifferenceRing(DifferentialRing(QQ[x], lambda p : p.derivative()), lambda p : QQ[x](p)(x=QQ[x].gens()[0] + 1))
        True

    We can also have more complexes structures with different types of operators::

        sage: R.<x,y> = QQ[] # x is the usual variable, y is an exponential
        sage: dx, dy = R.derivation_module().gens(); d = dx + y*dy
        sage: DR = DifferentialRing(R, d)
        sage: # We add a special homomorphism where the two generators are squared but QQ is fixed
        sage: DSR = DifferenceRing(DR, R.Hom(R)([x^2, y^2]))
        sage: DSR.noperators()
        2
        sage: DSR.operator_types()
        ('derivation', 'homomorphism')

    We can see that these operator **do not commute**::

        sage: x = DSR(x); y = DSR(y)
        sage: x.difference().derivative()
        2*x
        sage: x.derivative().difference()
        1
        sage: y.difference().derivative()
        2*y^2
        sage: y.derivative().difference()
        y^2

    Finally, this module also allows the definition of skew-derivations for any ring. This requires the use 
    of derivation modules with twist (see :sageref:`sage.rings.derivations <rings/sage/rings/derivation>`)::

        sage: R.<x,y> = QQ[]
        sage: s = R.Hom(R)([x-y, x+y])
        sage: td = R.derivation_module(twist=s)(x-y)
        sage: tR = DRing(R, s, td, types=["homomorphism", "skew"])
        sage: x,y = tR.gens()
        sage: (x*y).skew() == x.skew()*y + x.shift()*y.skew()
        True
        sage: (x*y).skew() == x.skew()*y.shift() + x*y.skew()
        True

    AUTHORS:

    - Antonio Jimenez-Pastor (:git:`GitHub <Antonio-JP>`)
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

import logging

from collections.abc import Sequence
from sage.all import ZZ, latex, Parent
from sage.categories.all import Morphism, Category, Rings, CommutativeRings, CommutativeAdditiveGroups, QuotientFields
from sage.categories.morphism import IdentityMorphism, SetMorphism # pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.misc.all import abstract_method, cached_method
from sage.rings.fraction_field import FractionField_generic
from sage.rings.fraction_field_element import FractionFieldElement # pylint: disable=no-name-in-module
from sage.rings.morphism import RingHomomorphism_im_gens # pylint: disable=no-name-in-module
from sage.rings.ring import Ring, CommutativeRing #pylint: disable=no-name-in-module
from sage.rings.derivation import RingDerivationModule
from sage.structure.element import parent, Element #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module
from sage.symbolic.ring import SR #pylint: disable=no-name-in-module
from typing import Callable

logger = logging.getLogger(__name__)

_Rings = Rings.__classcall__(Rings)
_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)
_CommutativeAdditiveGroups = CommutativeAdditiveGroups.__classcall__(CommutativeAdditiveGroups)
_QuotientFields = QuotientFields.__classcall__(QuotientFields)

####################################################################################################
###
### DEFINING THE CATEGORY FOR RINGS WITH OPERATORS
###
####################################################################################################
class DRings(Category):
    r'''
        Category for representing d-rings.

        Let `\sigma: R \rightarrow R` be an additive homomorphism, i.e., for all elements `r,s \in R`,
        the map satisfies `\sigma(r+s) = \sigma(r) + \sigma(s)`. We define the *ring* `R` *with operator*
        `\sigma` as the pair `(R, \sigma)`. 

        Similarly, if we have a set of additive maps `\sigma_1,\ldots,\sigma_n : R \rightarrow R`.
        Then we define the *ring* `R` *with operators* `(\sigma_1,\ldots,\sigma_n)` as the tuple 
        `(R, (\sigma_1,\ldots,\sigma_n))`.

        This category defines the basic methods for these rings and their elements
    '''
    ## Defining a super-category
    def super_categories(self):
        return [_Rings]

    ## Defining methods for the Parent structures of this category
    class ParentMethods: #pylint: disable=no-member
        ##########################################################
        ### METHODS RELATED WITH THE OPERATORS
        ##########################################################
        ### 'generic'
        @abstract_method
        def operators(self) -> Sequence[Morphism]:
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

        def operation(self, element : Element, operator : int = None) -> Element:
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

                    sage: from dalgebra import *
                    sage: dQx = DRing(QQ[x], lambda p : p.derivative())
                    sage: sQx = DRing(QQ[x], lambda p : p(x=QQ[x].gens()[0] + 1))
                    sage: sdQx = DRing(QQ[x], lambda p : p(x=QQ[x].gens()[0] + 1), lambda p : p.derivative())
                    sage: p = QQ[x](x^3 - 3*x^2 + 3*x - 1)
                    sage: dQx.operation(p)
                    3*x^2 - 6*x + 3
                    sage: sQx.operation(p)
                    x^3
                    sage: sdQx.operation(p)
                    Traceback (most recent call last):
                    ...
                    IndexError: An index for the operation must be provided when having several operations
                    sage: sdQx.operation(p, 0)
                    x^3
                    sage: sdQx.operation(p, 1)
                    3*x^2 - 6*x + 3
                    sage: sdQx.operation(p, 2)
                    Traceback (most recent call last):
                    ...
                    IndexError: ... index out of range
            '''
            if operator is None and self.noperators() == 1: operator = 0
            elif operator is None: raise IndexError("An index for the operation must be provided when having several operations")
            return self.operators()[operator](element)

        def apply_operations(self, element: Element, operations: list[int] | tuple[int], *, _ordered = False):
            r'''
                Method that apply several operations to an element in a specific way.

                INPUT:

                * ``element``: an element in ``self`` to whom the operations will be applied
                * ``operations``: list or tuple indicating the operations to be applied. If ``_ordered`` is given to 
                  ``True``, then the elements are interpreted as a list of operations that will be applied in 
                  the specific order that appears in ``operations``. Otherwise, the input must be a list/tuple of 
                  exactly ``self.noperators()`` indicating how many times each operation is applied.

                OUTPUT:

                The result of applying the operators to ``element``.
            '''
            result = element
            if _ordered:
                for operation in operations:
                    result = self.operation(result, operation)
            else:
                if len(operations) != self.noperators():
                    raise TypeError(f"The operations must be as many as operations (expected {self.noperators()}, got {len(operations)})")
                for operation, i in enumerate(operations):
                    result = result.operation(operation, times=i)
            return result

        def inverse_operation(self, element: Element, operator: int = None) -> Element:
            raise NotImplementedError("[inverse_operation] Inverses not implemented in general.")

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

        ### 'derivation'
        @cached_method
        def derivations(self) -> Sequence[DerivationMap]:
            r'''
                Method to filter the derivations out of a d-ring.

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

        def derivative(self, element: Element, derivation: int = None) -> Element:
            r'''
                Method to apply a derivation over an element.

                This method applies a derivation over a given element in the same way an operator
                is applied by the method :func:`~DRings.ParentMethods.operation`.
            '''
            if self.nderivations() == 0: raise TypeError("Derivations not defined for this ring.")
            elif derivation is None and self.nderivations() == 1: derivation = 0
            elif derivation is None: raise IndexError("An index for the derivation must be provided when having several derivations")
            return self.derivations()[derivation](element)

        ### 'difference'
        @cached_method
        def differences(self) -> Sequence[Morphism]:
            r'''
                Method to filter the differences out of a d-ring.

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

        def difference(self, element: Element, difference: int = None) -> Element:
            r'''
                Method to apply a difference over an element.

                This method applies a difference over a given element in the same way an operator
                is applied by the method :func:`~DRings.ParentMethods.operation`.
            '''
            if self.ndifferences() == 0: raise TypeError("Differences not defined for this ring.")
            elif difference is None and self.ndifferences() == 1: difference = 0
            elif difference is None: raise IndexError("An index for the difference must be provided when having several differences")
            return self.differences()[difference](element)
        
        def shift(self, element: Element, shift: int = None) -> Element:
            r'''
                Alias for :func:`~DRings.ParentMethods.difference`.
            '''
            return self.difference(element, shift)

        ### 'skews'
        @cached_method
        def skews(self) -> Sequence[Morphism]:
            r'''
                Method to filter the skew-derivations out of a d-ring.

                Differences are a particular type of operators. With this method we 
                provide a similar interface as with the generic operators but just with
                difference.

                Similarly, this class offers access to homomorphisms and derivations.

                When no skew-derivation is declared for a ring, an empty tuple is returned.
            '''
            return tuple([operator for (operator, ttype) in zip(self.operators(), self.operator_types()) if ttype == "skew"])

        def nskews(self) -> int:
            r'''
                Method to get the number of skew-derivations defined over a ring
            '''
            return len(self.skews())

        def has_skews(self) -> bool:
            r'''
                Method to know if there are skew-derivations defined over the ring.
            '''
            return self.ndifferences() > 0

        def is_skew(self) -> bool:
            r'''
                Method to check whether a ring is skewed, i.e, all operators are skew-derivations.
            '''
            return self.noperators() == self.nskews()

        def skew(self, element: Element, skew: int = None) -> Element:
            r'''
                Method to apply a skew-derivation over an element.

                This method applies a skew-derivation over a given element in the same way an operator
                is applied by the method :func:`~DRings.ParentMethods.operation`.
            '''
            if self.nskews() == 0: raise TypeError("Skew-derivations not defined for this ring.")
            elif skew is None and self.nskews() == 1: skew = 0
            elif skew is None: raise IndexError("An index for the skew must be provided when having several skews")
            return self.skews()[skew](element)
        
        ##########################################################
        ### OTHER METHODS
        ##########################################################
        @abstract_method
        def linear_operator_ring(self) -> Ring:
            r'''
                Method to get the operator ring of ``self``.

                When we consider a d-ring, we can always consider a new (usually non-commutative)
                ring where we extend ``self`` polynomially with all the operators and its elements represent
                new operators created from the operators defined over ``self``.

                This ring is the ring of linear operators over the ground ring.

                This method return this new structure.
            '''
            raise NotImplementedError("Method 'operator_ring' need to be implemented")

        def operators_commute(self, op1: int, op2: int, points: int = 10, *args, **kwds) -> bool:
            r'''
                Method to check whether two operators of the ring commute. 

                This method is not deterministic (meaning that it may return ``True`` even
                when the two operators do not fully commute) but it tries to check in a fix number
                of random elements if the two operators actually commute.

                It also try to see if the operators commute in the generators of the ring.

                INPUT:

                * ``op1``: index of the first operator to check.
                * ``op2``: index of the second operator to check.
                * ``points``: number of random points to be selected.
                * ``args``: arguments to be passed to the ``random_element`` method.
                * ``kwds``: arguments to be passed to the ``random_element`` method. 

                OUTPUT:

                ``True`` if all the tests indicates the operators commute, ``False`` otherwise.
            '''
            op1 = self.operators()[op1]; op2 = self.operators()[op2]
            
            to_check = list(self.gens()); current = self.base()
            while current.ngens() > 0 and (not 1 in to_check):
                to_check.extend([self.element_class(self, el) for el in current.gens()])
                current = current.base()
            to_check.extend(self.random_element(*args, **kwds) for _ in range(points))

            return all(op1(op2(element)) == op2(op1(element)) for element in to_check)

        def all_operators_commute(self, points: int = 10, *args, **kwds):
            r'''
                Method to check whether all operators of the ring commute. 

                This method is not deterministic (meaning that it may return ``True`` even
                when the two operators do not fully commute) but it tries to check in a fix number
                of random elements if the two operators actually commute.

                It also try to see if the operators commute in the generators of the ring.

                See :func:`operators_commute` for further information

                INPUT:

                * ``points``: number of random points to be selected.
                * ``args``: arguments to be passed to the ``random_element`` method.
                * ``kwds``: arguments to be passed to the ``random_element`` method. 

                OUTPUT:

                ``True`` if all the tests indicates the operators commute, ``False`` otherwise.

                EXAMPLES::

                    sage: from dalgebra import *
                    sage: R.<x> = QQ[]; d = diff; s = R.Hom(R)(x+1)
                    sage: dsR = DifferenceRing(DifferentialRing(R, d), s)
                    sage: dsR.all_operators_commute()
                    True
                    sage: R.<x,y> = QQ[]
                    sage: dx,dy = R.derivation_module().gens(); d = dx + y*dy
                    sage: s = R.Hom(R)([x + 1, y^2])
                    sage: dsR = DifferenceRing(DifferentialRing(R, d), s)
                    sage: dsR.all_operators_commute()
                    False
            '''
            return all(
                self.operators_commute(i, j, points, *args, **kwds) 
                for i in range(self.noperators())
                for j in range(i+1, self.noperators()) 
            )

        @abstract_method
        def constant_ring(self, operation: int = 0) -> Parent:
            r'''
                Method to obtain the constant ring of a given operation.

                The meaning of a ring of constants depends on the type of operator that 
                we are considering:

                * "homomorphism": the elements that are fixed by the operator.
                * "derivation": the elements that goes to zero with the operator.
                * "skew": the elements that goes to zero with the operator.
                * "none": it makes no sense to talk about constant for these operators.
            '''
            raise NotImplementedError("Method 'constant_ring' not implemented")
            
    ## Defining methods for the Element structures of this category
    class ElementMethods: #pylint: disable=no-member
        ##########################################################
        ### APPLICATION METHODS
        ##########################################################
        def operation(self, operation : int = None, times : int = 1) -> Element:
            r'''
                Apply an operation to ``self`` a given amount of times.

                This method applies repeatedly an operation defined in the parent of ``self``.
                See :func:`~DRings.ParentMethods.operation` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().operation(self, operation)
            else:
                return self.parent().operation(self.operation(operation=operation, times=times-1), operation)

        def inverse_operation(self, operation: int = None, times : int = 1) -> Element:
            r'''
                Apply the inverse operation to ``self`` a given amount of times.

                This method applies repeatedly the inverse operation defined in the parent of ``self``.
                See :func:`~DRings.ParentMethods.inverse_operation` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().inverse_operation(self, operation)
            else:
                return self.parent().inverse_operation(self.inverse_operation(operation=operation, times=times-1), operation)

        def derivative(self, derivation: int = None, times: int = 1) -> Element:
            r'''
                Apply a derivation to ``self`` a given amount of times.

                This method applies repeatedly a derivation defined in the parent of ``self``.
                See :func:`~DRings.ParentMethods.derivative` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().derivative(self, derivation)
            else:
                return self.parent().derivative(self.derivative(derivation=derivation, times=times-1), derivation)

        def difference(self, difference: int = None, times: int = 1) -> Element:
            r'''
                Apply a difference to ``self`` a given amount of times.

                This method applies repeatedly a difference defined in the parent of ``self``.
                See :func:`~DRings.ParentMethods.difference` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().difference(self, difference)
            else:
                return self.parent().difference(self.difference(difference=difference, times=times-1), difference)
                
        def shift(self, shift: int = None, times: int = 1) -> Element:
            r'''
                Alias for :func:`~DRings.ElementMethods.difference`.
            '''
            return self.difference(shift, times)

        def skew(self, skew: int = None, times: int = 1) -> Element:
            r'''
                Apply a skew-derivation to ``self`` a given amount of times.

                This method applies repeatedly a difference defined in the parent of ``self``.
                See :func:`~DRings.ParentMethods.skew` for further information.
            '''
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self.parent().skew(self, skew)
            else:
                return self.parent().skew(self.skew(skew=skew, times=times-1), skew)

        ##########################################################
        ### BOOLEAN METHODS
        ##########################################################
        def d_constant(self, operation: int = 0):
            r'''
                Method to check whether an element is a constant with respect to one operator.

                INPUT:

                * ``operation``: index defining the operation we want to check.

                OUTPUT:

                A boolean value with ``True`` is the element is a constant (see 
                :func:`~DRings.ParentMethods.constant_ring` for further information
                on what is a constant depending on the type of operator).

                REMARK: this method do not require the implementation on :func:`~DRings.ParentMethods.constant_ring`
                on its parent structure.

                EXAMPLES::

                    sage: from dalgebra import *
                    sage: R = DifferentialRing(QQ[x], diff)
                    sage: p = R(3)
                    sage: p.d_constant()
                    True
                    sage: p = R(x^3 - 3*x + 1)
                    sage: p.d_constant()
                    False

                Some interesting constants may arise unexpectedly when adding other derivations::

                    sage: R.<x,y> = QQ[]
                    sage: dx, dy = R.derivation_module().gens(); d = y*dx - x*dy
                    sage: dR = DifferentialRing(R, d)
                    sage: x,y = dR.gens()
                    sage: x.d_constant()
                    False
                    sage: y.d_constant()
                    False
                    sage: (x^2 + y^2).d_constant()
                    True
            '''
            ttype = self.parent().operator_types()[operation]
            if ttype == "homomorphism":
                result = self.operation(operation=operation) == self
            elif ttype in ("derivation", "skew"):
                result = self.operation(operation=operation) == self.parent().zero()
            else:
                raise ValueError(f"The operation {operation} has not a good type defined")

            return result
            
    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

RingsWithOperators = DRings #: alias for DRings (used for backward-compatibility)
_DRings = DRings.__classcall__(DRings)
####################################################################################################
###
### DEFINING THE FACTORY FOR THE CREATION OF WRAPPED RINGS
###
####################################################################################################
class DRingFactory(UniqueFactory):
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

        A :class:`DRing_Wrapper` with the new d-ring.
    '''
    def create_key(self, base : CommutativeRing, *operators : Callable, **kwds):
        # checking the arguments
        if len(operators) < 1:
            raise ValueError("At least one operator must be given.")
        elif len(operators) == 1 and isinstance(operators[0], Sequence):
            operators = operators[0]
        operators = list(operators)
        types = list(kwds.pop("types", len(operators)*["none"]))

        if isinstance(base, DRing_Wrapper):
            operators = list(base.construction()[0].operators) + operators
            types = list(base.construction()[0].types) + types
            base = base.wrapped
        
        # we convert the input into a common standard to create an appropriate key
        for (i, (operator, ttype)) in enumerate(zip(operators, types)):
            if ttype == "none":
                ## We decide the structure depending on the type of object
                if operator in base.Hom(base): # it is an homomorphism - we do nothing
                    types[i] = "homomorphism"
                    new_operator = operator
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
                    sum((base(operator(base_gen))*der_gen for (base_gen,der_gen) in zip(base.gens(),der_module.gens())), der_module.zero())
                )
            elif ttype == "skew":
                if not isinstance(parent(operator), RingDerivationModule):
                    raise NotImplementedError("Building skew-derivation from callable not implemented")
                twist = operator.parent().twisting_morphism()
                twist = base.Hom(base).one() if twist is None else twist
                new_operator = SkewMap(base, twist, operator)

            if new_operator != operator:
                operators[i] = new_operator
        return tuple([base, tuple(operators), tuple(types)])
            
    def create_object(self, _, key):
        base, operators, types = key

        return DRing_Wrapper(base, *operators, types=types)
DRing = DRingFactory("dalgebra.dring.DRing")
RingWithOperators = DRing #: alias fod DRing (used for backward-compatibility)

def DifferentialRing(base : CommutativeRing, *operators : Callable):
    r'''
        Method that calls the :class:`DRingFactory` with types always as "derivation".

        See documentation on :class:`DRingFactory` for further information.
    '''
    # checking the arguments
    if len(operators) < 1:
        logger.info("No operation is given: we set a zero derivative.")
        operators = [lambda p : 0]
    elif len(operators) == 1 and isinstance(operators[0], Sequence):
        operators = operators[0]

    return DRing(base, *operators, types=len(operators)*["derivation"])

def DifferenceRing(base: CommutativeRing, *operators : Callable):
    r'''
        Method that calls the :class:`DRingFactory` with types always as "homomorphism".

        See documentation on :class:`DRingFactory` for further information.
    '''
    # checking the arguments
    if len(operators) < 1:
        logger.info("No operation is given: we set an identity map.")
        operators = [base.Hom(base).one()]
    elif len(operators) == 1 and isinstance(operators[0], Sequence):
        operators = operators[0]

    return DRing(base, *operators, types=len(operators)*["homomorphism"])

####################################################################################################
###
### DEFINING THE ELEMENT AND PARENT FOR WRAPPED RINGS
###
####################################################################################################
class DRing_WrapperElement(Element):
    def __init__(self, parent, element):
        if(not isinstance(parent, DRing_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        Element.__init__(self, parent=parent)
        self.wrapped = element

    # Arithmetic methods
    def _add_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped + x.wrapped)
    def _sub_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped - x.wrapped)
    def __neg__(self) -> DRing_WrapperElement:
        return self.parent().element_class(self.parent(), -self.wrapped)
    def _mul_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _rmul_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _lmul_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _div_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        value = self.wrapped / x.wrapped
        if value in self.parent().wrapped:
            return self.parent().element_class(self.parent(), value) 
        else:
            return self.parent().fraction_field()._element_class(self.parent().fraction_field(), value.numerator(), value.denominator())
    def _floordiv_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped // x.wrapped) 
    def _mod_(self, x) -> DRing_WrapperElement:
        if parent(x) != self.parent(): # this should not happened
            x = self.parent().element_class(self.parent(), self.parent().base()(x))
        return self.parent().element_class(self.parent(), self.wrapped % x.wrapped) 
    def __pow__(self, n) -> DRing_WrapperElement:
        return self.parent().element_class(self.parent(), self.wrapped ** n)
    def __invert__(self) -> DRing_WrapperElement:
        value = ~self.wrapped
        if value in self.parent().wrapped:
            return self.parent().element_class(self.parent(), value)
        else:
            return self.parent().fraction_field().element_class(self.parent().fraction_field(), value)
    def __eq__(self, x) -> bool:
        if x is None: return False

        r = pushout(self.parent(), parent(x))
        if isinstance(r, DRing_Wrapper):
            return self.wrapped == r(x).wrapped
        return r(self) == r(x)

    def is_zero(self) -> bool:
        return self.wrapped == 0
    def is_one(self) -> bool:
        return self.wrapped == 1
    
    ## Other methods from rings and element
    def divides(self, other) -> bool:
        if not hasattr(self.wrapped, "divides"):
            raise AttributeError(f"Attribute 'divides' not included in {self.wrapped.parent()}")
        
        if other in self.parent():
            other = self.parent()(other)
        return self.wrapped.divides(other.wrapped)
    
    def numerator(self):
        try:
            numer = self.wrapped.numerator()
            if numer.parent() == self.parent().wrapped:
                destiny = self.parent()
            else:
                destiny = DRing(numer.parent(), *[operator.function for operator in self.parent().operators()], types=self.parent().operator_types())
            return destiny.element_class(destiny, numer)
        except Exception as e:
            raise AttributeError(f"'numerator' not an attribute for {self.__class__}. Reason: {e}")
    def denominator(self):
        try:
            denom = self.wrapped.denominator()
            if denom.parent() == self.parent().wrapped:
                destiny = self.parent()
            else:
                destiny = DRing(denom.parent(), *[operator.function for operator in self.parent().operators()], types=self.parent().operator_types())
            return destiny.element_class(destiny, denom)
        except Exception as e:
            raise AttributeError(f"'denominator' not an attribute for {self.__class__}. Reason: {e}")

    def gcd(self, other: DRing_WrapperElement) -> DRing_WrapperElement:
        try:
            other = self.parent()(other) # trying to cast other to be in ``self.parent()``
            g = self.wrapped.gcd(other.wrapped) # computing gcd in the wrapped level
            return self.parent().element_class(self.parent(), g)
        except AttributeError:
            raise AttributeError(f"[DRing] Wrapped element {self.wrapped} do no have method `gcd`")
        
    def is_unit(self) -> bool:
        return self.wrapped.is_unit()
    
    ## Other magic methods
    def __bool__(self) -> bool:
        return bool(self.wrapped)
    def __hash__(self) -> int:
        return hash(self.wrapped)
    def __str__(self) -> str:
        return str(self.wrapped)
    def __repr__(self) -> str:
        return repr(self.wrapped)
    def _latex_(self) -> str:
        return latex(self.wrapped)

class DRing_Wrapper(Parent):
    r'''
        Class for wrapping a Commutative ring and add operators over it.

        This class allows the user to translate a Commutative ring with some operations to 
        the category of :class:`DRings` preserving as many operations and properties
        of the original ring as possible, but adding the new functionality in the category.

        We do not recommend to use this class by itself. It should be created using the 
        corresponding factory (see :class:`DRingFactory` and its defined instance in 
        ``dalgebra.dring.DRing``).

        INPUT:

        * ``base``: the :class:`CommutativeRing` that will be wrapped.
        * ``operators``: a valid :class:`sage.categories.map.Map` to define an operator over ``self``.
        * ``types`` (optional): a list with the types (see :func:`DRings.ParentMethods.operator_types` 
          for further information). If nothing is given, the list will be automatically computed.
        * ``category`` (optional): argument from the category framework to allow further flexibility.
    '''
    Element = DRing_WrapperElement

    def __init__(self, 
        base : CommutativeRing, 
        *operators : Morphism | Sequence[Morphism],
        types : Sequence[str] = None, 
        category = None
    ):
        #########################################################################################################
        ### CHECKING THE ARGUMENTS
        ### 'base'
        if not base in _CommutativeRings:
            raise TypeError("Only commutative rings can be wrapped as DRing")

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
        categories = [_DRings, base.category()]
        if(isinstance(category, (list, tuple))):
            categories += list(category)
        elif(category != None): 
            categories.append(category) 

        #########################################################################################################
        ### CALLING THE SUPER AND ARRANGING SOME CONVERSIONS
        self.__wrapped = base
        super().__init__(base.base(), category=tuple(categories))
        
        # registering conversion to simpler structures
        current = self.__wrapped
        morph = DRing_Wrapper_SimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DRing_Wrapper_SimpleMorphism(self, current)
            current.register_conversion(morph)

        # registering coercion into its ring of linear operators
        try:
            operator_ring = self.linear_operator_ring()
            morph = DRing_Wrapper_SimpleMorphism(self, operator_ring)
            operator_ring.register_conversion(morph)
        except:
            pass

        #########################################################################################################
        ### CREATING THE NEW OPERATORS FOR THE CORRECT STRUCTURE
        self.__operators : tuple[WrappedMap] = tuple([WrappedMap(self, operator) for operator in operators])

        #########################################################################################################
        ### CREATING CACHED VARIABLES
        self.__linear_operator_ring = None
        self.__fraction_field : DFractionField = None

    @property
    def wrapped(self) -> CommutativeRing: return self.__wrapped

    def operators(self) -> tuple[WrappedMap]: return self.__operators

    def operator_types(self) -> tuple[str]: return self.__types

    def constant_ring(self, operation: int = 0) -> Parent:
        operation_type = self.operator_types()[operation]
        if operation_type == "homomorphism":
            if self.operators()[operation].function == self.wrapped.Hom(self.wrapped).one():
                return self.wrapped
        elif operation_type in ("skew", "derivation"):
            if self.operators()[operation].function.function == 0:
                return self.wrapped
            
        raise NotImplementedError(f"Constant ring do not implemented for {self} (operation {operation})")

    def linear_operator_ring(self):
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators using :mod:`ore_algebra`. It raises an error
            if this can not be done for any reason. The generators of the new ring are named
            depending on the type:

            * "D" for derivations,
            * "S" for homomorphisms,
            * "K" for skew derivations.

            If more than one is present, we use a subindex enumerating them.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R = DifferentialRing(QQ[x], diff)
                sage: R.linear_operator_ring()
                Univariate Ore algebra in D over Univariate Polynomial Ring in x over Rational Field

            This also works when having several operators::

                sage: B.<x,y> = QQ[]; dx,dy = B.derivation_module().gens()
                sage: s = B.Hom(B)([x+1,y-1])
                sage: R = DifferenceRing(DifferentialRing(B, dx, dy), s); R
                Ring [[Multivariate Polynomial Ring in x, y over Rational Field], (d/dx, d/dy, Hom({x: x + 1, y: y - 1}))]
                sage: R.linear_operator_ring()
                Multivariate Ore algebra in D_0, D_1, S over Multivariate Polynomial Ring in x, y over Rational Field

            We can check that `D_0` represents the first derivation (i.e., derivation w.r.t. `x`), `D_1` represents the second derivative and 
            `S` represents the special shift we are considering::

                sage: D_0,D_1,S = R.linear_operator_ring().gens()
                sage: D_0*x, D_0*y
                (x*D_0 + 1, y*D_0)
                sage: D_1*x, D_1*y
                (x*D_1, y*D_1 + 1)
                sage: S*x, S*y
                ((x + 1)*S, (y - 1)*S)

            This can only be used when the operators in the ring commute::

                sage: ns = B.Hom(B)([x^2, y^2])
                sage: T = DifferenceRing(DifferentialRing(B, dx, y*dy), ns); T
                Ring [[Multivariate Polynomial Ring in x, y over Rational Field], (d/dx, y*d/dy, Hom({x: x^2, y: y^2}))]
                sage: T.all_operators_commute()
                False
                sage: T.linear_operator_ring()
                Traceback (most recent call last):
                ...
                TypeError: Ore Algebra can only be created with commuting operators.

            But this can be done when the operators are not in the same ring::

                sage: U = DifferenceRing(B, ns); U.linear_operator_ring()
                Univariate Ore algebra in S over Multivariate Polynomial Ring in x, y over Rational Field
        '''
        from ore_algebra.ore_algebra import OreAlgebra
        if self.__linear_operator_ring == None:
            ## We need the operators to commute
            if not self.all_operators_commute():
                raise TypeError("Ore Algebra can only be created with commuting operators.")

            base_ring = self.wrapped

            operators = []
            def zero(_): return 0
            for operator, ttype in zip(self.operators(), self.operator_types()):
                if ttype == "homomorphism":
                    operators.append((f"S{f'_{self.differences().index(operator)}' if self.ndifferences() > 1 else ''}", operator.function, zero))
                elif ttype == "derivation":
                    operators.append((f"D{f'_{self.derivations().index(operator)}' if self.nderivations() > 1 else ''}", base_ring.Hom(base_ring).one(), operator.function))
                elif ttype == "skew":
                    operators.append((f"K{f'_{self.skews().index(operator)}' if self.nskews() > 1 else ''}", operator.function.twist, operator.function))

            self.__linear_operator_ring = OreAlgebra(self.wrapped, *operators)
        return self.__linear_operator_ring
        
    def inverse_operation(self, element: DRing_WrapperElement, operator: int = None) -> DRing_WrapperElement:
        if self.operator_types()[operator] == "homomorphism":
            try:
                return self.element_class(self, self.operators()[operator].function.inverse()(element.wrapped))
            except Exception as e:
                raise NotImplementedError(f"[inverse_operation] Inverses not implemented in general. Moreover: {e}")

        raise NotImplementedError("[inverse_operation] Inverses not implemented in general.")

    ## Coercion methods
    def _coerce_map_from_(self, S):
        return self.wrapped._coerce_map_from_(S) != None

    def __call__(self, x, *args, **kwds):
        result = self.wrapped(x, *args, **kwds)
        if result in self.wrapped:
            return self._element_constructor_(result)
        return result

    def _element_constructor_(self, x) -> DRing_WrapperElement:
        r'''
            Extended definition of :func:`_element_constructor_`.
        '''
        if x in SR: 
            # conversion from symbolic ring --> using its string representation
            x = str(x)
        elif isinstance(parent(x), DRing_Wrapper): 
            # conversion from other wrapped rings with operators --> we convert the element within
            x = x.wrapped
        if hasattr(self.wrapped, "_element_constructor_"):
            p = self.wrapped._element_constructor_(x)
        else:
            p = self.wrapped(x)
        return self.element_class(self, p)

    def _is_valid_homomorphism_(self, codomain, im_gens, base_map=None) -> bool:
        return self.wrapped._is_valid_homomorphism_(codomain, im_gens, base_map)

    def construction(self) -> DRingFunctor:
        return DRingFunctor([operator.function for operator in self.operators()], self.operator_types()), self.wrapped

    def _pushout_(self, other):
        scons, sbase = self.construction()
        if isinstance(other, DRing_Wrapper):
            ocons, obase = other.construction()
            cons = scons.merge(ocons)
            try:
                base = pushout(sbase, obase)
            except TypeError:
                base = pushout(obase, sbase)
            return cons(base)
        return None

    # Rings methods
    def fraction_field(self):
        try:
            if self.wrapped.is_field():
                return self
        except NotImplementedError:
            pass

        if self.__fraction_field is None:
            self.__fraction_field = DFractionField(self)
        return self.__fraction_field
    def characteristic(self) -> int:
        return self.wrapped.characteristic()

    def gens(self) -> tuple[DRing_WrapperElement]:
        return tuple([self.element_class(self, gen) for gen in self.wrapped.gens()])

    def ngens(self) -> int:
        return self.wrapped.ngens()

    def gen(self, i: int) -> DRing_WrapperElement:
        return self.gens()[i]

    ## Representation methods
    def __repr__(self) -> str:
        begin = "Differential " if self.is_differential() else "Difference " if self.is_difference() else ""
        return f"{begin}Ring [[{self.wrapped}], {repr(self.operators())}]"

    def __str__(self) -> str:
        return repr(self)

    def _latex_(self) -> str:
        return "".join((
            r"\left(",
            latex(self.wrapped),
            ", ",
            latex(self.operators()) if self.noperators() > 1 else latex(self.operators()[0]),
            r"\right)"
        ))

    ## Element generation
    def one(self) -> DRing_WrapperElement:
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R = DRing(QQ['x'], diff)
                sage: R.one()
                1
        '''
        return self.element_class(self, self.wrapped.one())
    
    def zero(self) -> DRing_WrapperElement:
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R = DRing(QQ['x'], diff)
                sage: R.zero()
                0
        '''
        return self.element_class(self, self.wrapped.zero())
    
    def random_element(self,*args,**kwds) -> DRing_WrapperElement:
        r'''
            Creates a random element in this ring.

            This method creates a random element in the base ring and cast it into an element of ``self``.
        '''
        p = self.wrapped.random_element(*args,**kwds)
        return self.element_class(self, p)

####################################################################################################
###
### DEFINING A GENERIC FIELD OF FRACTIONS FOR D-RINGS
###
####################################################################################################
class DFractionFieldElement(FractionFieldElement):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def derivative(self, derivation: int = None, times: int = 1):
        r'''Overridden method to force the use of the DRings structure'''
        return DRings.ElementMethods.derivative(self, derivation, times)
    
class DFractionField(FractionField_generic):
    r'''
        Class to represent a generic field of fractions of a d-ring.

        This class extends naturally the operations over the base ring and creates a natural extension for 
        fraction field to be used in the framework of difference and differential algebra.

        INPUT:

        * ``R``: the ring that will be transformed into a field of fractions. Must be in the category
          :class:`DRings` and also return ``True`` to the method ``is_integral_domain()``.
        * ``element_class``: (optional) class for the elements of the field of fractions. It is not recommended
          to provide anything here.
        * ``category``: (optional) base category to be use for these fields. By default it is the joint category 
          from quotient fields and d-rings.

        Methods implemented from DRings:

        * :func:`DRings.parent_class.operators`
        * :func:`DRings.parent_class.operator_types`
        * :func:`DRings.parent_class.constant_ring`: it tries to compute the field of fractions of the base ring
    '''
    def __init__(self, R, element_class=DFractionFieldElement, category=(_DRings & _QuotientFields)):
        ## Checking ``R`` is appropriate
        if not R in _DRings:
            raise TypeError(f"The base ring must be in the category of d-rings. Got {R}.")
        if not R.is_integral_domain():
            raise TypeError(f"The base ring must be an integral domain. Got {R}")

        super().__init__(R, element_class, category)

        ## We extend the operators from the base ring
        self.__operators = []
        for operator, ttype in zip(R.operators(), R.operator_types()):
            if ttype == "homomorphism":
                func = AdditiveMap(self, lambda p : operator(p.numerator()) / operator(p.denominator()))
            elif ttype == "derivation":
                func = AdditiveMap(self, lambda p : (operator(p.numerator())*p.denominator() - p.numerator()*operator(p.denominator())) / (p.denominator()**2))
            elif ttype == "skew":
                twist = operator.twist # this is necessary to know
                func = AdditiveMap(self, lambda p : (operator(p.numerator())*p.denominator() - p.numerator()*operator(p.denominator())) / (p.denominator() * twist(p.denominator())))
            self.__operators.append(func)

    def operators(self) -> Sequence[AdditiveMap]:
        return self.__operators
    
    def operator_types(self) -> Sequence[str]:
        return self.base().operator_types()
    
    def constant_ring(self, operation: int = 0) -> Parent:
        try:
            return self.base().constant_ring().fraction_field()
        except Exception as e:
            raise e

####################################################################################################
###
### DEFINING THE CONSTRUCTION FUNCTOR AND SIMPLE MORPHISM
###
####################################################################################################
class DRingFunctor(ConstructionFunctor):
    def __init__(self, operators: Sequence[Morphism], types: Sequence[str]):
        if len(operators) != len(types):
            raise ValueError("The length of the operators and types must coincide.")
        self.__operators = tuple(operators)
        self.__types = tuple(types)
        self.rank = 10 # just above PolynomialRing

        super().__init__(_CommutativeRings, _DRings)
    
    ### Methods to implement            
    def _apply_functor(self, x):
        return DRing(x, *self.__operators, types=self.__types)
        
    def _repr_(self):
        return f"DRing(*,{self.__operators}])"
        
    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.__operators == other.__operators and self.__types == other.__types

    def __merge_skews(self, f: SkewMap, g: SkewMap):
        r'''
            Method to merge to skew derivations.

            Currently, we only allow to mix two derivations `df` and `dg` when the pushout domain
            of both derivations is one of the domains of the derivations (i.e., we check for extension,
            but not for mixing derivations).

            In order to do so we do the following:

            1. We compute the ``pushout`` (`R`) of the domains of `df` and `dg`.
            2. We check `R` is the domain of `df` or `dg`. Let `S` be the other domain.
            3. We compute `df` and `dg`restricted to `S` by getting its representation over its generators.
            4. We check equality on the two restricted derivations.
            5. If they coincide, then we return the functor with the corresponding derivation.
        '''
        Mf = f.function.parent(); Mg = g.function.parent()
        # we try to merge the base ring of the modules
        R = pushout(Mf.domain(), Mg.domain())
        
        if R == Mf.domain(): 
            MR = Mf; twist = f.twist; goal = f.function; MS = Mg
        elif R == Mg.domain():
            MR = Mg; twist = g.twist; goal = g.function; MS = Mf
        else:
            raise AssertionError("We can only extend to one parent, no mix between them")
            
        # we try and cast both derivation into MS
        df = MS(f.function) if f.function in MS else MS([f.function(v) for v in MS.domain().gens()]) if len(MS.gens()) > 0 else MS()
        dg = MS(g.function) if g.function in MS else MS([g.function(v) for v in MS.domain().gens()]) if len(MS.gens()) > 0 else MS()
        
        if df - dg == 0: # this is the comparison on the restricted derivation
            if isinstance(f, DerivationMap):
                return DerivationMap(MR.domain(), goal)
            else: # general skew case
                return SkewMap(MR.domain(), twist, goal)
        return None

    def __merge_homomorphism(self, f, g):
        Mf = f.parent(); Mg = g.parent()
        # we try to merge the base ring of the modules
        R = pushout(Mf.domain(), Mg.domain())
        
        if R == Mf.domain(): M = Mf
        elif R == Mg.domain(): M = Mg
        else: raise AssertionError("We can only extend to one parent, no mix between them")    
        
        # we try and cast both derivation into M
        df = M(f) if f in M else M([f(v) for v in M.domain().gens()])
        dg = M(g) if g in M else M([g(v) for v in M.domain().gens()])
        
        return df if df == dg else None

    def merge(self, other):
        if isinstance(other, DRingFunctor):
            # we create a copy of the operators of self
            new_operators = [el for el in self.__operators]; new_types = [el for el in self.__types]
            self_operators = list(zip(self.__operators, self.__types))
            used_self = set()

            for (operator, ttype) in zip(other.__operators, other.__types):
                for i, (self_op, self_type) in enumerate(self_operators):
                    if not i in used_self:
                        if ttype == self_type:
                            try:
                                if ttype in ("skew", "derivation"):
                                    merged = self.__merge_skews(operator, self_op)
                                    if merged != None:
                                        used_self.add(i)
                                        new_operators[i] = merged
                                        break # we found an operator repeated
                                elif ttype == "homomorphism":
                                    merged = self.__merge_homomorphism(operator, self_op)
                                    if merged != None:
                                        used_self.add(i)
                                        new_operators[i] = merged
                                        break # we found an operator repeated
                            except (AssertionError, NotImplementedError):
                                pass
                else: # we need to add the operator to the final list
                    new_operators.append(merged); new_types.append(ttype)

            return DRingFunctor(new_operators, new_types)
        return None # Following definition of merge in ConstructionFunctor

    @property
    def operators(self) -> Sequence[Morphism]:  return self.__operators
    @property
    def types(self): return self.__types

class DRing_Wrapper_SimpleMorphism(Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`DRing_Wrapper` are included in simpler rings.
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
        return f"{repr(self.function)}"

    def _latex_(self) -> str:
        return latex(self.function)

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
    def __init__(self, domain : DRing_Wrapper, function : Morphism):
        if not isinstance(domain, DRing_Wrapper):
            raise TypeError("A WrappedMap can only be created for a 'DRing_Wrapper'")

        if function.domain() != domain.wrapped:
            raise ValueError(f"The map to be wrapped must have appropriate domain: ({domain.wrapped}) instead of ({function.domain()})")

        super().__init__(domain, lambda p : domain(function(domain(p).wrapped)))
        self.function = function

    def __repr__(self) -> str:
        if isinstance(self.function, RingHomomorphism_im_gens):
            im_gens = {v: im for (v,im) in zip(self.function.domain().gens(), self.function.im_gens())}
            return f"Hom({im_gens})"
        elif isinstance(self.function, IdentityMorphism):
            return "Id"
        else:
            return super().__repr__()

    def __str__(self) -> str:
        return f"Wrapped [{repr(self)}] over (({self.domain()}))"

    def _latex_(self) -> str:
        if isinstance(self.function, RingHomomorphism_im_gens):
            im_gens = {v: im for (v,im) in zip(self.function.domain().gens(), self.function.im_gens())}
            return r"\sigma\left(" + r", ".join(f"{latex(v)} \\mapsto {latex(im)}" for (v,im) in im_gens.items()) + r"\right)"
        elif isinstance(self.function, IdentityMorphism):
            return r"\text{id}"
        return super()._latex_()

__all__ = [
    "DRings", "DRing", "DFractionField", "DifferentialRing", "DifferenceRing", # names imported
    "RingsWithOperators", "RingWithOperators" # deprecated names (backward compatibilities)
]