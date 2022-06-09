r'''
Module containing the basic definitions for difference rings.

This file contains the definition of the category :class:`DifferenceRings`
that will contain all the difference structures and will help in the 
coercion and dynamic class system of Sage.

This module also includes a factory :class:`DifferenceRingFactory` that will 
help in the creation of difference structures from other Sage structures, 
adding to them the corresponding category and unifying the derivation method to the 
standards of an element in :class:`DifferenceRings`.

The main structure to achieve this is a wrapper class :class:`DifferenceRing_Wrapper`
that includes the functionality of the wrapped structure and adds the difference methods
defined in the category.

EXAMPLES::

    TODO

AUTHORS:

    - Antonio Jimenez-Pastor (2022-04-21): initial version
'''

# ****************************************************************************
#  Copyright (C) 2022 Antonio Jimenez-Pastor <jimenezpastor@lix.polytechnique.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.categories.all import Category
from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.pushout import pushout
from sage.misc.abstract_method import abstract_method
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from ore_algebra import OreAlgebra

from .ring_w_operator import (RingWithOperators_Wrapper, RingWithOperators_WrapperElement, 
                                CallableMap, RingWithOperatorsFunctor)
from .difference_ring import DifferenceRings
from .differential_ring import DifferentialRings

_DifferenceRings = DifferenceRings.__classcall__(DifferenceRings)
_DifferentialRings = DifferentialRings.__classcall__(DifferentialRings)

class DiffDiffRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_DifferenceRings,_DifferentialRings]

    # methods that all difference structures must implement
    class ParentMethods:
        # abstract methods from the super category, now implemented
        def operation(self, element, operation=0):
            return self.operators()[operation](element)

        def difference(self, element):
            return self.operators()[0](element)
        
        def shift(self, element):
            return self.difference(element)

        def derivative(self, element):
            return self.operators()[1](element)

        @abstract_method
        def constants(self, _):
            raise NotImplementedError

    # methods that all difference elements must implement
    class ElementMethods:
        # abstract methods from the super category
        def _operation(self, operation=0, *_):
            return self.parent().operation(self,operation=operation) #pylint: disable=no-member

        # new methods for this category
        def difference(self, times=1):
            return self.operation(times=times,operation=0) #pylint: disable=no-member

        def shift(self, times=1):
            return self.difference(times) #pylint: disable=no-member

        def derivative(self, times=1):
            return self.operation(times=times,operation=1) #pylint: disable=no-member

    # methods that all morphisms involving difference rings must implement
    class MorphismMethods: 
        pass

class DiffDiffRingFactory(UniqueFactory):
    r'''
        Factory to create uniquely Difference rings from usual rings Sage structures
    '''
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        if len(args) == 0:
            base = kwds["base"]
            difference = kwds.get("difference", lambda p : p)
            derivation = kwds.get("derivation", lambda p : 0)
        if len(args) == 1:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            base = args[0]
            difference = kwds.get("difference", lambda p : p)
            derivation = kwds.get("derivation", lambda p : 0)
        elif len(args) == 2:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "difference" in kwds:
                raise TypeError("Duplicated value for the difference")
            base = args[0]; difference = args[1]
            derivation = kwds.get("derivation", lambda p : 0)
        elif len(args) == 3:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "difference" in kwds:
                raise TypeError("Duplicated value for the difference")
            if "derivation" in kwds:
                raise TypeError("Duplicated value for the derivation")
            base = args[0]; difference = args[1]
            derivation = args[2]

        return (base, difference, derivation)

    def create_object(self, _, key):
        base, difference, derivation = key

        if base in DifferenceRings:
            # check equality of the operators?
            return base

        if isinstance(difference, Map):
            try:
                domain_po = pushout(difference.domain(), base)
                codomain_po = pushout(difference.codomain(), base) 
                if not domain_po == base:
                    raise TypeError(f"The domain [{difference.domain()}] must be something to be coerced into {base}")
                if not codomain_po == base:
                    raise TypeError(f"The codomain [{difference.codomain()}] must be something to be coerced into {base}")

                if domain_po != difference.domain() or codomain_po != difference.codomain():
                    new_difference = CallableMap(lambda p : difference(p), base, base)
                else:
                    new_difference = difference
            except:
                raise ValueError(f"{difference.domain()} or {difference.codomain()} could not be pushed into common parent with {base}")
        elif callable(difference):
            new_difference = CallableMap(difference, base, base)

        if isinstance(derivation, Map):
            try:
                domain_po = pushout(derivation.domain(), base)
                codomain_po = pushout(derivation.codomain(), base) 
                if not domain_po == base:
                    raise TypeError(f"The domain [{derivation.domain()}] must be something to be coerced into {base}")
                if not codomain_po == base:
                    raise TypeError(f"The codomain [{derivation.codomain()}] must be something to be coerced into {base}")

                if domain_po != derivation.domain() or codomain_po != derivation.codomain():
                    new_derivation = CallableMap(lambda p : derivation(p), base, base)
                else:
                    new_derivation = derivation
            except:
                raise ValueError(f"{derivation.domain()} or {derivation.codomain()} could not be pushed into common parent with {base}")
        elif callable(derivation):
            new_derivation = CallableMap(derivation, base, base)

        return DifferenceRing_Wrapper(base, new_difference, new_derivation)

DiffDiffRing = DiffDiffRingFactory("dalgebra.ring_w_operator.difference_ring.DifferenceRing")

class DiffDiffRing_WrapperElement(RingWithOperators_WrapperElement):
    def __init__(self, parent, element):
        if(not isinstance(parent, DiffDiffRing_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        super().__init__(parent, element)

class DiffDiffRing_Wrapper(RingWithOperators_Wrapper):
    Element = DiffDiffRing_WrapperElement

    def __init__(self, base, difference, derivation, category=None):
        categories = [DiffDiffRings()]
        if isinstance(category, (list, tuple)):
            categories += list(category)
        elif category != None:
            categories.append(category)
        super().__init__(base, [difference, derivation], ["difference", "derivation"], tuple(categories))

    def construction(self):
        return DiffDiffRingFunctor(self.operators()[0], self.operators()[1]), self.wrapped

    ## Representation methods
    def __repr__(self) -> str:
        return f"Difference-Differential Ring [{self.wrapped}] with difference [{repr(self.operators()[0])}] \
            and derivation [{repr(self.operators()[1])}]"

class DiffDiffRingFunctor(RingWithOperatorsFunctor):
    def __init__(self, difference, derivation):
        super().__init__([difference, derivation])
        
    def _apply_functor(self, x):
        return DiffDiffRing(x,*self.operators())
        
    def _repr_(self):
        return "DiffDiffRing(*,%s)" %(repr(self.operators()))
        
__all__ = ["DiffDiffRings", "DiffDiffRing"]