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
from sage.categories.map import Map
from sage.categories.pushout import pushout
from sage.misc.abstract_method import abstract_method
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from ore_algebra import OreAlgebra

from .ring_w_operator import (RingWithOperator_Wrapper, RingWithOperator_WrapperElement, 
                                RingsWithOperator, CallableMap, RingWithOperatorFunctor)

_RingsWithOperator = RingsWithOperator.__classcall__(RingsWithOperator)

class DifferenceRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_RingsWithOperator]

    # methods that all difference structures must implement
    class ParentMethods:
        # abstract methods from the super category, now implemented
        def operation(self, element):
            return self.difference(element)

        # new abstract methods for this category
        @abstract_method
        def difference(self, _):
            raise NotImplementedError

        @abstract_method
        def constants(self):
            raise NotImplementedError

    # methods that all difference elements must implement
    class ElementMethods:
        # abstract methods from the super category
        def _operation(self, *_):
            return self._difference()

        # new methods for this category
        def difference(self, times=1):
            return self.operation(times)

        def _difference(self, *_):
            r'''
                Method that actually computes the difference of an element of a ring with operator.
            '''
            return self.parent().difference(self)

    # methods that all morphisms involving difference rings must implement
    class MorphismMethods: 
        pass

class DifferenceRingFactory(UniqueFactory):
    r'''
        Factory to create uniquely Difference rings from usual rings Sage structures
    '''
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        if len(args) == 0:
            base = kwds["base"]; difference = kwds.get("difference", lambda p : p)
        if len(args) == 1:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            base = args[0]; difference = kwds.get("difference", lambda p : p)
        elif len(args) == 2:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "difference" in kwds:
                raise TypeError("Duplicated value for the difference")
            base = args[0]; difference = args[1]

        return (base, difference)

    def create_object(self, _, key):
        base, difference = key

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

        return DifferenceRing_Wrapper(base, new_difference)

DifferenceRing = DifferenceRingFactory("dalgebra.ring_w_operator.difference_ring.DifferenceRing")

class DifferenceRing_WrapperElement(RingWithOperator_WrapperElement):
    def __init__(self, parent, element):
        if(not isinstance(parent, DifferenceRing_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        super().__init__(parent, element)

class DifferenceRing_Wrapper(RingWithOperator_Wrapper):
    Element = DifferenceRing_WrapperElement

    def __init__(self, base, difference, category=None):
        categories = [DifferenceRings()]
        if isinstance(category, (list, tuple)):
            categories += list(category)
        elif category != None:
            categories.append(category)
        super().__init__(base, difference, "difference", tuple(categories))

    def difference(self, element):
        return super().operation(element)

    def operator_ring(self):
        return OreAlgebra(self.wrapped, ('S', lambda p : self(p).difference().wrapped, lambda _ : self.wrapped.zero()))

    ## Representation methods
    def __repr__(self) -> str:
        return f"Difference Ring [{self.wrapped}] with difference [{repr(self.operator)}]"

class DifferentialRingFunctor(RingWithOperatorFunctor):
    def __init__(self, difference):
        super().__init__(difference)
        
    def _apply_functor(self, x):
        return DifferenceRing(x,self.operator())
        
    def _repr_(self):
        return "DifferenceRing(*,[%s])" %(repr(self.operator()))
        