r'''
Module containing the basic definitions for differential rings.

This file contains the definition of the category :class:`DifferentialRings`
that will contain all the differential structures and will help in the 
coercion and dynamic class system of Sage.

This module also includes a factory :class:`DifferentialRingFactory` that will 
help in the creation of differential structures from other Sage structures, 
adding to them the corresponding category and unifying the derivation method to the 
standards of an element in :class:`DifferentialRings`.

The main structure to achieve this is a wrapper class :class:`DifferentialRing_Wrapper`
that includes the functionality of the wrapped structure and adds the differential methods
defined in the category.

EXAMPLES::

    TODO

AUTHORS:

    - Antonio Jimenez-Pastor (2022-02-02): initial version
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

from .ring_w_operator import (RingWithOperator_Wrapper, RingWithOperator_WrapperElement, 
                                RingsWithOperator, CallableMap, RingWithOperatorFunctor)

_RingsWithOperator = RingsWithOperator.__classcall__(RingsWithOperator)

class DifferentialRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_RingsWithOperator]

    # methods that all differential structures must implement
    class ParentMethods:
        # abstract methods from the super category, now implemented
        def operation(self, element):
            return self.derivation(element)

        # new abstract methods for this category
        @abstract_method
        def derivation(self, _):
            raise NotImplementedError

        @abstract_method
        def constants(self):
            raise NotImplementedError

    # methods that all differential elements must implement
    class ElementMethods:
        # abstract methods from the super category
        def _operation(self, *_):
            return self._derivative()

        # new methods for this category
        def derivative(self, times=1):
            return self.operation(times) #pylint: disable=no-member

        def _derivative(self, *_):
            r'''
                Method that actually computes the derivative of an element of a ring with operator.
            '''
            return self.parent().derivation(self) #pylint: disable=no-member

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class DifferentialRingFactory(UniqueFactory):
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        if len(args) == 0:
            base = kwds["base"]; derivation = kwds.get("derivation", lambda p : 0)
        if len(args) == 1:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            base = args[0]; derivation = kwds.get("derivation", lambda p : 0)
        elif len(args) == 2:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "derivation" in kwds:
                raise TypeError("Duplicated value for the derivation")
            base = args[0]; derivation = args[1]

        return (base, derivation)

    def create_object(self, _, key):
        base, derivation = key

        if base in DifferentialRings:
            # check equality of the operators?
            return base

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

        return DifferentialRing_Wrapper(base, new_derivation)

DifferentialRing = DifferentialRingFactory("dalgebra.ring_w_operator.differential_ring.DifferentialRing")

class DifferentialRing_WrapperElement(RingWithOperator_WrapperElement):
    def __init__(self, parent, element):
        if(not isinstance(parent, DifferentialRing_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        super().__init__(parent, element)

class DifferentialRing_Wrapper(RingWithOperator_Wrapper):
    Element = DifferentialRing_WrapperElement

    def __init__(self, base, derivation, category=None):
        categories = [DifferentialRings()]
        if isinstance(category, (list, tuple)):
            categories += list(category)
        elif category != None:
            categories.append(category)
        super().__init__(base, derivation, "derivation", tuple(categories))

    def derivation(self, element):
        return super().operation(element)

    def operator_ring(self):
        return OreAlgebra(self.wrapped, ('D', lambda p : p, lambda p : self.derivation(p).wrapped))     

    ## Representation methods
    def __repr__(self) -> str:
        return f"Differential Ring [{self.wrapped}] with derivation [{repr(self.operator)}]"


class DifferentialRingFunctor(RingWithOperatorFunctor):
    def __init__(self, derivation):
        super().__init__(derivation)
        
    def _apply_functor(self, x):
        return DifferentialRing(x,self.operator())
        
    def _repr_(self):
        return "DifferentialRing(*,[%s])" %(repr(self.operator()))
        
__all__ = ["DifferentialRings", "DifferentialRing"]