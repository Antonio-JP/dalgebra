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
from sage.categories.map import Map
from sage.categories.pushout import pushout
from sage.misc.abstract_method import abstract_method
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from ore_algebra import OreAlgebra

from .ring_w_operator import RingWithOperator_Wrapper, RingWithOperator_WrapperElement, RingsWithOperator, CallableMap

_RingsWithOperator = RingsWithOperator.__classcall__(RingsWithOperator)

class DifferentialRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_RingsWithOperator]

    # methods that all differential structures must implement
    class ParentMethods:
        # abstract methods from the super category, now implemented
        def operation(self, element):
            return self.derivative(element)

        # new abstract methods for this category
        @abstract_method
        def derivative(self, _):
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
            return self.operation(times)

        def _derivative(self, *_):
            r'''
                Method that actually computes the derivative of an element of a ring with operator.
            '''
            return self.parent().derivative(self)

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class DifferentialRingFactory(UniqueFactory):
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        if len(args) == 0:
            base = kwds["base"]; derivative = kwds["derivative"]
        if len(args) == 1:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            base = args[0]; derivative = kwds["derivative"]
        elif len(args) == 2:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "derivative" in kwds:
                raise TypeError("Duplicated value for the derivative")
            base = args[0]; derivative = args[1]

        return (base, derivative)

    def create_object(self, _, key):
        base, derivative = key

        if base in DifferentialRings:
            # check equality of the operators?
            return base

        if isinstance(derivative, Map):
            try:
                domain_po = pushout(derivative.domain(), base)
                codomain_po = pushout(derivative.codomain(), base) 
                if not domain_po == base:
                    raise TypeError(f"The domain [{derivative.domain()}] must be something to be coerced into {base}")
                if not codomain_po == base:
                    raise TypeError(f"The codomain [{derivative.codomain()}] must be something to be coerced into {base}")

                if domain_po != derivative.domain() or codomain_po != derivative.codomain():
                    new_derivative = CallableMap(lambda p : derivative(p), base, base)
            except:
                raise ValueError(f"{derivative.domain()} or {derivative.codomain()} could not be pushed into common parent with {base}")
        elif callable(derivative):
            new_derivative = CallableMap(derivative, base, base)

        return DifferentialRing_Wrapper(base, new_derivative)

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

    def __init__(self, base, derivative, category=None):
        categories = [DifferentialRings()]
        if isinstance(category, (list, tuple)):
            categories += list(category)
        elif category != None:
            categories.append(category)
        super().__init__(base, derivative, "derivative", tuple(categories))

    def derivative(self, element):
        return super().operation(element)

    def operator_ring(self):
        return OreAlgebra(self.wrapped, ('D', lambda p : p, lambda p : self(p).derivative().wrapped))

    def __contains__(self, element):
        if(element.parent() in DifferentialRings):
            return element.parent() == self
        return element in self.wrapped        

    ## Representation methods
    def __repr__(self) -> str:
        return f"Differential Ring [{self.wrapped}] with derivative [{repr(self.operator)}]"
