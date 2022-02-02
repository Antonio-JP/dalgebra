r"""
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
"""

# ****************************************************************************
#  Copyright (C) 2022 Antonio Jimenez-Pastor <jimenezpastor@lix.polytechnique.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import CommutativeRing, ZZ
from sage.categories.all import Category, CommutativeRings
from sage.misc.abstract_method import abstract_method
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)

class DifferentialRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_CommutativeRings]

    # methods that all differential structures must implement
    class ParentMethods:
        @abstract_method
        def derivation(self, element):
            pass

    # methods that all differential elements must implement
    class ElementMethods:
        def derivative(self, times=1):
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self._derivative()
            else:
                return self.derivative(times=times-1).derivative()

        @abstract_method
        def _derivative(self):
            r'''
                Method that actually computes the derivative of an element of a differential ring.
            '''
            raise NotImplementedError

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class DifferentialRingFactory(UniqueFactory):
    pass

DifferentialRing = DifferentialRingFactory("dalgebra.differential_ring.differential_ring.DifferentialRing")

class DifferentialRing_Wrapper(CommutativeRing):
    pass