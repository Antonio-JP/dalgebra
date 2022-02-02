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