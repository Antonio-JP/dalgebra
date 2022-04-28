r"""
Module ``ring_w_operator``

This is the main entry package point for the functionalities of rings with operators associated,
such as difference and differential rings.

AUTHORS::

    - Antonio Jimenez-Pastor (2022-04-20): initial version

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

from .ring_w_operator import RingsWithOperator, RingWithOperator
from .differential_ring import DifferentialRings, DifferentialRing
from .difference_ring import DifferenceRings, DifferenceRing