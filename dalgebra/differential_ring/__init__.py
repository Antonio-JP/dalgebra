r"""
Package ``differential_ring``

This is a package containing all the classes for creating and 
manipulating differential rings.

AUTHORS:

    - Antonio Jimenez-Pastor (2021-07-07): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from pkgutil import extend_path;
__path__ = extend_path(__path__, __name__)

from .differential_ring import *
