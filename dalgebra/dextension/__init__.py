r"""
Package ``dextension``

This is a package containing all the classes for extending d-rings (see module
:mod:`~dalgebra.dring`) in a polynomial manner. This can be interpret, when the added
elements are transcendental or algebraically independent, as polynomial rings where the 
operations are extended in a specific way.

AUTHORS:

    - Antonio Jimenez-Pastor (:git:`GitHub <Antonio-JP>`)

"""

# ****************************************************************************
#  Copyright (C) 2023 Antonio Jimenez-Pastor <ajpa@cs.aau.dk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from .dextension_parent import *
from .dextension_element import *
from .dextension_field import *
