r"""
Package DAlgebra

This is the main entry package point for the functionalities included in the
repository :git:`Antonio-JP/dalgebra`.

AUTHORS::

    - Antonio Jimenez-Pastor (2012-05-15): initial version

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

## Configuring logger for this package
import logging, sys

print(__name__)
logger = logging.getLogger(__name__)
logger.setLevel(logging.ERROR)
formatter = logging.Formatter('%(asctime)s %(levelname)-8s %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
fh = logging.FileHandler("dalgebra.log")
# ch = logging.StreamHandler(sys.stderr)
fh.setFormatter(formatter)# ; ch.setFormatter(formatter)
logger.addHandler(fh)# ; logger.addHandler(ch)
logger.propagate = False

from .diff_polynomial import *
from .ring_w_operator import *
