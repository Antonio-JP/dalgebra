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
import logging

logger = logging.getLogger(__name__)
logger.setLevel(logging.ERROR)
formatter = logging.Formatter('%(asctime)s %(levelname)-8s %(message)s', datefmt='%Y-%m-%d %H:%M:%S')

#### CREATING THE HANDLERS
# first we strip the __init__p.py from __file__, then we add the relative path
path_to_logging = __file__[:-__file__[-1::-1].find('/')] + "logging/dalgebra.log" 
fh = logging.FileHandler(path_to_logging)
fh.setFormatter(formatter)
logger.addHandler(fh)
logger.propagate = False

# from .ring_w_operator import * # basic ring structures
# from .diff_polynomial import * # ring of difference/differential polynomials

def dalgebra_version():
    import pkg_resources
    return pkg_resources.get_distribution('dalgebra').version