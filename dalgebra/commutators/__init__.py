r'''
    Module that contains all the files used in computation of commutators.

    This module contains all the files and code necessary in applications for computing
    non-trivial commutators for differential polynomial. The focus on the differential
    setting is temporal and will be generalized in the future to more generic
    :class:`DPolynomialRing_Monoid`.

    This module is split into 3 main subpackages:

    * :mod:`almost_commuting`: contains all necessary functions to compute the almost-commuting
      basis described by Wilson (in *Algebraic curves and soliton equations* (1985)). These computations
      also allows the computation of integrable hierarchies.
    * :mod:`ideals`: contains method that can analyze and study algebraic ideals. This is an auxiliary
      subpackage that is useful for other packages in the module.
    * :mod:`commutator`: contains all the methods necessary for computing non-trivial commutators for
      a differential linear operator. This requires the use of the other packages of the module.
    * :mod:`spectral`: contains all the methods and functionality related with the computation of
      spectral curves for a pair of commuting linear differential operators.
'''

# ****************************************************************************
#  Copyright (C) 2025 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from .almost_commuting import *
from .ideals import *
from .commutator import *
from .spectral import *