r'''
    Module to compute the KP hierarchy for generic operators

    Given a pseudo differential operator `L = D + u_1 D^{-1} + u_2 D^{-2} + ...` we can define for a certain order `n`
    its KP hierarchy as follows:

    1. Solve the equation `[L, (L^n)_+]` for the unknown functions `u_i` for `i \geq n`. This system can always be solved by iterated integration of the equations obtained by equating the coefficients of `D^k` to zero for `k < 0`.
    2. Evaluate the operator `L` at the solution obtained in step 1, and denote it by `L_n`.
    3. Given a level value `m`, compute the conditions for `[L_n, (L_n^m)_+]`. The first `n-1` conditions are all that we require: the following coefficients are always in the differential ideal of the first conditions, hence, these first conditions are sufficient and necessary for satisfying the whole commutation. 

    These conditions are what we will call the KP hierarchy of order `n` at level `m`. Note that the KP hierarchy of order `n` at level `m` is a system of ODEs for the functions `u_1, u_2, ..., u_{n-1}`.

    These hierarchies are defined based on Pseudo-differential operators with coefficients in `\mathbb{K}\{u_1,\ldots,u_{n-1}\}`, for `\mathbb{K}` a differential domain. 
    
    **WARNING (Not yet implemented)** A key feature of this module is that we will take into consideration the possibility that the domain is non commutative, which is the case for instance when we are working with matrix pseudo-differential operators. 

    ::NO EXAMPLES::
'''

# ****************************************************************************
#  Copyright (C) 2026 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

import logging
logger = logging.getLogger(__name__)

from sage.rings.rational_field import QQ

from ..dpolynomial.dpolynomial import DifferentialPolynomialRing, DPolynomial, DPolynomialRing_Monoid
from ..dpolynomial.pseudo_doperator import PseudoDOperatorRing
from ..logging.logging import cache_in_file

#################################################################################
## MAIN METHOD OF THE MODULE
##
## - It is cached in a file, so it is easy to recompute
## - There will be another method to be used as an interface when requiring a different
##   output field.
##################################################################################
def kp_ring(n: int) -> DPolynomialRing_Monoid:
    r'''
        Computes the ring where the KP hierarchy is usually established.

        This is helpful to other methods to predict where elements will be so they can build the appropriate coercions
        without computing the hierarchy.
    '''
    return DifferentialPolynomialRing(QQ, names=[f'u_{i}' for i in range(1, n)])


@cache_in_file
def kp_hierarchy_get(n: int, m: int) -> tuple[DPolynomial]:
    r'''
        Method to compute the KP hierarchy with fully generic coefficients.

        This method computes the conditions for the coefficients `u_1,...,u_{n-1}` so the corresponding 
        pseudo operator `L` of order 1 can commute both with `(L^n)_+` and `(L^m)_+`. The first value
        force the infinite tail of `L` to take a specific form, and the second value gives us the KP hierarchy
        of order `n` at level `m`.
    '''
    # We create the ring of pseudo-differential operators with generic coefficients
    # Since we can not create the infinite tail, we need to create the ring with a finite number of differential values
    # We can bound the used coefficients by 2*n.
    R = DifferentialPolynomialRing(QQ, names=[f'u_{i}' for i in range(1, 2*n+1)])
    u = (0,) + R.gens()
    DO = PseudoDOperatorRing(R, 'D')
    D = DO.gen()
    Di = DO.igen()

    # We create the generic pseudo-differential operator of order 1
    L = D + sum(u[i]*Di**(i) for i in range(1, n+m+2))

    # We compute the nth power differential part
    Ln = (L**n).differential_part()

    # We compute the conditions for commuting with this differential part
    lb = L*Ln - Ln*L # this has order -1
    sols = dict()
    for k in range(-1, -m-3, -1):
        equ = lb[k](**sols)
        sols[u[-n-k+1].variable_name()] = equ.solve(u[-n-k+1])

    # We compute the final truncated L operator
    L = D + sum(sols.get(u[i].variable_name(), u[i][0])*Di**(i) for i in range(1, n+m+2))
    Lm = (L**m).differential_part()

    lb = L*Lm - Lm*L
    ## We collect the equations in the field that we are interested
    B = R.remove_variables(*[u[n+i] for i in range(1,m+2)])
    return tuple(B(lb[k]) for k in range(-1, -n, -1))


