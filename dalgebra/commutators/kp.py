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

    TODO: for kp -> depends on pseudo
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

from functools import lru_cache

from sage.rings.rational_field import QQ
from sage.structure.unique_representation import UniqueRepresentation

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
def kp_ring(n: int, *, name_var:str = "u") -> DPolynomialRing_Monoid:
    r'''
        Computes the ring where the KP hierarchy is usually established.

        This is helpful to other methods to predict where elements will be so they can build the appropriate coercions
        without computing the hierarchy.

        ::NO EXAMPLE::
    '''
    return DifferentialPolynomialRing(QQ, names=[f'{name_var}_{i}' for i in range(1, n)])

@lru_cache(maxsize=64)
def kp_generic(n: int, *, name_var:str = "u", name_partial:str = "D") -> tuple[DPolynomial]:
    r'''
        Method to compute the KP hierarchy with fully generic coefficients.

        This method computes the conditions for the coefficients `u_1,...,u_{n-1}` so the corresponding 
        pseudo operator `L` of order 1 can commute with `(L^n)_+`. The first value
        force the infinite tail of `L` to take a specific form, and the second value gives us the KP hierarchy
        of order `n` at level `n`.

        ::NO EXAMPLE::
    '''
    goal = kp_ring(n, name_var=name_var)
    goal_op_ring = PseudoDOperatorRing(goal, name_partial)

    return goal_op_ring.element_class(goal_op_ring, coefficient_map=GenericKPOperator(n, name_var=name_var), order_bound=1)

@cache_in_file
def kp_hierarchy(n: int, m: int, *, name_var:str = "u", name_partial:str = "D") -> tuple[DPolynomial]:
    r'''
        Method to compute the KP hierarchy with fully generic coefficients.

        This method computes the conditions for the coefficients `u_1,...,u_{n-1}` so the corresponding 
        pseudo operator `L` of order 1 can commute both with `(L^n)_+` and `(L^m)_+`. The first value
        force the infinite tail of `L` to take a specific form, and the second value gives us the KP hierarchy
        of order `n` at level `m`.

        ::NO EXAMPLE::
    '''
    # We compute the final truncated L operator
    L = kp_generic(n, name_var=name_var, name_partial=name_partial)
    Lm = (L**m).differential_part()
    lb = L*Lm - Lm*L
    return tuple(lb[k] for k in range(-1, -n, -1))


##################################################################################
## AUXILIARY CLASSES
##################################################################################
class GenericKPOperator(UniqueRepresentation):
    r'''
        Class to represent the generic pseudo-differential operator of order 1 with coefficients `u_1,...,u_{n-1}` and the infinite tail determined by the commutation with `(L^n)_+`.

        This class is created because this computation is universal and it make sense to store it as a unique element.

        ::NO EXAMPLE::
    '''
    def __init__(self, n: int, name_var:str = "u"):
        self.n = n
        self.name_var = name_var
        self.ring = kp_ring(n, name_var=name_var)

        self.__current = self.ring
        self.__sols = dict()

    def __extend_current(self):
        r'''Private method to extend the current computations one further iteration (::NO EXAMPLE::)'''
        m = self.__current.ngens() # we have u_1,...,u_m 
        ## we want to double it
        self.__current = self.__current.append_variables(*[f'{self.name_var}_{i}' for i in range(m+1, 2*m+1)]) # we add u_{m+1},...,u_{2m}
        OpRing = PseudoDOperatorRing(self.__current, 'D')
        D, Di = OpRing.gen(), OpRing.igen()
        L = D + sum(self.__sols.get(f'{self.name_var}_{i}', self.__current.gen(f'{self.name_var}_{i}'))*Di**i for i in range(1, 2*m+1))
        Ln = (L**self.n).differential_part()

        lb = L*Ln - Ln*L # this has order -1

        ## The length of sols gives the number of coefficients already computed, se we compute all the necessary intermediate steps
        for k in range(-1-len(self.__sols), -1-len(self.__sols)-m, -1):
            equ = lb[k](**self.__sols)
            self.__sols[f'{self.name_var}_{self.n-k-1}'] = equ.solve(self.__current.gen(f'{self.name_var}_{self.n-k-1}'))
        
        return self.__current, self.__sols

    def __call__(self, m: int) -> DPolynomial:
        r'''
            Returns the coefficient of the KP operator of order `n` at position `D^{m}` for `m` an integer (::NO EXAMPLE::)
        '''
        if m > 1: # The order is 1 by definition
            return self.ring.zero()
        elif m == 1: # The leading coefficient is 1 by definition
            return self.ring.one()
        elif m == 0: # The operator is in normal form
            return self.ring.zero()
        elif m > -self.n: # The first coefficients are fully generic
            return self.ring.gen(f'{self.name_var}_{-m}')[0]
        else: # Other coefficients require computations
            while f'{self.name_var}_{-m}' not in self.__sols:
                self.__extend_current()
            return self.ring(self.__sols[f'{self.name_var}_{-m}'])
