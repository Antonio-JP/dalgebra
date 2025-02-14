import sys
sys.path.insert(0, "../..") # dalgebra is here

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from dalgebra import *
from dalgebra.commutators import *
from dalgebra.commutators.ideals import SolutionBranch

import logging
from functools import lru_cache

from cProfile import Profile
from pstats import Stats, SortKey
from contextlib import nullcontext
from datetime import datetime

logging.getLogger("dalgebra").setLevel(int(10))

__profile__ = True


## We create the base ring for the differential operator
with (Profile() if __profile__ else nullcontext()) as pr:
    try:
        print("### Creating base ring")
        B = PolynomialRing(QQ, "x")
        R = DifferentialRing(B, [1]).fraction_field()
        (x,) = R.gens()

        ## In the usual case, we would create the new constants. This is not necessary here
        ## We simply create the operator L
        print("### Creating operator and coefficients")
        OpRing = DifferentialPolynomialRing(R, "z")
        z = OpRing.gens()[0]
        a = [1, 0, -175, 525, 3955, -8960] # values for numerator of coefficients
        L = sum(a[5-i]/x^(5-i if i < 4 else 0)*z[i] for i in range(5+1))

        Us = tuple([0 if L.coefficient_full(z[i]) == 0 else L.coefficient_full(z[i]).coefficients()[0] for i in range(L.order(z)-1)])
        ## Now we have the operator created. We would like to compute
        ## the centralizer of L
        print("### Computing centralizer")
        L_2, centr_GB, flag = GetCentralizer(
            Us, 18, 
            starting_level=6, update_bound=True, ignore_bound=True
        )
    except KeyboardInterrupt:
        print("Execution stopped by user")

if __profile__:
    stats = Stats(pr)
    stats.sort_stats(SortKey.TIME)
    today = datetime.now()
    stats.dump_stats(filename=f"./({today.year:04d}-{today.month:02d}-{today.day:02d})_recursion_error.prf")

# from dalgebra import *
# from dalgebra.commutators import almost_commuting_wilson
# P, Hs = almost_commuting_wilson(5,18)

# print("### Creating base ring")
# B = PolynomialRing(QQ, "x")
# R = DifferentialRing(B, [1]).fraction_field()
# (x,) = R.gens()
# ## In the usual case, we would create the new constants. This is not necessary here
# ## We simply create the operator L
# print("### Creating operator and coefficients")
# OpRing = DifferentialPolynomialRing(R, "z")
# z = OpRing.gens()[0]
# a = [1, 0, -175, 525, 3955, -8960] # values for numerator of coefficients
# L = sum(a[5-i]/x^(5-i if i < 4 else 0)*z[i] for i in range(5+1))

# Us = {f"u_{L.order(z)-i}": 0 if L.coefficient_full(z[i]) == 0 else L.coefficient_full(z[i]).coefficients()[0] for i in range(L.order(z)-1)}
# def evaluate_split(P, dic, split=100):
#     Ps = [sum(c*P.parent()(m) for c,m in zip(P.coefficients()[100*i:100*(i+1)], P.monomials()[100*i:100*(i+1)])) for i in range(len(P.monomials())//100 + 1)]
#     Ps_eval = [p(**dic) for p in Ps]
#     return sum(Ps_eval)
# def evaluate(P, dic):
#     return P(**dic)