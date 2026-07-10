from sage.all_cmdline import *   # import sage library

import sys
import time
sys.path.insert(0, "../..") # dalgebra is here

from dalgebra import *
from dalgebra.commutators import *
from sage.rings.rational_field import Q as QQ

def first_example():
    R = DifferentialRing(PolynomialRing(QQ,'x'), [1])
    x = R.gens()[0]
    DR = DifferentialPolynomialRing(R.fraction_field(), names=['z'])
    z = DR.gens()[0]
    U = (40/x**4, 32/x**3, -16/x**2)
    L, GB, fl = GetCentralizer(U, 5, starting_level=5, ignore_bound=True)
    return GB

def second_example():
    R = DifferentialRing(PolynomialRing(QQ, ['g_2', 'g_3']))
    g_2, g_3 = R.gens()
    E = DElliptic(R.fraction_field(), 'p_p^2 - 4*p^3 - g_2*p - g_3', names=('p',))
    p = E.gen()
    DR = DifferentialPolynomialRing(E, names=['z'])
    z = DR.gens()[0]
    U = (1, 0, -12*p)
    L, GB, fl = GetCentralizer(U, 5, starting_level=5, ignore_bound=True)
    return GB

def order(el):
    if isinstance(el, tuple):
        return el[1].order(el[1].parent().gen("z"))
    else:
        return el.order(el.parent().gen("z"))

if __name__ == "__main__":
    
    start = time.time()
    GB1 = first_example()
    first = time.time()
    GB2 = second_example()
    second = time.time()

    print(f"First example took {first-start} seconds")
    print(f"Second example took {second-first} seconds")

    print(f"First example GB: {[order(el) for el in GB1]}")
    print(f"Second example GB: {[order(el) for el in GB2]}")