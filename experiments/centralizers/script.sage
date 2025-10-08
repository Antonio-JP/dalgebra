r'''
    Script to analyze centralizers for different families os coefficients.

    The script has several arguments:

    - `n`: the size of the operator `L` to be analyzed.
    - `m`: the order of the first non-trivial element in the centralizer.
    - `family`: either "rational", "hyperbolic" or "elliptic".
    - `maple`: if given, the script will use Maple to solve algebraic systems.
    - `simple`: if given we will consider as systems the ideal of the last column.

    This script is essentially a combination of the cells in the notebook `commutator_order_5.ipynb`.
'''

import sys
sys.path.insert(0, "../..") # dalgebra is here

from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ

from dalgebra import *
from dalgebra.commutators import *
from dalgebra.commutators.ideals import SolutionBranch

import logging
from functools import lru_cache
import pickle
import argparse

logging.getLogger("dalgebra").setLevel(int(15))

@lru_cache
def create_base(family: str, **kwds):
    if family == "rational":
        B = PolynomialRing(QQ, "x")
        R = DifferentialRing(B, [1]).fraction_field()
        (x,) = R.gens()
        return R, (x,), family
    if family == "trigonometric":
        BD = DifferentialRing(QQ)
        E = DElliptic(BD, "cos^2 + cos_p^2 - 1", names=("cos",))
        cosh = E.gen()
        sinh = cosh.derivative()
        return E, (cosh, sinh), family
    if family == "hyperbolic":
        BD = DifferentialRing(QQ)
        E = DElliptic(BD, "cosh^2 - cosh_p^2 - 1", names=("cosh",))
        cosh = E.gen()
        sinh = cosh.derivative()
        return E, (cosh, sinh), family
    if family == "hyperbolic_exp":
        BD = DifferentialRing(QQ)
        E = DMonomial(BD, "e_x", "e_x")
        t = E.gen()
        cosh = (t + (1/t))/2
        sinh = (t - (1/t))/2
        return E.fraction_field(), (cosh, sinh), family
    if family.startswith("elliptic"):
        # kwds contains the parameters g_2 and g_3
        try:
            g_2 = QQ(kwds.get("g_2", "g_2"))
        except TypeError:
            g_2 = kwds.get("g_2", "g_2")
        try:
            g_3 = QQ(kwds.get("g_3", "g_3"))
        except TypeError:
            g_3 = kwds.get("g_3", "g_3")
        
        lc = QQ(kwds.get("lc", 4))

        constants = [el for el in (g_2, g_3) if isinstance(el, str)]
        if lc != 1:
            family = f"{family}_lc[{lc}]"
        if not isinstance(g_2, str):
            family = f"{family}_{g_2}"
        if not isinstance(g_3, str):
            family = f"{family}_{g_3}"

        if len(constants) > 0:
            B = PolynomialRing(QQ, constants)
            BD = DifferentialRing(B, [0,0]).fraction_field()
        else:
            BD = DifferentialRing(QQ)
        E = DElliptic(BD, f"eta_p^2 - {lc}*eta^3 - {g_2}*eta - {g_3}", names=("eta",))
        eta = E.gens()[0]
        return E, (eta,), family
    raise ValueError(f"Unknown family {family}")

@lru_cache
def get_templates(generators: tuple, family: str, n:int) -> dict:
    if family == "rational":
        (x,) = generators
        f = 1/x^2
    elif family == "trigonometric":
        cos = generators[0]
        f = 1/cos^2
    elif family == "hyperbolic":
        cosh = generators[0]
        f = 1/cosh^2
    elif family == "hyperbolic_exp":
        cosh = generators[0]
        f = 1/cosh^2
    elif family.startswith("elliptic"):
        (eta,) = generators
        f = eta
    else:
        raise ValueError(f"Unknown family {family}")
   
    templates = {2:[f]}
    for i in range(3, n+1):
        g = f.derivative(times=i-2)
        templates[i] = [el[0]/g.denominator() for el in g.conditions_to_zero()]

    return templates

def add_constants(R, generators, n: int, family: str) -> dict:
    templates = get_templates(generators, family, n)
    constants = {i:
                 [f"a_{i}_{j}" for j in range(len(templates[i]))]
                 if len(templates[i]) > 1 else [f"a_{i}"]
                for i in range(2,n+1)}
   
    all_constants = sum(constants.values(), [])
    R_wa = R.add_constants(*all_constants)

    constants = {k: [R_wa(el) for el in v] for k, v in constants.items()}
   
    return R_wa, constants

def create_Us(generators: tuple, constants: dict, family: str):
    N = max(constants.keys())
    print(f"{N=}")
    templates = get_templates(generators, family, N)
    Us = dict()
    print(constants.keys())
    print(templates.keys())
    for k in templates.keys():
        Us[k] = sum(c*t for (c,t) in zip(constants[k], templates[k]))
   
    print(Us)
    n = min(Us.keys())
    return tuple([Us[i] for i in range(N, n-1, -1)])

def main(n: int, M: int, family: str, maple: bool = False, simple: bool = False, **kwds):
    R, generators, family = create_base(family, **kwds)
    _, constants = add_constants(R, generators, n, family)
    Us = create_Us(generators, constants, family)

    L, P, H = dict(), dict(), dict()
    cases, computed = dict(), dict()

    for m in range(1, M+1):
        if m%n != 0:
            print(f"+ Computing Equations for level {m}...")
            L[m],P[m],H[m] = GetEquationsForLevel(n, m, Us, filename=family, maple=maple, simple=simple)
            print(f"- Computed Equations for level {m}...")
            if m > n:
                print(f"+ Analyzing GDH for level {m}...")
                cases[m], computed[m] = AnalyzeGDH(n,m,L[m],H[m], H, filename=family, table=True)
                print(f"- Analyzed GDH for level {m}...")

    return cases, computed

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze centralizers for different families of coefficients.")
    parser.add_argument("-n", type=int, required=True, help="The size of the operator L to be analyzed.")
    parser.add_argument("-m", type=int, required=True, help="The order of the first non-trivial element in the centralizer.")
    parser.add_argument("-family", type=str, required=True, choices=["rational", "trigonometric", "hyperbolic", "hyperbolic_exp", "elliptic"], help="The family of coefficients.")
    parser.add_argument("-simple", action="store_true", help="Consider as systems the ideal of the last column.")
    parser.add_argument("-maple", action="store_true", help="Use Maple to solve algebraic systems.")
    
    # Parse additional arbitrary arguments of the form -name value
    args, unknown_args = parser.parse_known_args()
    extra_args = {}
    i = 0
    while i < len(unknown_args):
        if unknown_args[i].startswith("-") and i + 1 < len(unknown_args):
            key = unknown_args[i][1:]
            value = unknown_args[i + 1]
            extra_args[key] = value
            i += 2
        else:
            i += 1

    from timeit import default_timer as timer
    start = timer()
    cases, computed = main(args.n, args.m, args.family, args.maple, args.simple, **extra_args)
    end = timer()
    print(f"%%% Execution time: {end - start:.5f} seconds")