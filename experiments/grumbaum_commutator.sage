#from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

from sage.all import SR, PolynomialRing, diff, QQ
from dalgebra import DifferentialRing, DifferentialPolynomialRing
from dalgebra.hierarchies.hierarchies import GetEquationsForSolution, generate_polynomial_equations, analyze_ideal
import logging
from time import time

#########################################################################################
### SCRIPT AREA
### Processing command input
n = 1; degree_V = None; degree_U = None; degree_W = None; V = None; U = None; W = None; order_P = None
while n < len(sys.argv):
    if sys.argv[n].startswith("-"):
        if sys.argv[n].endswith("dv"):
            degree_V = int(sys.argv[n+1]); n+=2
        elif sys.argv[n].endswith("du"):
            degree_U = int(sys.argv[n+1]); n+=2
        elif sys.argv[n].endswith("dw"):
            degree_W = int(sys.argv[n+1]); n+=2
        elif sys.argv[n].endswith("u"):
            U = sys.argv[n+1]; n+=2
        elif sys.argv[n].endswith("v"):
            V = sys.argv[n+1]; n+=2
        elif sys.argv[n].endswith("w"):
            W = sys.argv[n+1]; n+=2
        elif sys.argv[n].endswith("P"):
            order_P = int(sys.argv[n+1]); n+=2
        else:
            n += 1
    else:
        n += 1

## By convention we put variables of the polynomials "u", "v", "w" with "u_*" where * is the degree
if degree_U is None and U is None:
    raise ValueError(f"Necessary some information for U(x)")
if degree_V is None and V is None:
    raise ValueError(f"Necessary some information for V(x)")
if degree_W is None and W is None:
    raise ValueError(f"Necessary some information for W(x)")
if order_P is None: order_P = 5

if U is None:
    U = sum(SR(f"u_{i}")*SR("x")^i for i in range(degree_U+1))
else:
    U = SR(U)
if V is None:
    V = sum(SR(f"v_{i}")*SR("x")^i for i in range(degree_V+1))
else:
    V = SR(V)
if W is None:
    W = sum(SR(f"w_{i}")*SR("x")^i for i in range(degree_W+1))
else:
    W = SR(W)

variables = list(set(sum((list(p.variables()) for p in (U,V,W)), [])))
PR = PolynomialRing(QQ, variables)
x = PR("x")
BD = DifferentialRing(PR, lambda p : diff(p, x))
R = DifferentialPolynomialRing(BD, names=["z"])
z = R.gens()[0]

U = BD(U); V = BD(V); W = BD(W)
FP = z[2] + V*z[0]
L = FP(z=FP) + U*z[1] + W*z[0]
order_L = 4

########################################################################################
## Code to execute
with open(f"./[results]grunbaum_commutator({U.degree(x)}-{V.degree(x)}-{W.degree(x)}-{order_P}).txt", "wt") as out_file:
    out_file.writelines([
        f"####################################################################\n"
        f"###\n",
        f"### Results of computing the non-trivial Commutator in the Weil Algebra\n",
        f"###\n",
        f"### {U=}\n### {V=}\n### {W=}\n### {order_P=}\n",
        f"####################################################################\n"
    ])
    out_file.flush()
    ctime = time()
    L,P,H = GetEquationsForSolution(order_L, order_P, [BD(str(L.coefficient(z[i]))) for i in range(order_L-1)], generate_polynomial_equations, loglevel=logging.DEBUG, method="linear")
    time_conditions = time()-ctime
    out_file.writelines([
        f"-- Generated operator {L=}\n",
        f"-- Generated commutator {P=}\n",
        f"-- Computed conditions for commutation in {time_conditions} secs.\n",
        f"-- Number of conditions: {len(H.gens())}\n",
        f"-- Number of variables: {len(H.ring().gens())}\n"
    ])
    out_file.flush()

    partial_solution = {f"c_{order_P}" : 1} # we set the highest constant to on to have exactly order_P
    partial_solution.update({f"c_{a*order_L}" : 0 for a in range(order_P//order_L + 1)}) # we set the coefficients of L and all its powers to zero)
    out_file.write(f"-- Initial conditions on the ideal: {partial_solution}\n")
    ctime = time()
    branches = analyze_ideal(
        H, 
        partial_solution, 
        [("var", f"c_{order_P}", 1)] + [("var", f"c_{a*order_L}", 0) for a in range(order_P//order_L)], 
        P.parent().base().wrapped,
        loglevel=logging.DEBUG
    )
    branches = list(set([branch for branch in branches if branch.eval(P) != 0])) # cleaning also repeated branches
    time_analysis = time()-ctime

    out_file.writelines([
        f"-- Computed branches of options in {time_analysis} secs.\n",
        f"-- Number of branches: {len(branches)}\n"
    ])
    out_file.flush()

    for i,branch in enumerate(branches):
        bL = branch.eval(L)
        bP = branch.eval(P)
        out_file.writelines([
            f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",
            f"%%% Data for branch {i+1}/{len(branches)}\n",
            f"Remaining ideal: {branch.I.gens()}\n",
            f"Remaining variables: {branch.remaining_variables()}\n",
            f"Final parent: {bL.parent()}\n"
            f"Final operator: {branch.eval(L)}\n",
            f"Final commutator: {branch.eval(P)}\n",
            f"Lie bracket: {bL(z=bP)-bP(z=bL)}\n"
            f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"
            f""
        ])
        out_file.flush()

#########################################################################################
#########################################################################################
#########################################################################################
