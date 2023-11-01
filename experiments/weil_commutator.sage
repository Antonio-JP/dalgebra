#from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

from dalgebra.commutators.commutator import PolynomialCommutator
from dalgebra.commutators.ideals import analyze_ideal
import logging
from time import time

#########################################################################################
### SCRIPT AREA
### Processing command input
n = 1; order_L = None; order_P = None; degree = None
while n < len(sys.argv):
    if sys.argv[n].startswith("-"):
        if sys.argv[n].endswith("L"):
            order_L = int(sys.argv[n+1]); n+=2
        elif sys.argv[n].endswith("P"):
            order_P = int(sys.argv[n+1]); n+=2
        elif sys.argv[n].endswith("d"):
            degree = int(sys.argv[n+1]); n+=2
        else:
            n += 1
    else:
        n += 1
if order_L is None: order_L = 2
if order_P is None: order_P = 3
if degree is None: degree = 4

#########################################################################################
### Code to execute
with open(f"./[results]weil_commutator({order_L}-{order_P}-{degree}).txt", "wt") as out_file:
    out_file.writelines([
        f"####################################################################\n"
        f"###\n",
        f"### Results of computing the non-trivial Commutator in the Weil Algebra\n",
        f"###\n",
        f"### {order_L=}, {order_P=}, {degree=}\n",
        f"####################################################################\n"
    ])
    out_file.flush()
    ctime = time()
    L, P, H = PolynomialCommutator(order_L,order_P,degree,loglevel=logging.DEBUG)
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
    H = [poly(**partial_solution) for poly in H.gens()]
    out_file.write(f"-- Initial conditions on the ideal: {partial_solution}\n")
    ctime = time()
    branches = analyze_ideal(
        H, 
        partial_solution, 
        [("var", f"c_{order_P}", 1)] + [("var", f"c_{a*order_L}", 0) for a in range(order_P//order_L)], 
        P.parent().base().wrapped)
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
            f"Solution on coefficients: {branch._SolutionBranch__solution}\n",
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
