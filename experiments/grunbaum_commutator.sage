import os, sys
sys.path.insert(0,"..") # dalgebra is here

from sage.all import SR, PolynomialRing, diff, QQ
from dalgebra import DifferentialRing, DifferentialPolynomialRing
from dalgebra.hierarchies.hierarchies import GetEquationsForSolution, generate_polynomial_equations, analyze_ideal
from dalgebra.logging.logging import logging_file_level, logging_stderr_level
import logging
from time import time

def print_help():
    PAD_SIZE = os.get_terminal_size()[0]
    print("".ljust(PAD_SIZE, "-"))
    print("--- GRUNBAUM SCRIPT HELP ".ljust(PAD_SIZE, "-"))
    print("".ljust(PAD_SIZE, "-"))
    print("Usage of the command:")
    print("\tsage grunbaum_commutator.sage [-v|-dv <>] [-u|-du <>] [-w|-dw <>] [-P <>] (options)")
    print("")
    print("where the arguments can be:")
    print("\t* [v|dv]: the value for the polynomial V(x). If `-v` is used, we allow an expression on `x`, otherwise, an integer is required.")
    print("\t* [u|du]: the value for the polynomial U(x). If `-u` is used, we allow an expression on `x`, otherwise, an integer is required.")
    print("\t* [w|dw]: the value for the polynomial W(x). If `-w` is used, we allow an expression on `x`, otherwise, an integer is required.")
    print("\t* [P]: order (integer) we are looking for a commutator.")
    print("Moreover, the options available are the following:")
    print("\t* [-cpus <>] Used for parallel computing with the given number of cpus when analyzing ideals.")
    print("\t* [-nogrb] Used to indicate that NO Gröbner basis computation must be done when analyzing ideals.")
    print("\t* [-log <>] The argument will be considered as a path for a desired complete Logger.")
    print("\t* [-stderr-log <>] Indicates the level that will be used for the STDERR logger.")
    print("\t* [-gen-log <>] Indicates the level that will be used in the package logger.")
    print("".ljust(PAD_SIZE, "-"))

#########################################################################################
### SCRIPT AREA
### Processing command input
if len(sys.argv) < 2 or any(el in sys.argv for el in ("-h", "--h", "-help", "--help", "-man", "--man", "man", "help")):
    print_help()
else:
    n = 1; degree_V = None; degree_U = None; degree_W = None; V = None; U = None; W = None; order_P = None; parallel = None; groebner = True; logfile = None; stderr_level = None; gen_log_level = None;
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
            elif sys.argv[n].endswith("nogrb"):
                groebner = False; n+=1
            elif sys.argv[n].endswith("cpus"):
                parallel = int(sys.argv[n+1]); n+=2
            elif sys.argv[n].endswith("gen-log"):
                gen_log_level = int(sys.argv[n+1]); n+=2
            elif sys.argv[n].endswith("stderr-log"):
                stderr_level = int(sys.argv[n+1]); n+=2
            elif sys.argv[n].endswith("log"):
                logfile = sys.argv[n+1]; n+=2
            else:
                n += 1
        else:
            n += 1

    ## Checking general arguments for seeting up the execution
    if stderr_level != None:
        logging_stderr_level(stderr_level)
    if gen_log_level != None:
        logging_file_level(gen_log_level)

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
            f"### Original command: sage grunbaum_commutator.sage {' '.join(sys.argv[2:])}\n",
            f"### {U=}\n### {V=}\n### {W=}\n### {order_P=}\n",
            f"####################################################################\n"
        ])
        out_file.flush()
        ctime = time()
        L,P,H = GetEquationsForSolution(
            order_L, 
            order_P, 
            [BD(str(L.coefficient(z[i]))) for i in range(order_L-1)], 
            generate_polynomial_equations, 
            loglevel=logging.DEBUG, 
            logfile=logfile, 
            method="linear"
        )
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
        out_file.flush()
        ctime = time()
        branches = analyze_ideal(
            H, 
            partial_solution, 
            [("var", f"c_{order_P}", 1)] + [("var", f"c_{a*order_L}", 0) for a in range(order_P//order_L)], 
            P.parent().base().wrapped,
            parallel=parallel,
            groebner=groebner,
            loglevel=logging.DEBUG,
            logfile=logfile
        )
        branches = list(set([branch for branch in branches])) # cleaning also repeated branches
        time_analysis = time()-ctime

        out_file.writelines([
            f"-- Computed branches of options in {time_analysis} secs.\n",
            f"-- Number of branches: {len(branches)}\n"
        ])
        out_file.flush()

        for i,branch in enumerate(branches):
            try:
                bL = branch.eval(L)
            except:
                bL = "Error evaluating L\n"
            try:
                bP = branch.eval(P)
            except:
                bP = "Error evaluating P\n"
            out_file.writelines([
                f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",
                f"%%% Data for branch {i+1}/{len(branches)}\n",
                f"Remaining ideal: {branch.I.gens()}\n",
                f"Solution on coefficients: {branch._SolutionBranch__solution}\n",
                f"Remaining variables: {branch.remaining_variables()}\n"] + ([
                f"Final parent: {bL.parent()}\n"
                f"Final operator: {branch.eval(L)}\n"] if not isinstance(bL, str) else [
                bL]) + ([f"Final commutator: {branch.eval(P)}\n"] if not isinstance(bP, str) else [
                bP]) + ([f"Lie bracket: {bL(z=bP)-bP(z=bL)}\n"] if all(not isinstance(e, str) for e in (bL, bP)) else []) + [ 
                f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"
            ])
            out_file.flush()

#########################################################################################
#########################################################################################
#########################################################################################
