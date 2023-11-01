import os, sys
sys.path.insert(0,"..") # dalgebra is here

from io import TextIOWrapper
from sage.all import SR, diff, QQ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element_generic import Polynomial
from dalgebra import DifferentialRing, DifferentialPolynomialRing
from dalgebra.commutators.commutator import GetEquationsForSolution, generate_polynomial_equations
from dalgebra.commutators.ideals import analyze_ideal
from dalgebra.dpolynomial.dpolynomial_element import DPolynomial, DPolynomialGen
from dalgebra.dring import DRing_WrapperElement
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

def process_arguments(*argv: str) -> tuple[
                                           DPolynomial, 
                                           tuple[DRing_WrapperElement,DRing_WrapperElement,DRing_WrapperElement], 
                                           tuple[Polynomial,DPolynomialGen],
                                           int,tuple[int,bool,str]
]:
    ######################################################
    ## Default values for inputs
    n = 0
    degree_V = None; degree_U = None; degree_W = None; V = None; U = None; W = None
    order_P = None
    parallel = None; groebner = True; logfile = None
    stderr_level = None; gen_log_level = None
    ######################################################
    ## Processing the list of argv
    while n < len(argv):
        if argv[n].startswith("-"):
            if argv[n].endswith("dv"):
                degree_V = int(argv[n+1]); n+=2
            elif argv[n].endswith("du"):
                degree_U = int(argv[n+1]); n+=2
            elif argv[n].endswith("dw"):
                degree_W = int(argv[n+1]); n+=2
            elif argv[n].endswith("u"):
                U = argv[n+1]; n+=2
            elif argv[n].endswith("v"):
                V = argv[n+1]; n+=2
            elif argv[n].endswith("w"):
                W = argv[n+1]; n+=2
            elif argv[n].endswith("P"):
                order_P = int(argv[n+1]); n+=2
            elif argv[n].endswith("nogrb"):
                groebner = False; n+=1
            elif argv[n].endswith("cpus"):
                parallel = int(argv[n+1]); n+=2
            elif argv[n].endswith("gen-log"):
                gen_log_level = int(argv[n+1]); n+=2
            elif argv[n].endswith("stderr-log"):
                stderr_level = int(argv[n+1]); n+=2
            elif argv[n].endswith("log"):
                logfile = argv[n+1]; n+=2
            else:
                n += 1
        else:
            n += 1

    ######################################################
    ## Updating log levels if necessary
    if stderr_level != None:
        logging_stderr_level(stderr_level)
    if gen_log_level != None:
        logging_file_level(gen_log_level)

    ######################################################
    ## Processing the variables U,V,W
    ## By convention we put variables of the polynomials "u", "v", "w" with "u_*" where * is the degree
    if degree_U is None and U is None:
        raise ValueError(f"Necessary some information for U(x)")
    if degree_V is None and V is None:
        raise ValueError(f"Necessary some information for V(x)")
    if degree_W is None and W is None:
        raise ValueError(f"Necessary some information for W(x)")
    if order_P is None: order_P = 5

    U = sum(SR(f"u_{i}")*SR("x")^i for i in range(degree_U+1)) if U is None else SR(U)
    V = sum(SR(f"v_{i}")*SR("x")^i for i in range(degree_V+1)) if V is None else SR(V)
    W = sum(SR(f"w_{i}")*SR("x")^i for i in range(degree_W+1)) if W is None else SR(W)

    ######################################################
    ## Creating the Differential Structures
    variables = list(set(sum((list(p.variables()) for p in (U,V,W)), [])))
    PR = PolynomialRing(QQ, variables)
    x = PR("x")
    BD = DifferentialRing(PR, lambda p : diff(p, x))
    R = DifferentialPolynomialRing(BD, names=["z"])
    z = R.gens()[0]

    ######################################################
    ## Creating the operator L
    U = BD(U); V = BD(V); W = BD(W)
    FP = z[2] + V*z[0]
    L = FP(z=FP) + U*z[1] + W*z[0]

    return L, (U,V,W), (x,z), order_P, (parallel, groebner, logfile)

def run_execution(
        L: DPolynomial, 
        U: DRing_WrapperElement, V: DRing_WrapperElement, W: DRing_WrapperElement, 
        x: Polynomial, z: DPolynomialGen, 
        order_P: int, 
        parallel: int, groebner: bool, logfile: str, 
        outfile: TextIOWrapper
):
    outfile.writelines([
        f"####################################################################\n"
        f"###\n",
        f"### Results of computing the non-trivial Commutator in the Weil Algebra\n",
        f"###\n",
        f"### Original command: sage grunbaum_commutator.sage {' '.join(sys.argv[2:])}\n",
        f"### {U=}\n### {V=}\n### {W=}\n### {order_P=}\n",
        f"####################################################################\n"
    ]);  outfile.flush()
    ctime = time()
    L,P,H = GetEquationsForSolution(
        order_P, 
        n = order_L, 
        U = [BD(str(L.coefficient(z[i]))) for i in range(order_L-1)], 
        extract=generate_polynomial_equations, 
        loglevel=logging.DEBUG, 
        logfile=logfile
    )
    time_conditions = time()-ctime
    outfile.writelines([
        f"-- Generated operator {L=}\n",
        f"-- Generated commutator {P=}\n",
        f"-- Computed conditions for commutation in {time_conditions} secs.\n",
        f"-- Number of conditions: {len(H.gens())}\n",
        f"-- Number of variables: {len(H.ring().gens())}\n"
    ]); outfile.flush()

    partial_solution = {f"c_{order_P}" : 1} # we set the highest constant to on to have exactly order_P
    partial_solution.update({f"c_{a*order_L}" : 0 for a in range(order_P//order_L + 1)}) # we set the coefficients of L and all its powers to zero)
    H = [poly(**partial_solution) for poly in H.gens()]
    outfile.write(f"-- Initial conditions on the ideal: {partial_solution}\n")
    outfile.flush()
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
    time_analysis = time()-ctime

    outfile.writelines([
        f"-- Computed branches of options in {time_analysis} secs.\n",
        f"-- Number of branches: {len(branches)}\n"
    ]); outfile.flush()

    for i,branch in enumerate(branches):
        try:
            bL: DPolynomial = branch.eval(L)
        except:
            bL = "Error evaluating L\n"
        try:
            bP: DPolynomial = branch.eval(P)
        except:
            bP = "Error evaluating P\n"
        outfile.writelines([
            f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n",
            f"%%% Data for branch {i+1}/{len(branches)}\n",
            f"Remaining ideal: {branch.I.gens()}\n",
            f"Solution on coefficients: {branch._SolutionBranch__solution}\n",
            f"Remaining variables: {branch.remaining_variables()}\n"] + ([
            f"Final parent: {bL.parent()}\n"
            f"Final operator: {bL}\n"] if not isinstance(bL, str) else [bL]) + ([
            f"Final commutator: {bP}\n"] if not isinstance(bP, str) else [bP]) + ([
            f"Lie bracket: {bL.lie_bracket(bP, z)}\n"] if all(not isinstance(e, str) for e in (bL, bP)) else []) + [ 
            f"%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"
        ]); outfile.flush()

#########################################################################################
### SCRIPT AREA
### Processing command input
if len(sys.argv) < 2 or any(el in sys.argv for el in ("-h", "--h", "-help", "--help", "-man", "--man", "man", "help")):
    print_help()
else:
    try:
        L, (U,V,W), (x,z), order_P, (parallel, groebner, logfile) = process_arguments(*sys.argv[1:])
    except Exception as e: # Case with errors in arguments
        print(e)
        print_help()
        sys.exit()

    order_L = L.order(z)
    BD = L.parent().base()

    ########################################################################################
    ## Code to execute
    with open(f"./[results]grunbaum_commutator({U.degree(x)}-{V.degree(x)}-{W.degree(x)}-{order_P}).txt", "wt") as outfile:
        run_execution(L, U, V, W, x, z, order_P, parallel, groebner, logfile, outfile)

#########################################################################################
#########################################################################################
#########################################################################################
