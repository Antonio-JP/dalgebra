import sys
sys.path.insert(0,"..") # dalgebra is here

from datetime import datetime
from time import process_time
from cProfile import Profile
from contextlib import nullcontext
from pandas import read_csv
from pstats import Stats, SortKey
import tracemalloc
import os, csv

from dalgebra.commutators.almost_commuting import almost_commuting_wilson, generic_normal

def print_help():
    PAD_SIZE = os.get_terminal_size()[0]
    print("".ljust(PAD_SIZE, "-"))
    print("--- TIME TEST FOR ALMOST_COMMUTING_WILSON  ".ljust(PAD_SIZE, "-"))
    print("".ljust(PAD_SIZE, "-"))
    print("Usage of the command:")
    print("\tsage almost_commuting.sage [-table | (-run|-prf) <n> <m> <get_equs> <solver>]")
    print("")
    print("where the arguments can be:")
    print("\t* -table: prints the table of executed results so far")
    print("\t* (-run|-prf): executes one run of the tests with the given arguments:")
    print("\t\t+ <n>: a positive integer greater than 1")
    print("\t\t+ <m>: a positive integer greater than 1")
    print("\t\t+ <get_equs>: either 'direct' or 'recursive' indicating how to get the equations")
    print("\t\t+ <solver>: either 'integral' or 'linear' indicating how to solve the system")
    print("\t\t+ If we use '-prf' instead of '-run' we also save a profile of the execution")
    print("".ljust(PAD_SIZE, "-"))

def print_table():
    data = read_csv("./results_almost_commuting.csv")

    print(data.groupby(["get_equs", "solver", "n", "m"]).mean(numeric_only=True))


def test(n: int, m: int, get_equs: str, solver: str, out_file, profile: bool = False):
    r'''
        Runs :func:`almost_commuting_wilson` for given arguments, measure time and checks output.

        It prints the result in a CSV file in the following format:
        (`n`, `m`, `get_equs`, `solver`, `time`, `memory`, `almost_commute`)
    '''
    print(datetime.now(), f"[test] Executing `almost_commuting_wilson` with inputs \n\t{n=}, {m=}, {get_equs=}, {solver=}", flush=True)
    with (Profile() if profile else nullcontext()) as prf:
        tracemalloc.start()
        ctime = process_time()
        P, _ = almost_commuting_wilson(n,m,equation_gens=get_equs,solver=solver,to_cache=False)
        ctime = process_time() - ctime
        memory = tracemalloc.get_traced_memory()[1] / 2.**20
        tracemalloc.stop()

    if profile:
        print(datetime.now(), f"[test] Storing the time profile from last execution", flush=True)
        stats = Stats(prf)
        stats.sort_stats(SortKey.TIME)
        today = datetime.now()
        stats.dump_stats(filename=f"./profiles/({today.year:04d}-{today.month:02d}-{today.day:02d})almost_commuting_wilson_{get_equs}_{solver}[{n=},{m=}].prf")

    print(datetime.now(), f"[test] Checking the result and `L` almost commutes", flush=True)
    L = generic_normal(n)
    z = L.parent().gen("z")
    C = L.lie_bracket(P, z)
    almost_commute = C.order(z) < (n-1)

    print(datetime.now(), f"[test] Printing results", flush=True)

    out_file.writerow((n, m, get_equs, solver, ctime, memory, almost_commute))

if __name__ == "__main__":
    if len(sys.argv) >= 2:
        what = sys.argv[1]
        if what == "-table":
            print_table()
            sys.exit()
        elif what in ("-run", "-prf"):
            n = int(sys.argv[2])
            m = int(sys.argv[3])
            get_equs = sys.argv[4]
            solver = sys.argv[5]

            if n < 2: raise ValueError("Incorrect input (n). Must be positive integer greater than 1. See command -help for further information")
            if m < 2: raise ValueError("Incorrect input (m). Must be positive integer greater than 1. See command -help for further information")
            if not get_equs in ("direct", "recursive"): raise ValueError("Incorrect input (get_equs). Must be one of 'direct' or 'recursive'. See command -help for further information")
            if not solver in ("integral", "linear"): raise ValueError("Incorrect input (solver). Must be one of 'integral' or 'linear'. See command -help for further information")

            existed = os.path.exists("./results_almost_commuting.csv")

            with open("./results_almost_commuting.csv", "+at") as file:
                writer = csv.writer(file)
                if not existed:
                    writer.writerow(["n","m","get_equs","solver","time","memory","almost_commute"])
                test(n,m,get_equs,solver,writer,what=="-prf")
            sys.exit()
    print_help()
