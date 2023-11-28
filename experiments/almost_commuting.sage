import sys
sys.path.insert(0,"..") # dalgebra is here

from datetime import datetime
from time import process_time
from cProfile import Profile
from contextlib import nullcontext
from pandas import read_csv, DataFrame, set_option
from pstats import Stats, SortKey
import tracemalloc
import os, csv

from dalgebra.commutators.almost_commuting import base_almost_commuting_wilson, generic_normal

def print_help():
    PAD_SIZE = os.get_terminal_size()[0]
    print("".ljust(PAD_SIZE, "-"))
    print("--- TIME TEST FOR ALMOST_COMMUTING_WILSON  ".ljust(PAD_SIZE, "-"))
    print("".ljust(PAD_SIZE, "-"))
    print("Usage of the command:")
    print("\tsage almost_commuting.sage [-table <<args>> | (-run|-prf) <n> <m> <get_equs> <solver>]")
    print("")
    print("where the arguments can be:")
    print("\t* -table: prints the table of executed results so far. It allows optional arguments:")
    print("\t\t+ -n <N>: prints results with n=N")
    print("\t\t+ -m <M>: prints results with m=M")
    print("\t\t+ -get_equs <E>: prints results with get_equs=E")
    print("\t\t+ -solver <S>: prints results with solver=S")
    print("\t\t+ -latex <filename>: put the output table into LaTeX format in file './filename.tex'")
    print("\t* (-run|-prf): executes one run of the tests with the given arguments:")
    print("\t\t+ <n>: a positive integer greater than 1")
    print("\t\t+ <m>: a positive integer greater than 1")
    print("\t\t+ <get_equs>: either 'direct' or 'recursive' indicating how to get the equations")
    print("\t\t+ <solver>: either 'integral' or 'linear' indicating how to solve the system")
    print("\t\t+ If we use '-prf' instead of '-run' we also save a profile of the execution")
    print("".ljust(PAD_SIZE, "-"))

def print_table(*argv):
    ## Reading the filters

    i = 0; n_filter = list(); m_filter = list(); equs_filter = list(); solver_filter = list(); latex = None

    while i < len(argv):
        if argv[i] == "-n":
            n_filter.append(int(argv[i+1])); i += 2
        elif argv[i] == "-m":
            m_filter.append(int(argv[i+1])); i += 2
        elif argv[i] == "-get_equs":
            equs_filter.append(argv[i+1]); i += 2
        elif argv[i] == "-solver":
            solver_filter.append(argv[i+1]); i += 2
        elif argv[i] == "-latex":
            latex = argv[i+1]; i += 2
        else:
            i+=1

    data = read_csv("./results_almost_commuting.csv")

    filters = lambda row : ((len(n_filter) == 0 or row['n'] in n_filter) and
                            (len(m_filter) == 0 or row['m'] in m_filter) and
                            (len(equs_filter) == 0 or row['get_equs'] in equs_filter) and
                            (len(solver_filter) == 0 or row['solver'] in solver_filter))
    
    data = DataFrame([row for (_,row) in data.iterrows() if filters(row)], columns = data.columns)

    to_print = data.groupby(["get_equs", "solver", "n", "m"]).mean(numeric_only=True)
    set_option('display.max_rows', int(2)*len(to_print)) # guarantee the table is fully printed
    print(to_print)

    if latex != None:
        new_rows = dict()
        for i,row in data.reset_index().iterrows():
            key = row["n"], row["m"]
            if not key in new_rows:
                new_rows[key] = {"DI": "?", "DL": "?", "RI": "?", "RL": "?"}
            if row["get_equs"] == "direct" and row["solver"] == "integral":
                to_change = "DI"
            elif row["get_equs"] == "direct":
                to_change = "DL"
            elif row["solver"] == "integral":
                to_change = "RI"
            else:
                to_change = "RL"
            new_rows[key][to_change] = row["time"]

        new_data = DataFrame([
            [key[0],key[1]]+[value["DI"], value["DL"], value["RI"], value["RL"]] 
            for (key,value) in sorted(new_rows.items()) if all(v != "?" for v in value.values())], 
            columns = ["n","m","DI","DL","RI","RL"]
        )
        with open(f"./{latex}.tex", "wt") as file:
            new_data.style.format_index(
                "\\textbf{{{}}}", escape="latex", axis=1).highlight_min(
                subset=["DI","DL","RI","RL"], axis=1, props="font-weight:bold;").hide(
                axis="index").to_latex(
                    file,
                    convert_css=True,
                    column_format="cc|cccc",
                    position="!ht",
                    position_float="centering",
                    hrules=True
            )
      
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
        P, _ = base_almost_commuting_wilson(n,m,equation_gens=get_equs,solver=solver,to_cache=False)
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
            print_table(*sys.argv[2:])
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
