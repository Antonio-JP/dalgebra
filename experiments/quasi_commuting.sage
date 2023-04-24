from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

from time import time
from cProfile import Profile
from pstats import Stats, SortKey

from dalgebra.hierarchies.commutators import *

if __name__ == "__main__":
    print("+++ Measure timing for quasi-commuting element +++")
    print(sys.argv)
    n = int(sys.argv[1])
    m = int(sys.argv[2])
    method = sys.argv[3]
    print(f"\t - {n =}\n\t - {m = }\n\t - {method = }")


    with Profile() as profile:
        start = time()
        quasi_commuting_schr(n,m,method=method)
        total = time()-start
    
    stats = Stats(profile)
    stats.sort_stats(SortKey.TIME)
    print(f"[{n=},{m=},{method}] Saving profile...")
    stats.dump_stats(filename=f"./profiles/time_{method}[{n=},{m=}].prf")

    print(f"[{n=},{m=},{method}] Saving time...")
    with open(f"./results/{method}.txt", "a+") as file:
        file.write(f"{n};{m};{total}\n")

    print(f"--- [{n=},{m=},{method}]")
