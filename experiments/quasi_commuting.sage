from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

from time import time
from cProfile import Profile
from pstats import Stats, SortKey

from dalgebra.hierarchies.hierarchies import *

if __name__ == "__main__":
    n = int(sys.argv[1])
    m = int(sys.argv[2])
    method = sys.argv[3]


    with Profile() as profile:
        start = time()
        almost_commuting_schr(n,m,method=method)
        total = time()-start
    
    stats = Stats(profile)
    stats.sort_stats(SortKey.TIME)
    stats.dump_stats(filename=f"./profiles/time_{method}[{n=},{m=}].prf")

    with open(f"./results/{method}.csv", "a+") as file:
        file.write(f"{n};{m};{total}\n")
