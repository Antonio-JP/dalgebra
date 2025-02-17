r'''
SageMath script to generate indefinitely elements of the almost commuting basis for a given value of `n`. 

The result of these computations are cached in the `dalgebra` package, so they can then be used for updating the repository "da_wilson".

'''
import sys
sys.path.insert(0,"../..") # dalgebra is here

from dalgebra import dalgebra_folder
from dalgebra.commutators.almost_commuting import base_almost_commuting_wilson

import logging
import os
import argparse

logger = logging.getLogger("dalgebra")
logger.setLevel(logging.INFO)

RESULTS_FOLDER = os.path.join(dalgebra_folder(), "results", "almost_commuting")

def run_case(n,m):
    try:
        logger.info(f"[ACW - {n=}, {m=}] ++ Starting computing generic almost commuting operator for order {n} and level {m}...")
        base_almost_commuting_wilson(n,m, path_to_folder=RESULTS_FOLDER,extension="out")
        logger.info(f"[ACW - {n=}, {m=}] -- Finished computing generic almost commuting operator for order {n} and level {m}...")
    except KeyboardInterrupt:
        logger.info(f"[ACW - {n=}, {m=}] -- Interrupted by user")
        return False
    except:
        logger.exception(f"[ACW - {n=}, {m=}] -- Exception occurred")
        return False

    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run almost commuting basis generator.")
    parser.add_argument("-n", type=int, required=True, help="The order of the almost commuting operator.")
    parser.add_argument("-m", type=int, help="Starting level of search.")
    parser.add_argument("-M", type=int, help="Bound for the level of search.")
    args = parser.parse_args()

    n = args.n
    M = args.M
    m = 1 if not args.m else args.m
    go_on = True

    while go_on and m <= M:
        if m%n != 0:
            go_on = run_case(n, m)
        m += 1
