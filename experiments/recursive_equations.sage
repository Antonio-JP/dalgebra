from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

import os
from csv import writer
from time import time

from sage.all import QQ
from dalgebra import DifferentialPolynomialRing
from dalgebra.hierarchies.hierarchies import __almost_commuting_direct, __almost_commuting_recursive, __names_u

existed = os.path.exists("./results/time_equs.csv")

ORDER_L = 10
ORDER_P = 20
REPETITIONS = 10

with open("./results/time_equs.csv", "a+") as file:
    csv_writer = writer(file)
    if not existed:
        csv_writer.writerow(["order_L", "order_P", "type", "time"])

    for n in range(2, ORDER_L):
        name_u = "u"
        names_u = __names_u(n, name_u)
        R = DifferentialPolynomialRing(QQ, names=names_u+["z"])
        for m in range(2, ORDER_P):
            for i in range(REPETITIONS):
                print(f"Executing DIRECT {n=}, {m=} ({i+1}/{REPETITIONS})...")
                time_direct = time()
                O_DIRECT = __almost_commuting_direct(R, n, m, "p", name_u, "z")
                time_direct = time() - time_direct
                csv_writer.writerow([n,m,"direct",time_direct])

                print(f"Executing RECURSIVE {n=}, {m=} ({i+1}/{REPETITIONS})...")
                time_rec = time()
                O_RECURSIVE = __almost_commuting_recursive(R, n, m, "p", name_u, "z")
                time_rec = time() - time_rec
                csv_writer.writerow([n,m,"recursive",time_rec])
                __almost_commuting_recursive.cache_clear()

                try:
                    assert O_DIRECT == O_RECURSIVE
                except AssertionError as e:
                    print("###################################################################")
                    print("### Found an error on computation?")
                    print(O_DIRECT)
                    print("--------------------------")
                    print(O_RECURSIVE)
                    print("###################################################################")
                    raise e


                file.flush()