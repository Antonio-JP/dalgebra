from sage.all_cmdline import *   # import sage library

import sys
sys.path.insert(0,"..") # dalgebra is here

from datetime import datetime
from time import time, process_time
from cProfile import Profile
from pstats import Stats, SortKey
import tracemalloc
import os, psutil, csv
from psutil._pslinux import pcputimes, pmem

from dalgebra.hierarchies.hierarchies import *

def get_exec_data(proc: psutil.Process)->tuple:
    ## Getting time usage
    times=proc.cpu_times()
    memory=proc.memory_info()
    return times,memory

def get_time_from_data(beg_time: pcputimes, end_time: pcputimes)->dict:
    output = dict()
    output[("time","user")] = end_time.user - beg_time.user
    output[("time","system")] = end_time.system - beg_time.system
    output[("time","iowait")] = end_time.iowait - beg_time.iowait

    return output


def get_mem_from_data(beg_mem: pmem, end_mem: pmem)->dict:
    output = dict()
    output[("memory","rss")] = (end_mem.rss - beg_mem.rss)/(2.**20)
    output[("memory","vms")] = (end_mem.vms - beg_mem.vms)/(2.**20)
    output[("memory","shared")] = (end_mem.shared - beg_mem.shared)/(2.**20)
    output[("memory","text")] = (end_mem.text - beg_mem.text)/(2.**20)
    output[("memory","lib")] = (end_mem.lib - beg_mem.lib)/(2.**20)
    output[("memory","data")] = (end_mem.data - beg_mem.data)/(2.**20)
    output[("memory","dirty")] = (end_mem.dirty - beg_mem.dirty)/(2.**20)

    return output

if __name__ == "__main__":
    n = int(sys.argv[1])
    m = int(sys.argv[2])
    method = sys.argv[3]
    equ_method = sys.argv[4]

    print(f"+++ Starting execution of {n=}, {m=}, {method=}, {equ_method=}")
    self_p = psutil.Process(os.getpid())


    with Profile() as profile:
        beg_time, beg_mem = get_exec_data(self_p)
        tracemalloc.start()
        start = time(); pr_time = process_time()
        almost_commuting_schr(n,m,method=method,equations_method=equ_method,to_cache=False)
        total = time()-start; pr_time = process_time() - pr_time
        peak_mem = tracemalloc.get_traced_memory()[1]/(2.**20)
        tracemalloc.stop()
        end_time, end_mem = get_exec_data(self_p)
    
    data_output = get_time_from_data(beg_time, end_time)
    data_output[("time", "process")] = pr_time
    data_output.update(get_mem_from_data(beg_mem, end_mem))
    data_output[("memory","peak")] = peak_mem
    today = datetime.now()
    stats = Stats(profile)
    stats.sort_stats(SortKey.TIME)
    stats.dump_stats(filename=f"./profiles/({today.year:04d}-{today.month:02d}-{today.day:02d})time_{method}_{equ_method}[{n=},{m=}].prf")

    file = f"./results/new_{method}_{equ_method}.csv"
    existed = os.path.exists(file)
    with open(file, "a+") as file:
        csv_writer = csv.writer(file)
        if not existed:
            csv_writer.writerow(["n", "m", "time"] + list(data_output.keys()))
        csv_writer.writerow([n, m, total] + list(v for _,v in data_output.items()))
        
    print(f"--- Finished execution of {n=}, {m=}, {method=}, {equ_method=}")
