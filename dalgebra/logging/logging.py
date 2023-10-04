r'''
Module containing the extra functionality for logging

This module contains the extra decorators to make the use of 
the Python package :mod:`logging` easier for the whole repository.

AUTHORS:

    - Antonio Jimenez-Pastor (2022-05-08): initial version
'''

# ****************************************************************************
#  Copyright (C) 2023 Antonio Jimenez-Pastor <ajpa@cs.aau.dk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************
import functools, logging, os, pickle, sys

STDOUT_HANDLER = logging.StreamHandler(sys.stdout)

__USED_LOGLEVEL = set()

def loglevel(logger):
    def inner(func):
        @functools.wraps(func)
        def wrap(*args, loglevel=False, **kwds):
            loglevel = logging.INFO if (loglevel is True) else loglevel
            if loglevel:
                if logger in __USED_LOGLEVEL:
                    # another function must has set this up, no need to remove at the end
                    loglevel = False
                else:
                    # We set up the appropriate logging level
                    old_level = logger.level
                    __USED_LOGLEVEL.add(logger)
                    logger.setLevel(loglevel)
                
            try:
                out = func(*args, **kwds)
            except Exception as e:
                if loglevel:
                    logger.setLevel(old_level)
                    __USED_LOGLEVEL.remove(logger)
                raise e

            if loglevel:
                logger.setLevel(old_level)
                __USED_LOGLEVEL.remove(logger)

            return out
        return wrap
    return inner

def verbose(logger):
    def inner(func):
        @functools.wraps(func)
        def wrap(*args, verbose=False, **kwds):
            if verbose:
                if STDOUT_HANDLER in logger.handlers:
                    # another function must has set this up, no need to remove at the end
                    verbose = False
                else:
                    # We mimic the format of the current handlers
                    old_format = STDOUT_HANDLER.formatter
                    if len(logger.handlers) > 0: 
                        STDOUT_HANDLER.setFormatter(logger.handlers[0].formatter)
                    logger.addHandler(STDOUT_HANDLER)
                    old_level = logger.level
                    logger.setLevel(logging.INFO)
                
            out = func(*args, **kwds)

            if verbose:
                logger.setLevel(old_level)
                logger.removeHandler(STDOUT_HANDLER)
                STDOUT_HANDLER.setFormatter(old_format)

            return out
        return wrap
    return inner

def cache_in_file(func):
    r'''
        Decorator for a function to cache its result on a file that detects when the 
        result can be reused directly. It includes an atumatic detection of the 
        version of the module allowing to easily repeat computations when needed.
    '''
    @functools.wraps(func)
    def wrapped(*args, to_cache=True, **kwds):
        if not to_cache:
            return func(*args, **kwds)
        else:
            from .. import dalgebra_version
            file_for_result = f"{func.__name__}({','.join(str(el) for el in args)})[{','.join(f'{k}_{v}' for (k,v) in kwds.items())}]_{dalgebra_version()}.dmp"
            ## Creating if neede the folder for the cache
            path_to_folder = os.path.join(os.path.dirname(__file__) if __name__ != "__main__" else "./", "..", "__pycache__")
            os.makedirs(path_to_folder, exist_ok=True)

            ## Creating the final file path 
            path_to_file = os.path.join(path_to_folder, file_for_result)
            if os.path.exists(path_to_file): # the result exists
                try:
                    with open(path_to_file, "rb") as file:
                        return pickle.load(file)
                except Exception as e:
                    pass
            
            ## Calling the function
            output = func(*args, **kwds)

            ## Caching the output
            try:
                with open(path_to_file, "wb") as file:
                    pickle.dump(output, file)
            except Exception as e:
                print(f"[FILE_CACHE] Error while caching in file: {e}")
            return output

    return wrapped

__all__ = ["cache_in_file", "loglevel", "verbose"]
