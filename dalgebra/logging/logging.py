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
import functools
import logging
import os
import pickle
import sys

from sage.misc.persist import SagePickler # pylint: disable=no-name-in-module

STDOUT_HANDLER = logging.StreamHandler(sys.stdout)

__USED_LOGLEVEL = set()

def cut_string(string, size):
    if not isinstance(string, str):
        string = str(string)
    if len(string) <= size:
        return string
    return string[:size] + "..."

def print_args(size, *args, **kwds):
    output = ""
    if len(args):
        output += f"\n\t* args: {[cut_string(el, size) for el in args]}"
    if len(kwds):
        output += f"\n\t* kwds: {dict([(k, cut_string(v, size)) for (k,v) in kwds.items()])}"
    return output

def loglevel(logger : logging.Logger):
    def inner(func):
        @functools.wraps(func)
        def wrap(*args, loglevel=False, logfile=None, **kwds):
            loglevel = logging.INFO if (loglevel is True) else loglevel
            file_handler = None
            if loglevel:
                if logger in __USED_LOGLEVEL:
                    # another function must has set this up, no need to remove at the end
                    loglevel = False
                else:
                    # We set up the appropriate logging level
                    old_level = logger.level
                    __USED_LOGLEVEL.add(logger)
                    logger.setLevel(loglevel)

                    # If given a file, we set up the the handler for that file
                    if logfile is not None:
                        file_handler = logging.FileHandler(logfile)
                        file_handler.setFormatter(FORMATTER)
                        file_handler.setLevel(loglevel)
                        logger.addHandler(file_handler)

            try:
                logger.info(f"[{func.__name__}] {''.rjust(50, '+')}\n{' Starting  execution '.ljust(15, '+').rjust(15,'+')}{print_args(20, *args, **kwds)}")
                output = func(*args, **kwds)
                logger.info(f"[{func.__name__}]{' Execution completed '.ljust(15, '-').rjust(15,'-')}{print_args(20, *args, **kwds)}\n{''.rjust(50,'-')}")
                return output
            finally: # This is done
                if loglevel: # Removing the logger if was the original logged
                    logger.setLevel(old_level)
                    __USED_LOGLEVEL.remove(logger)
                if logfile is not None and file_handler is not None: # Removed the file handler if created
                    logger.removeHandler(file_handler)
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
        result can be reused directly. It includes an automatic detection of the
        version of the module allowing to easily repeat computations when needed.
    '''
    @functools.wraps(func)
    def wrapped(*args, to_cache:bool = True, path_to_folder:str = None, extension:str = "dmp", **kwds):
        if not to_cache:
            return func(*args, **kwds)
        else:
            from .. import dalgebra_version, dalgebra_folder
            file_for_result = f"{func.__name__}({','.join(str(el) for el in args)})[{','.join(f'{k}_{v}' for (k,v) in kwds.items())}]_{dalgebra_version()}.{extension}"
            ## Creating if needed the folder for the cache (if needed)
            path_to_folder = os.path.join(dalgebra_folder(), "__pycache__") if path_to_folder is None else path_to_folder
            os.makedirs(path_to_folder, exist_ok=True)

            ## Creating the final file path
            path_to_file = os.path.join(path_to_folder, file_for_result)
            if os.path.exists(path_to_file): # the result exists
                try:
                    with open(path_to_file, "rb") as file:
                        return pickle.load(file)
                except Exception:
                    pass

            ## Calling the function
            output = func(*args, **kwds)

            ## Caching the output
            try:
                with open(path_to_file, "wb") as file:
                    file.write(SagePickler.dumps(output))
            except Exception as e:
                print(f"[FILE_CACHE] Error while caching in file: {e}")
            return output

    return wrapped


#################################################################################
###
### SETTING THE DEFAULT LOGGERS AND METHODS TO HELP MANAGING THE LOGGER
###
#################################################################################
#### CREATING THE LOGGER AND FORMAT
logger = logging.getLogger("dalgebra")
logger.setLevel(logging.ERROR)
FORMATTER = logging.Formatter('%(asctime)s %(levelname)-8s %(message)s', datefmt='%Y-%m-%d %H:%M:%S')

GENERAL_FILE_HANDLER = logging.FileHandler(os.path.join(os.path.dirname(__file__), "dalgebra.log"))
GENERAL_STDERR_HANDLER = logging.StreamHandler(sys.stderr)

## Setting up default levels for handlers
GENERAL_FILE_HANDLER.setLevel(logging.INFO)

## Setting up the default formatter for handlers
for handler in (GENERAL_FILE_HANDLER, GENERAL_STDERR_HANDLER):
    handler.setFormatter(FORMATTER)

## Adding the default handlers to the main logger
for handler in (GENERAL_FILE_HANDLER, GENERAL_STDERR_HANDLER):
    logger.addHandler(handler)
logger.propagate = False

#### METHODS TO MANIPULATE THE LEVELS FOR DEFAULT HANDLERS
def logging_file_level(new_level: int): GENERAL_FILE_HANDLER.setLevel(new_level)
def logging_stderr_level(new_level: int): GENERAL_STDERR_HANDLER.setLevel(new_level)


__all__ = ["cache_in_file", "loglevel", "verbose"]
