r'''
Module containing the extra functionality for logging

This module contains the extra decorators to make the use of 
the Python package :mod:`logging` easier for the whole repository.

AUTHORS:

    - Antonio Jimenez-Pastor (2022-05-08): initial version
'''

# ****************************************************************************
#  Copyright (C) 2022 Antonio Jimenez-Pastor <jimenezpastor@lix.polytechnique.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

import functools, logging, sys

STDOUT_HANDLER = logging.StreamHandler(sys.stdout)

def verbose(logger):
    def inner(func):
        @functools.wraps(func)
        def wrap(*args, verbose=False, **kwds):
            if verbose:
                if STDOUT_HANDLER in logger.handlers:
                    # another function must has set this up, no need to remove at the end
                    print("stdout already in --> avoiding verbose")
                    verbose = False
                else:
                    print("stdout not in --> using verbose")
                    logger.addHandler(STDOUT_HANDLER)
                    old_level = logger.level
                    logger.setLevel(logging.INFO)
                
            out = func(*args, **kwds)

            if verbose:
                logger.setLevel(old_level)
                logger.removeHandler(STDOUT_HANDLER)

            return out
        return wrap
    return inner
