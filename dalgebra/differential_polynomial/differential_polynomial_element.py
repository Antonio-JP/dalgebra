r"""
File for the ring structure of Differential polynomials

This file contains all the element structures for Differential polynomials.

AUTHORS:

    - Antonio Jimenez-Pastor (2012-05-19): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import cached_method, ZZ

from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialGen
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense, InfinitePolynomial_sparse

def is_InfinitePolynomial(element):
    return (isinstance(element, InfinitePolynomial_dense) or isinstance(element, InfinitePolynomial_sparse))

class DiffPolynomialGen (InfinitePolynomialGen):
    r'''
        TODO: do documentation
    '''
    def __init__(self, parent, name):
        from .differential_polynomial_ring import DiffPolynomialRing
        if(not (isinstance(parent, DiffPolynomialRing))):
            raise TypeError("The DiffPolynomialGen must have a DiffPolynomialRing parent")
        super().__init__(parent, name)

    def __getitem__(self, i):
        return self._parent(super().__getitem__(i))

    def contains(self, element):
        name = str(element)
        spl = name.split("_")
        first = "_".join(spl[:-1])
        return first == self._name

    def index(self, element):
        if(self.contains(element)):
            return int(str(element).split("_")[-1])

    def __hash__(self):
        return hash(self._name)

class DiffPolynomial (InfinitePolynomial_dense):
    r'''
        TODO: do documentation
    '''
    def __init__(self, parent, polynomial):
        if(is_InfinitePolynomial(polynomial)):
            polynomial = polynomial.polynomial()
        super().__init__(parent, polynomial)

    # Magic methods
    def __call__(self, *args, **kwargs):
        return self.parent().eval(self, *args, **kwargs)

    # Arithmetic methods
    def _add_(self, x):
        return DiffPolynomial(self.parent(), super()._add_(x))
    def _sub_(self, x):
        return DiffPolynomial(self.parent(), super()._sub_(x))
    def _mul_(self, x):
        return DiffPolynomial(self.parent(), super()._mul_(x))
    def _rmul_(self, x):
        return DiffPolynomial(self.parent(), super()._rmul_(x))
    def _lmul_(self, x):
        return DiffPolynomial(self.parent(), super()._lmul_(x))
    def __pow__(self, n):
        return DiffPolynomial(self.parent(), super().__pow__(n))

    # Differential methods
    @cached_method
    def derivative(self, times=1):
        if((not times in ZZ) or (times < 0)):
            raise ValueError("A differential polynomial can not be differentiated %s times" %times)
        elif(times == 0):
            return self
        elif(times > 1):
            return self.derivative(times=times-1).derivative()
        else:
            return self.parent().derivation(self)
