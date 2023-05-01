r"""
TODO: add documentation

AUTHORS:

    - Antonio Jimenez-Pastor (:git:`GitHub <Antonio-JP>`)

"""

# ****************************************************************************
#  Copyright (C) 2023 Antonio Jimenez-Pastor <ajpa@cs.aau.dk>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import annotations

from sage.rings.polynomial.multi_polynomial import MPolynomial #pylint: disable=no-name-in-module
from sage.rings.polynomial.multi_polynomial_libsingular import MPolynomial_libsingular #pylint: disable=no-name-in-module

#######################################################################################
###
### MAIN CLASS FOR THE ELEMENTS
###
#######################################################################################
class DExtension_Element (MPolynomial):
    r'''
        TODO: add documentation
    '''
    def __init__(self, *args, **kwds):
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")


    def as_linear_operator(self):
        r'''
            Method to convert this operator to a linear operator. 
            
            See method :func:`~.dpolynomial_ring.DPolynomialRing_dense.as_linear_operator`.
        '''
        return self.parent().as_linear_operator(self)

    # Magic methods
    def __call__(self, *args, **kwargs) -> None:
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")        

    def coefficients(self) -> list[DExtension_Element]:
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")  

    def coefficient(self, monomial) -> DExtension_Element:
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")  
    
    def monomials(self) -> list[DExtension_Element]:
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")  
    
    ###################################################################################
    ### Arithmetic methods
    ###################################################################################
    def _add_(self, x):
        return self.parent().element_class(self.parent(), super()._add_(x))
    def __neg__(self):
        return self.parent().element_class(self.parent(), super().__neg__())
    def _sub_(self, x):
        return self.parent().element_class(self.parent(), super()._sub_(x))
    def _mul_(self, x):
        return self.parent().element_class(self.parent(), super()._mul_(x))
    def _rmul_(self, x):
        return self.parent().element_class(self.parent(), super()._rmul_(x))
    def _lmul_(self, x):
        return self.parent().element_class(self.parent(), super()._lmul_(x))
    def _mod_(self, x):
        return self.parent().element_class(self.parent(), super()._mod_(x))
    def _div_(self, x):
        return self.parent().element_class(self.parent(), super()._div_(x))
    def _floordiv_(self, x):
        return self.parent().element_class(self.parent(), super()._floordiv_(x))
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), super().__pow__(n))

    ###################################################################################
    ### Other magic methods
    ###################################################################################
    def __repr__(self) -> str:
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")
    
    def _latex_(self) -> str:
        raise NotImplementedError("[DExtension_Element] __init__ not implemented")

class DExtension_Element_libsingular (DExtension_Element, MPolynomial_libsingular):
    pass

__all__ = []