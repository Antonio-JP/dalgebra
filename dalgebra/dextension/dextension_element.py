r"""
File for the elements of d-extensions.

This file contains all the element structures necessary for defining a d-extension (see :mod:`.dextension_parent` for 
further information).

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

from sage.all import Parent, ZZ
from sage.rings.polynomial.multi_polynomial_element import MPolynomial_polydict
from sage.structure.element import Element #pylint: disable=no-name-in-module

from typing import Collection

#######################################################################################
###
### MAIN CLASS FOR THE ELEMENTS
###
#######################################################################################
class DExtension_element (MPolynomial_polydict):
    r'''
        Class for representing elements of a d-extension.

        Given a d-ring `(R,\Delta)`, we can always build an extension for it by creating a new transcendental element `t`
        and extnding each `\sigma \in \Delta` by setting a value for `t` in `R[t]`. We can do the same for several variables
        at the same time.

        This class extends the multivariate polynomials in SageMath (see :class:`sage.rings.polynomial.multi_polynomial_element.MPolynomial_polydict`)
        adding or overriding the new operations to the polynomial according to the category :class:`dalgebra.dring.DRings`.
        
        INPUT:

        * ``parent``: the parent structure where the element will belong.
        * ``x``: representation of ``self`` that will be set for defining ``self``.
    '''
    def __init__(self, parent : Parent, x : Element):
        super().__init__(parent, x)

    #######################################################################################
    ### METHODS OF DRINGS
    #######################################################################################
    def derivative(self, derivation: int = None, times: int = 1) -> DExtension_element:
        if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

        if(times == 0):
            return self
        elif(times == 1):
            return self.parent().derivative(self, derivation)
        else:
            return self.parent().derivative(self.derivative(derivation=derivation, times=times-1), derivation) 
    #######################################################################################
    ### Properties methods (is_...)
    #######################################################################################
    def as_linear_operator(self):
        r'''
            Method to convert this operator to a linear operator. 
            
            See method :func:`~.dpolynomial_ring.DPolynomialRing_dense.as_linear_operator`.
        '''
        return self.parent().as_linear_operator(self)

    # def degree(self, x=None, std_grading=False) -> int: 
    #     r'''Overriding :func:`degree` to fit the setting of D'''
    #     R = self.parent().polynomial_ring()
    #     if x != None and x.parent() == self.parent():
    #         x = R(x.polynomial())
        
    #     return R(self.polynomial()).degree(x, std_grading)

    def coefficient(self, degrees) -> DExtension_element:
        return self.base()(super().coefficient(degrees))
    
    def monomials(self) -> list[DExtension_element]:
        return [self.parent()(m) for m in super().monomials()]
    
    ###################################################################################
    ### Arithmetic methods
    ###################################################################################
    # def _add_(self, x):
    #     return self.parent().element_class(self.parent(), super()._add_(x))
    # def __neg__(self):
    #     return self.parent().element_class(self.parent(), super().__neg__())
    # def _sub_(self, x):
    #     return self.parent().element_class(self.parent(), super()._sub_(x))
    # def _mul_(self, x):
    #     return self.parent().element_class(self.parent(), super()._mul_(x))
    # def _rmul_(self, x):
    #     return self.parent().element_class(self.parent(), super()._rmul_(x))
    # def _lmul_(self, x):
    #     return self.parent().element_class(self.parent(), super()._lmul_(x))
    # def _mod_(self, x):
    #     return self - (self // x)*x
    #     #return self.parent().element_class(self.parent(), self.polynomial() % x.polynomial())
    # def _div_(self, x):
    #     return self.parent().element_class(self.parent(), self.polynomial() / x.polynomial())
    # def _floordiv_(self, x):
    #     R = self.parent().polynomial_ring()
    #     return self.parent().element_class(self.parent(), R(self.polynomial()) // R(self.parent()(x.polynomial())))
    # def __pow__(self, n):
    #     return self.parent().element_class(self.parent(), super().__pow__(n))

__all__ = []