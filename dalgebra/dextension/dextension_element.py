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

import logging

from sage.all import Parent, ZZ
from sage.rings.polynomial.multi_polynomial_element import MPolynomial_polydict
from ..dring import DRings

logger = logging.getLogger(__name__)

def _GCD(*elements):
    try:
        from sage.arith.misc import gcd
        return gcd(elements)
    except TypeError:
        if len(elements) == 0:
            return 0
        cgcd = elements[0]; i = 1
        while i < len(elements) and cgcd != 1:
            cgcd = cgcd.gcd(elements[i])
            i += 1
        return cgcd

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

        We now proceed to write several tests guaranteeing the correct behavior of several methods
        related with polynomial elements that must still work in the framework of d-extensions::

            sage: from dalgebra import *
            sage: B = DifferenceRing(DifferentialRing(QQ))
            sage: Q.<x,y,z> = DExtension(B, [[1, 'x+1'],[0,'y'],['z','y*z']]) # y = e, z = e^x
    '''
    def __init__(self, parent : Parent, x):
        x = x.dict() if hasattr(x, "dict") else x
        super().__init__(parent, x)
        ## reducing coefficients
        for coeff in self.coefficients():
            if hasattr(coeff, "reduce"):
                try:
                    coeff.reduce()
                except: pass

    #######################################################################################
    ### METHODS OF DRINGS THAT APPEAR IN MPOLYNOMIAL_POLYDICT
    #######################################################################################
    def derivative(self, derivation: int = None, times: int = 1) -> DExtension_element:
        return DRings.ElementMethods.derivative(self, derivation, times)
    
    #######################################################################################
    ### Special getter methods (need changes from MPolynomial_Polydict)
    #######################################################################################
    def leading_coefficient(self):
        return self.lc()
    
    def lt(self):
        r'''Get the leading term of the polynomial'''
        return self.parent().element_class(self.parent(), super().lt().dict())

    # #######################################################################################
    # ### Methods specific for DExtension_element
    # #######################################################################################
    def polynomial(self, var):
        r'''
            Overriding method :func:`~sage.rings.polynomial.multi_polynomial.MPolynomial.polynomial`.

            It preserves the d-structure of the polynomial, meaning that if ``var`` can not be removed
            from the ring, this method will raise an error (see :func:`~.dextension_parent.DExtension_parent.remove_var`)
        '''
        return self.parent().univariate_ring(var)(str(self))
    
    def content(self):
        return self.parent().base()(_GCD(*self.coefficients()))
        
    def monic(self):
        r'''
            Return the monic equivalent of ``self``, i.e., with leading coefficient 1.

            This method just divides by the leading coefficient of ``self``. This means that 
            when several variables appear, the higer `lc` is computed using "degrevlex" as a
            term ordering.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = 3*x^3 + x^2 + x + 5
                sage: p.monic()
                x^3 + 1/3*x^2 + 1/3*x + 5/3
                sage: p.monic().parent()
                DExtension(Differential Ring [[Rational Field], (0,)], [x -> (1,)]
                sage: R.<x,y> = DExtension(B, [[1], ['y']]) # (Q[x,e^x], dx)
                sage: p = 3*x^3*y + 7*x^2*y^4 + x*y + 5
                sage: p.monic()
                x^2*y^4 + 3/7*x^3*y + 1/7*x*y + 5/7
                sage: p.monic().parent()
                DExtension(Differential Ring [[Rational Field], (0,)], [x -> (1,),y -> (y,)]
                sage: p.polynomial(x).monic() # now we fix `x` as main variable
                x^3 + 7/3*y^3*x^2 + 1/3*x + 5/(3*y)
                sage: p.polynomial(x).monic().parent()
                DExtension(Fraction Field of DExtension(Differential Ring [[Rational Field], (0,)], [y -> (y,)], [x -> (1,)]
        '''
        return (1/self.lc())*self
    
    def quo_rem(self, right):
        r'''
            Method for Euclidean division on univariate polynomials.

            Method implemented to avoid errors when converting to singular.
            
            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = 3*x^3 + x^2 + x + 5
                sage: q = 5*x^2 - 3*x + 1
                sage: p.quo_rem(q)
                (3/5*x + 14/25, 52/25*x + 111/25)

            After implementing this method, the Euclidean algorithm for GCD is automatically included::

                sage: p = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: q = x^3 + x^2 - 4*x - 4
        '''
        ## Casting ``right`` to the same parent
        right = self.parent()(str(right))
        # try:
        #     right = self.parent()(right)
        # except: ## TODO: Using the str casting for now. In the future this should not be necessary
        #     right = self.parent()(str(right))

        ## Checking arguments are of correct type
        if self.parent().ngens() > 1: # if multiple variable we fall back to default implementation
            try:
                return super().quo_rem(right)
            except: # Falling back to a basic quo remainder
                logger.warning(f"[Quo-Rem] Falling to basic quo_rem implementation")
                # Trying a simple reduction using the idea from Gröbner basis
                Q = 0; R = self; b = right
                lt_R = R.lt(); lt_b = b.lt(); to_Q = lt_R//lt_b
                while to_Q != 0:
                    Q += to_Q
                    R -= to_Q*right
                    lt_R = R.lt(); to_Q = lt_R // lt_b

                return (Q,R)
        
        ## Running the Euclidean algorithm
        x = self.parent().gens()[0] # getting the variable
        Q = 0; R = self; d = R.degree() - right.degree()
        while R != 0 and d >= 0:
            T = R.lc()/right.lc()*x**d
            Q += T
            R -= right*T
            d = R.degree() - right.degree()
        return (Q, R)

    def pseudo_quo_rem(self,right):
        r'''
            Method for Euclidean division on univariate polynomials.

            Method implemented since in multivariate polynomials is not included.

            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)
        
            EXAMPLES::

                from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = 3*x^3 + x^2 + x + 5
                sage: q = 5*x^2 - 3*x + 1
                sage: p.pseudo_quo_rem(q)
                (15*x + 14, 52*x + 111)
        '''
        ## Checking arguments are of correct type
        if self.parent().ngens() > 1: # if multiple variable we fall back to default implementation
            ## TODO: implement something for multiple variables
            return super().quo_rem(right)
        
        ## Casting ``right`` to the same parent
        right = self.parent()(str(right))
        # try:
        #     right = self.parent()(right)
        # except: ## TODO: Using the str casting for now. In the future this should not be necessary
        #     right = self.parent()(str(right))
        ## Running the Euclidean pseudo-division
        x = self.parent().gens()[0] # getting the variable
        b = right.lc(); N = self.degree() - right.degree() + 1; Q = 0; R = self
        d = R.degree() - right.degree()
        while R != 0 and d >= 0:
            T = R.lc() * x**d
            N -= 1
            Q = b*Q + T
            R = b*R - T*right
            d = R.degree() - right.degree()

        b_pow_N = b**N
        return (b_pow_N*Q, b_pow_N*R)

    def xgcd_half(self, right):
        r'''
            Method for computing half the Extended GCD algorithm.

            This method takes `p` from ``self`` receives a polynomial `q` in ``other`` and computes 
            two polynomials `s, g` such that `g = gcd(p,q)` and `sp \eqiv g (mod q)`.

            This can be used later for obtaining the extended version of the GCD Euclidean algorithm
            (see :func_`xgcd` for further information).

            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: q = x^3 + x^2 - 4*x - 4
                sage: p.xgcd_half(q)
                ((-1/5)*x + 3/5, x + 1)
        '''
        if self.parent().ngens() > 1:
            ## TODO: implement something for multiple variables
            raise NotImplementedError(f"Extended GCD for multivariate polynomials not implemented")
        right = self.parent()(str(right))

        a = self; b = right
        a1 = self.parent().one(); b1 = self.parent().zero()
        while b != 0:
            logger.debug(f"[xgcd_half] Starting iteration: {a=}, {b=}, {a1=}, {b1=}")
            (q,r) = a.quo_rem(b)
            a,b = b,r
            a1, b1 = b1, a1-q*b1
        
        logger.debug(f"[xgcd_half] Finished loop: {a=}, {a1=}")
        # we return the monic gcd, just as a default behavior
        lc = a.lc()
        a1 = (1/lc)*a1; a = a.monic() 
        return (a1,a)
        
    def xgcd(self, right):
        r'''
            Method for extended GCD implementation using Euclidean division.

            This method takes `p` (``self``) and `q` (``other``) and finds the corresponding polynomials
            `s,t,g` such that `sp + tq = g` where `g` is the GCD of `p` and `q`.

            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: q = x^3 + x^2 - 4*x - 4
                sage: p.xgcd(q)
                ((-1/5)*x + 3/5, (1/5)*x^2 + (-6/5)*x + 2, x + 1)
        '''
        if self.parent().ngens() > 1:
            ## TODO: implement something for multiple variables
            raise NotImplementedError(f"Extended GCD for multivariate polynomials not implemented")
        right = self.parent()(str(right))

        a = self; b = right
        s,g = a.xgcd_half(b)
        t,r = (g-s*a).quo_rem(b) # here r must be 0
        assert r == 0
        return (s,t,g)
    
    def diophantine_half(self, right, sol):
        r'''
            Method to compute with Euclidean division the diophantine solution to the equation

            .. MATH::

                sp + tq = c

            where `p` is ``self``, `q` is given by ``right`` and `c` is given by ``sol``.
            This method returns the "half" version of it, returning just the value for `s` where the degree of `s` 
            is bounded by the degree of `q`.

            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: q = x^3 + x^2 - 4*x - 4
                sage: c = x^2 - 1
                sage: p.diophantine_half(q, c)
                (-1/5)*x^2 + 4/5*x - 3/5
        '''
        if self.parent().ngens() > 1:
            ## TODO: implement something for multiple variables
            raise NotImplementedError(f"Extended GCD for multivariate polynomials not implemented")
        right = self.parent()(str(right))
        sol = self.parent()(str(sol))

        a,b,c = self, right, sol
        s,g = a.xgcd_half(b)
        q,r = c.quo_rem(g)
        if r != 0:
            raise ValueError(f"The diophantine equation has no solution ({c} not generated by {g})")
        s = q*s
        if s != 0 and s.degree() > b.degree():
            _,s = s.quo_rem(b)
        return s
        
    def diophantine(self, right, sol):
        r'''
            Method to compute with Euclidean division the diophantine solution to the equation

            .. MATH::

                sp + tq = c

            where `p` is ``self``, `q` is given by ``right`` and `c` is given by ``sol``.
            This method returns the particular solution `(s,t)` where the degree of `s` 
            is bounded by the degree of `q`.

            Algorithm taken from Brontein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: p = x^4 - 2*x^3 - 6*x^2 + 12*x + 15
                sage: q = x^3 + x^2 - 4*x - 4
                sage: c = x^2 - 1
                sage: p.diophantine(q, c)
                ((-1/5)*x^2 + 4/5*x - 3/5), 1/5*x^3 + (-7/5)*x^2 + 16/5*x - 2)
        '''
        if self.parent().ngens() > 1:
            ## TODO: implement something for multiple variables
            raise NotImplementedError(f"Extended GCD for multivariate polynomials not implemented")
        right = self.parent()(str(right))
        sol = self.parent()(str(sol))

        a,b,c = self,right,sol
        s = a.diophantine_half(b,c)
        t,r = (c-s*a).quo_rem(b) # here r must be 0
        assert r == 0
        return (s,t)





__all__ = []