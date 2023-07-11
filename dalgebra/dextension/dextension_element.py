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

from sage.all import Parent, prod, ZZ
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
        and extending each `\sigma \in \Delta` by setting a value for `t` in `R[t]`. We can do the same for several variables
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
    ### METHODS OF D-RINGS THAT APPEAR IN MPOLYNOMIAL_POLYDICT
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
    def polynomial(self, var) -> DExtension_element:
        r'''
            Overriding method :func:`~sage.rings.polynomial.multi_polynomial.MPolynomial.polynomial`.

            It preserves the d-structure of the polynomial, meaning that if ``var`` can not be removed
            from the ring, this method will raise an error (see :func:`~.dextension_parent.DExtension_parent.remove_var`)
        '''
        return self.parent().univariate_ring(var)(str(self))
    
    # def content(self): TODO: remove this method
    #     return self.parent().base()(_GCD(*self.coefficients()))
        
    def monic(self) -> DExtension_element:
        r'''
            Return the monic equivalent of ``self``, i.e., with leading coefficient 1.

            This method just divides by the leading coefficient of ``self``. This means that 
            when several variables appear, the higher `lc` is computed using "degrevlex" as a
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
    
    def primitive(self) -> DExtension_element:
        return self//self.content()

    def quo_rem(self, right) -> tuple[DExtension_element,DExtension_element]:
        r'''
            Method for Euclidean division on univariate polynomials.

            Method implemented to avoid errors when converting to singular.
            
            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

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
        right = self.parent()(str(right)) if not right in self.parent() else right
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
                Q = self.parent().zero(); R = self; b = right
                lt_R = R.lt(); lt_b = b.lt(); to_Q = lt_R//lt_b
                while to_Q != 0:
                    Q += to_Q
                    R -= to_Q*right
                    lt_R = R.lt(); to_Q = lt_R // lt_b

                return (Q,R)
        
        ## Running the Euclidean algorithm
        x = self.parent().gens()[0] # getting the variable
        Q = self.parent().zero(); R = self; d = R.degree() - right.degree()
        while R != 0 and d >= 0:
            T = R.lc()/right.lc()*x**d
            Q += T
            R -= right*T
            d = R.degree() - right.degree()
        return (Q, R)

    def pseudo_quo_rem(self,right) -> tuple[DExtension_element,DExtension_element]:
        r'''
            Method for Euclidean division on univariate polynomials.

            Method implemented since in multivariate polynomials is not included.

            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)
        
            EXAMPLES::

                sage: from dalgebra import *
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
        
        if right.is_zero():
            raise ZeroDivisionError("Pseudo-division by zero is not possible")
        
        ## Casting ``right`` to the same parent
        right = self.parent()(str(right)) if not right in self.parent() else right
        # try:
        #     right = self.parent()(right)
        # except: ## TODO: Using the str casting for now. In the future this should not be necessary
        #     right = self.parent()(str(right))

        ## Running the Euclidean pseudo-division
        x = self.parent().gens()[0] # getting the variable
        b = right.lc(); N = self.degree() - right.degree() + 1; Q = self.parent().zero(); R = self
        d = R.degree() - right.degree()
        while R != 0 and d >= 0:
            T = R.lc() * x**d
            N -= 1
            Q = b*Q + T
            R = b*R - T*right
            d = R.degree() - right.degree()

        b_pow_N = b**N
        return (b_pow_N*Q, b_pow_N*R)

    def xgcd_half(self, right) -> tuple[DExtension_element,DExtension_element]:
        r'''
            Method for computing half the Extended GCD algorithm.

            This method takes `p` from ``self`` receives a polynomial `q` in ``other`` and computes 
            two polynomials `s, g` such that `g = gcd(p,q)` and `sp \equiv g (mod q)`.

            This can be used later for obtaining the extended version of the GCD Euclidean algorithm
            (see :func_`xgcd` for further information).

            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

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
        right = self.parent()(str(right)) if not right in self.parent() else right

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
        
    def xgcd(self, right) -> tuple[DExtension_element,DExtension_element,DExtension_element]:
        r'''
            Method for extended GCD implementation using Euclidean division.

            This method takes `p` (``self``) and `q` (``other``) and finds the corresponding polynomials
            `s,t,g` such that `sp + tq = g` where `g` is the GCD of `p` and `q`.

            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

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
        right = self.parent()(str(right)) if not right in self.parent() else right

        a = self; b = right
        s,g = a.xgcd_half(b)
        t,r = (g-s*a).quo_rem(b) # here r must be 0
        assert r == 0
        return (s,t,g)
    
    def diophantine_half(self, right, sol) -> DExtension_element:
        r'''
            Method to compute with Euclidean division the diophantine solution to the equation

            .. MATH::

                sp + tq = c

            where `p` is ``self``, `q` is given by ``right`` and `c` is given by ``sol``.
            This method returns the "half" version of it, returning just the value for `s` where the degree of `s` 
            is bounded by the degree of `q`.

            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

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
        right = self.parent()(str(right)) if not right in self.parent() else right
        sol = self.parent()(str(sol)) if not sol in self.parent() else sol

        a,b,c = self, right, sol
        s,g = a.xgcd_half(b)
        q,r = c.quo_rem(g)
        if r != 0:
            raise ValueError(f"The diophantine equation has no solution ({c} not generated by {g})")
        s = q*s
        if s != 0 and s.degree() > b.degree():
            _,s = s.quo_rem(b)
        return s
        
    def diophantine(self, right, sol) -> tuple[DExtension_element,DExtension_element]:
        r'''
            Method to compute with Euclidean division the diophantine solution to the equation

            .. MATH::

                sp + tq = c

            where `p` is ``self``, `q` is given by ``right`` and `c` is given by ``sol``.
            This method returns the particular solution `(s,t)` where the degree of `s` 
            is bounded by the degree of `q`.

            Algorithm taken from Bronstein's book "Symbolic integration I: Transcendental Functions" (Chapter 1)

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
        right = self.parent()(str(right)) if not right in self.parent() else right
        sol = self.parent()(str(sol)) if not sol in self.parent() else sol

        a,b,c = self,right,sol
        s = a.diophantine_half(b,c)
        t,r = (c-s*a).quo_rem(b) # here r must be 0
        assert r == 0
        return (s,t)

    def partial_fraction(self, *factors, _check_coprime=True) -> tuple[DExtension_element, tuple[DExtension_element,...]]:
        r'''
            Method for computing a partial fraction decomposition for a polynomial

            This method is currently implemented for 1 variable. Consider using method :func:`polynomial` 
            to reduce the polynomial to one variable before calling this method.

            This method can be called in two different ways: 

            * ``factors`` are tuples `(d, e)` and we will consider the full partial fraction decomposition.
            * ``factors`` are simply elements `d`. We will consider the non-full partial fraction decomposition.

            The non-full approach will consider a set of factors `d_1,\ldots, d_n` that are pairwise co-prime 
            (check method :func:`gcd` and argument ``_check_coprime``) and will compute a set of coefficients 
            `a_0,\ldots, a_n` such that

            .. MATH::

                \frac{self}{d_1 \cdots d_n} = a_0 + \sum_{i=1}^n \frac{a_i}{d_i},

            where `\deg(a_i) < \deg(d_i)`.

            The full partial fraction decomposition work similar, but consider powers of the factors of the 
            denominator. Namely, if we provide co-prime factors `d_1,\ldots,d_n` and corresponding exponents 
            `e_1,\ldots,e_n`, this method will produce a set of elements `a_0` and `a_{i,j}` for `i = 1,\ldots,n` 
            and `j = 1,\ldots, e_i` such that:

            .. MATH::
            
                \frac{self}{d_1^{e_1}\cdots c_n^{e_n}} = a_0 + \sum_{i=1}^n \sum_{j=1}^e_i \frac{a_{i,j}}{d_i^j}

            To comply for both ways of implementing this method, we always return a tuple with `n+1` element. The first
            element will be the value for `a_0`. Then the `i`-th element will be a tuple of length `e_i` (length 1 if 
            using the non-full approach).

            INPUT:

            * ``factors``: a list of elements or tuples (`d_i` or `(d_i, e_i)`) for the different factors of the denominator.
            * ``_check_coprime``: (optional - ``True``) we check whether the factors are coprime or not.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: a = x^2 + 3*x
                sage: a.partial_fraction(x+1, x^2-2*x+1)
                (0, (-1/2,), (3/2*x + 1/2,))
                sage: a.partial_fraction(x+1, (x-1,2))
                (0, (-1/2,), (3/2, 2))

            TODO: add examples from Bronstein's book
        '''
        if not self.parent().ngens() == 1:
            raise NotImplementedError(f"Partial fraction decomposition not implemented for multivariate polynomials")
        
        ## Processing the input
        final_input = []
        for factor in factors:
            if isinstance(factor, (tuple, list)):
                if len(factor) != 2:
                    raise TypeError(f"[PFD] Incorrect format for PFD. We allow tuples of 2 elements, got {factor}")
                final_input.append((self.parent()(str(factor[0])), ZZ(factor[1])))
                if final_input[-1][-1] <= 0:
                    raise ValueError(f"[PFD] Got a negative exponent for one factor. Only positive exponents are allowed.")
            else:
                final_input.append((self.parent()(str(factor)), 1))
        
        if _check_coprime:
            for i in range(len(final_input)):
                for j in range(i+1, len(final_input)):
                    if final_input[i][0].gcd(final_input[j][0]) != 1:
                        raise ValueError(f"[PFD] Factors {final_input[i][0]} and {final_input[j][0]} are not co-prime")

        if len(final_input) == 0: # checking error in input (no input)
            raise TypeError(f"[PFD] No factors given for partial fraction decomposition")

        if all(factor[1] == 1 for factor in final_input): # non-full approach
            prod_from2 : DExtension_element = prod((factor[0] for factor in final_input[1:]), z=self.parent().one())
            full_prod : DExtension_element = final_input[0][0] * prod_from2
            a0, r = self.quo_rem(full_prod)
            if len(factors) == 1:
                return tuple([a0, tuple([r])])
            else:
                a1, t = prod_from2.diophantine(final_input[0][0], r)
                partial_decomposition = t.partial_fraction(*final_input[1:], _check_coprime=False)
                b = partial_decomposition[0]; others = partial_decomposition[1:]
                return tuple([a0+b, tuple([a1]), *others])
        else:
            non_full_decomposition = self.partial_fraction(*[factor[0]**factor[1] for factor in final_input], _check_coprime=False)
            output = [non_full_decomposition[0]]
            for i,factor in enumerate(final_input):
                a_i = non_full_decomposition[i+1][0]
                new_a_i = []
                for j in range(factor[1], 0, -1):
                    a_i, to_add = a_i.quo_rem(factor[0])
                    new_a_i.insert(0, to_add)
                output.append(tuple(new_a_i))
            return tuple(output)
            
    def partial(self, variable=None):
        r'''Computes the partial derivative w.r.t. the given variable'''
        if variable is None and self.parent().ngens() > 1:
            raise ValueError(f"Required variable to compute the partial derivative (more than 1 generator)")
        elif variable is None:
            ind = 0
        else:
            variable = self.parent()(str(variable))
            if not variable in self.parent().gens():
                raise ValueError(f"The given variable ({variable}) is not a generator of {self.parent()}")
            ind = self.parent().gens().index(variable)

        new_dict = {}
        for k,v in self.dict().items():
            if k[ind] > 0:
                k = list(k); k[ind]-=1; k = tuple(k)
                new_dict[k] = (k[ind]+1)*v
        return self.parent().element_class(self.parent(), new_dict)
    
    def kappa(self, operation=None):
        r'''Compute the `\kappa` operation over an element. This is define by applying the operation over the coefficients.'''
        if operation is None and self.parent().noperators() > 1:
            raise ValueError(f"Required operation to compute the kappa operation (more than 1 operation)")
        elif operation is None:
            operation = 0
        else:
            operation = ZZ(operation)
            if operation < 0:
                raise IndexError("Incorrect index for operation: negative index")
            elif operation >= self.parent().noperators():
                raise IndexError("Incorrect index for operation: index too big")
            
        return self.parent().element_class(self.parent(), {k:v.operation(operation) for (k,v) in self.dict() if not v.is_constant(operation)})
        
    def squarefree(self, *, _algorithm="musser"):
        r'''
            Method to compute a squarefree factorization of ``self``.

            This method only works for univariate polynomials.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, [[1]]) # (Q[x], dx)
                sage: A = x^8 + 6*x^6 + 12*x^4 + 8*x^2
                sage: A.squarefree()
                ((1, 1), (x, 2), (x^2 + 2, 3))
                sage: prod(factor**exp for (factor,exp) in A.squarefree()) == A
                True
                sage: A.squarefree(_algorithm="yun")
                ((1, 1), (x, 2), (x^2 + 2, 3))
                sage: 
        '''
        if self.parent().ngens() > 1:
            raise TypeError(f"Squarefree factorization only implemented for univariate polynomials")
        
        if _algorithm == "musser":
            c = self.content(); S = self//c
            S_ = S.gcd(S.partial())
            S_star = S//S_
            A = []

            while S_.degree() > 0:
                Y = S_star.gcd(S_)
                A.append(S_star//Y)
                S_star, S_ = Y, S_//Y

            A.append(S_star)
            A[0]*=c*S_
            return tuple([(factor, exp+1) for exp,factor in enumerate(A)])
        elif _algorithm == "yun":
            c = self.content(); S = self//c
            S_x = S.partial(); S_ = S.gcd(S_x); S_star = S//S_; Y = S_x//S_
            A = []
            Z = Y - S_star.partial()
            while Z != 0:
                A.append(S_star.gcd(Z))
                S_star, Y = S_star//A[-1], Z//A[-1]
                Z = Y - S_star.partial()
            A.append(S_star)
            A[0] *= c
            return tuple([(factor, exp+1) for exp,factor in enumerate(A)])
        else:
            raise NotImplementedError(f"[Squarefree] algorithm '{_algorithm}' not implemented for squarefree decomposition")
        
    def squarefree_decomposition(self):
        return self.squarefree()
    
    def subresultants(self, other, variable=None):
        r'''
            Return the nonzero subresultant polynomials of "self" and "other".

            INPUT:

            * "other" -- a polynomial

            OUTPUT: a list of polynomials in the same ring as "self"

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: R.<x,y> = DExtension(B, [1, 'y'])
                sage: p = (y^2 + 6)*(x - 1) - y*(x^2 + 1)
                sage: q = (x^2 + 6)*(y - 1) - x*(y^2 + 1)
                sage: p.subresultants(q, y)
                [2*x^6 + (-22)*x^5 + 102*x^4 + (-274)*x^3 + 488*x^2 + (-552)*x + 288,
                -x^3 - x^2*y + 6*x^2 + 5*x*y + (-11)*x + (-6)*y + 6]
                sage: p.subresultants(q, x)
                [2*y^6 + (-22)*y^5 + 102*y^4 + (-274)*y^3 + 488*y^2 + (-552)*y + 288,
                x*y^2 + y^3 + (-5)*x*y + (-6)*y^2 + 6*x + 11*y - 6]
                sage: Q.<x> = DExtension(B, 1)
                sage: f = x^8 + x^6 -3*x^4 -3*x^3 +8*x^2 +2*x -5
                sage: g = 3*x^6 +5*x^4 -4*x^2 -9*x +21
                sage: f.subresultants(g)
                [260708,
                9326*x - 12300,
                169*x^2 + 325*x - 637,
                65*x^2 + 125*x - 245,
                25*x^4 + (-5)*x^2 + 15,
                15*x^4 + (-3)*x^2 + 9]

            This example is taken from Example 1.5.1 from Brontein's book::

                sage: A = x^2 + 1; B = x^2 - 1
                sage: A.subresultants(B)
                [4, -2]

            ALGORITHM: 

            Took directly from :func:`sage.rings.polynomial.polynomial_element.subresultant`
            for the univariate case to avoid an infinite recursion on the DExtension 
            structure.
        '''
        R = self.parent()
        if variable is None:
            x = R.gen(0)
        else:
            x = variable
        if not x in self.parent().gens():
            raise TypeError(f"Required a valid generator of a polynomial ring. Got {x}")
        
        if self.parent().ngens() > 1:
            # Took from MPolynomial_polydict.subresultants
            R = self.parent()
            if variable is None:
                x = R.gen(0)
            else:
                x = variable
            p = self.polynomial(x)
            q = other.polynomial(x)
            return [R(str(f)) for f in  p.subresultants(q)]
        else:
            ## Took from sage.rings.polynomial.polynomial_element.Polynomial.subresultants
            P, Q = self, other
            if P.degree() < Q.degree():
                P, Q = Q, P
            S = []
            s = Q.leading_coefficient()**(P.degree()-Q.degree())
            A = Q
            B = P.pseudo_quo_rem(-Q)[1]
            ring = self.parent()
            while True:
                d = A.degree()
                e = B.degree()
                if B.is_zero():
                    return S
                S : list[DExtension_element] = [ring(B)] + S
                delta = d - e
                if delta > 1:
                    if len(S) > 1:
                        n = S[1].degree() - S[0].degree() - 1
                        if n == 0:
                            C = S[0]
                        else:
                            x = S[0].leading_coefficient()
                            y = S[1].leading_coefficient()
                            a = 1 << (int(n).bit_length()-1)
                            c = x
                            n = n - a
                            while a > 1:
                                a /= 2
                                c = c**2 / y
                            if n >= a:
                                c = c * x / y
                                n = n - a
                        C = c * S[0] / y
                    else:
                        C = B.leading_coefficient()**(delta-1) * B / s**(delta-1)
                    S = [ring(C)] + S
                else:
                    C = B
                if e == 0:
                    return S
                B = A.pseudo_quo_rem(-B)[1] / (s**delta * A.leading_coefficient())
                A = C
                s = A.leading_coefficient()

    def subresultant_prs(self, other, variable=None):
        r'''
            Method to compute the Subresultant Polynomial Remainder Sequence

            This methods computes the Subresultant Polynomial Remainder Sequence (PRS)
            as it is characterized in Bronstein's book, Chapter 1, Section 1.5 and 
            computed with the algorithm in page 24.

            INPUT:

            * "other" -- a polynomial

            OUTPUT: 
            
            A list `(R, PRS)` where `R` is the resultant of ``self`` and ``other`` and 
            `PRS` is a tuple of `k+1` elements where the last is zero and defines the 
            subresultant PRS.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, 1)
                sage: f = x^8 + x^6 -3*x^4 -3*x^3 +8*x^2 +2*x -5
                sage: g = 3*x^6 +5*x^4 -4*x^2 -9*x +21
                sage: f.subresultant_prs(g)
                (-260708,
                 (x^8 + x^6 + (-3)*x^4 + (-3)*x^3 + 8*x^2 + 2*x - 5,
                  3*x^6 + 5*x^4 + (-4)*x^2 + (-9)*x + 21,
                  15*x^4 + (-3)*x^2 + 9,
                  65*x^2 + 125*x - 245,
                  9326*x - 12300,
                  -260708,
                  0))
                sage: A = x^2 + 1; B = x^2 - 1
                sage: A.subresultant_prs(B)
                (4, (x^2 + 1, x^2 - 1, -2, 0))
                sage: T = DExtension(Q, ['t'], names=['t'])
                sage: x,t = T.gens()
                sage: A = 3*t*x^2 - t^3 - 4
                sage: B = x^2 + t^3*x - 9
                sage: A.subresultant_prs(B, x)
                ((-3)*t^10 + (-12)*t^7 + t^6 + (-54)*t^4 + 8*t^3 + 729*t^2 + (-216)*t + 16,
                 (3*x^2*t - t^3 - 4,
                  x^2 + x*t^3 - 9,
                  3*x*t^4 + t^3 + (-27)*t + 4,
                  (-3)*t^10 + (-12)*t^7 + t^6 + (-54)*t^4 + 8*t^3 + 729*t^2 + (-216)*t + 16,
                  0))
                sage: A.subresultant_prs(B, x)[0] == A.resultant(B, x)
                True
        '''
        R = self.parent()
        if variable is None:
            x = R.gen(0)
        else:
            x = variable
        if not x in self.parent().gens():
            raise TypeError(f"Required a valid generator of a polynomial ring. Got {x}")
        
        if self.parent().ngens() > 1:
            R = self.parent()
            if variable is None:
                x = R.gen(0)
            else:
                x = variable
            p = self.polynomial(x)
            q = other.polynomial(x)
            R, PRS = p.subresultant_prs(q)
            return (self.parent()(str(R)), tuple(self.parent()(str(el)) for el in PRS))
        else:
            A = self; B = self.parent()(str(other)) if not other in self.parent() else other
            R = [A, B]
            i = 1; gamma = [None, ZZ(-1)]; delta = [None, A.degree(x)-B.degree(x)]; beta = [None, ZZ((-1))**(delta[1]+1)]
            r = [None]
            while R[i] != 0:
                r.append(R[i].lc())
                logger.info(f"{i} --> gamma: {gamma[i]} | delta: {delta[i]} | beta: {beta[i]}")
                logger.info(f"\t r: {r[i]}")
                _,R_ = R[i-1].pseudo_quo_rem(R[i])
                R.append(R_//beta[i]); i += 1
                gamma.append((-r[i-1])**(delta[i-1])*gamma[i-1]**(1-delta[i-1]))
                delta.append(R[i-1].degree(x) - R[i].degree(x)) 
                beta.append(-r[i-1]*gamma[i]**delta[i])
            k = i-1
            if R[k].degree(x) > 0:
                return (self.parent().zero(), tuple(R))
            elif R[k-1].degree(x) == 1:
                return (R[k], tuple(R))
            s, c = self.parent().one(),self.parent().one()
            for j in range(1,k):
                if (R[j-1].degree(x)%2) and (R[j].degree(x)%2):
                    s = -s
                c = c*(beta[j]//r[j]**(1+delta[j]))**(R[j-1].degree(x))*r[j]**(R[j-1].degree(x) - R[j+1].degree(x))

            return (s*c*R[k]**(R[k-1].degree(x)), tuple(R))

    def hermite_reduce(self, other):
        r'''
            Method to compute the hermite reduction of ``self`` with respect to ``other``.

            This method only work for univariate polynomials and computes two rational functions
            `g, h` such that

            .. MATH::

                \frac{self(x)}{other(x)} = \partial_x g(x) + h(x)

            and `h(x)` has a squarefree denominator.

            It is important to remark that this Hermite reduction do not include the difference 
            or differential structure of the :class:`DExtension_parent` and is another operation
            that only extends the polynomial functionality.

            This methods can be used when considering the derivation `\partial_x` over the rational
            functions to compute an integral.

            This method is based on the "HermiteReduce" algorithm from Bronstein's book on Chapter 2 
            (page 44), which uses the linear version from Mack.

            INPUT:

            * ``other``: the denominator that will be considered.

            OUTPUT:

            A pair of rational functions `g, h` fulfilling the Hermite condition.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ)
                sage: Q.<x> = DExtension(B, 1)
                sage: A = x^7 - 24*x^4 - 4*x^2 + 8*x - 8
                sage: D = x^8 + 6*x^6 + 12*x^4 + 8*x^2
                sage: A.hermite_reduce(D)
                ((3*x^3 + 8*x^2 + 6*x + 4)/(x^5 + 4*x^3 + 4*x), 1/x)
        '''
        if self.parent().ngens() > 1:
            raise NotImplementedError(f"[HR] HermiteReduce not implemented for multivariate polynomials.")
        
        ## Casting other to the parent if necessary
        other = self.parent()(str(other)) if not other in self.parent() else other

        if self.gcd(other) != 1:
            quotient = self/other
            quotient.reduce()
            return quotient.numerator().hermite_reduce(quotient.denominator())
        
        ## Setting notation as in book
        A, D = self, other

        ## Taken from pseudo-code on Bronstein's book
        g = self.parent().zero()
        D_ = D.gcd(D.partial())
        D_star = D//D_
        while D_.degree() > 0:
            D__ = D_.gcd(D_.partial())
            D__star = D_//D__
            B,C = (-D_star*D_.partial()//D_).diophantine(D__star, A)
            A = C - B.partial()*D_star//D__star
            g += B/D_
            D_ = D__
        return g, A/D_star
    
    def rothstein_trager(self, other, variable=None, *, _new_var = "t_a"):
        r'''
            Method to compute the Rothstein-Trager Subresultant PRS.

            Given two polynomials `A(x)` and `D(x)`, we can define, for a new indeterminate `t`
            the following resultant:

            .. MATH::

                R = \text{resultant}_x(D(x), A - t\partial_x(D)).

            It was shown that this resultant contains meaningful information about the 
            rational function defined by `A(x)/D(x)` (see Theorem 2.4.1 on Bronstein's book).

            This method computes this resultant by computing the Subresultant PRS and
            return the whole sequence.
        '''
        R = self.parent()
        if variable is None:
            x = R.gen(0)
        else:
            x = variable
        if not x in self.parent().gens():
            raise TypeError(f"Required a valid generator of a polynomial ring. Got {x}")
        
        ## We add the new variable
        from .dextension_parent import DExtension
        E = DExtension(R, [[0 for _ in range(R.noperators())]], names=[_new_var])
        t = E(_new_var); x = E(str(x))
        A = E(str(self)); D = E(str(other))

        return D.resultant(A - t*D.partial(x), x)

    def rothstein_trager_prs(self, other, variable=None, *, _new_var = "t_a"):
        r'''
            Method to compute the Rothstein-Trager Subresultant PRS.

            Given two polynomials `A(x)` and `D(x)`, we can define, for a new indeterminate `t`
            the following resultant:

            .. MATH::

                R = \text{resultant}_x(D(x), A - t\partial_x(D)).

            It was shown that this resultant contains meaningful information about the 
            rational function defined by `A(x)/D(x)` (see Theorem 2.4.1 on Bronstein's book).

            This method computes this resultant by computing the Subresultant PRS and
            return the whole sequence.
        '''
        R = self.parent()
        if variable is None:
            x = R.gen(0)
        else:
            x = variable
        if not x in self.parent().gens():
            raise TypeError(f"Required a valid generator of a polynomial ring. Got {x}")
        
        ## We add the new variable
        from .dextension_parent import DExtension
        E = DExtension(R, [[0 for _ in range(R.noperators())]], names=[_new_var])
        t = E(_new_var); x = E(str(x))
        A = E(str(self)); D = E(str(other))

        return D.subresultant_prs(A - t*D.partial(x), x)


__all__ = []