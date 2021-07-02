r"""
File for the structure of a Differential Ring

This file contains the main structure and methods require for a Differential Ring.

Let `R` be a commutative ring. We say that `\partial: R \rightarrow R` is a derivation 
on `R` if it satisfies the following two properties:

* Addition homomorphism: for all `r,s \in R`, `\partial(r+s) = \partial(r) + \partial(s)`.
* Leibniz rule: for all `r, s \in R`, `\partial(rs) = \partial(r)s + r\partial(s)`.

The set of all derivations over `R` form a left `R`-module. But here we are interested
in the case of the pair `(R,\partial)` (i.e., we fix a derivation). We say that this pair
is a differential ring.

In terms of implementation, this class is a conceptual way of packing together a ring 
structure with its corresponding derivation. Hence, all the elements of the ring will
have a method ``derivative`` that will compute the corresponding derivative. This class
is also built such that if `r \in R`, then the call ``diff(r)`` using the Sage command
:func:`diff` computes the element `\partial(r)`.

EXAMPLES::

    sage: from dalgebra import DifferentialRing
    sage: R = DifferentialRing(QQ['x'], lambda p: p.derivative(x))
    sage: R
    Differential Ring (Univariate Polynomial Ring in x over Rational Field, ...) 

AUTHORS:

    - Antonio Jimenez-Pastor (2021-07-02): initial version

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

from sage.categories.all import Morphism, CommutativeRings
from sage.misc.classcall_metaclass import ClasscallMetaclass # pylint: disable=no-name-in-module
from sage.rings.ring import CommutativeRing

_CommutativeRings = Rings.__classcall__(CommutativeRings)

class DifferentialRing (CommutativeRing, metaclass=ClasscallMetaclass):
    r'''
        Class for representing a Differential Ring.

        This class represents the pair `(R,\partial)` there `R` is a commutative ring and
        `\partial` is a derivation over `R`. This class does not check whether the method
        provided is indeed a derivation. That is left to the user.

        This class offers different method to compute the derivative of its elements 
        and to build special rings, such as the ring of differential polynomials 
        with coefficients in `R` (see :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing`).

        Otherwise, this class offers the same methods for a ring as the original structure 
        over it is based.

        INPUT:

        * ``base``: the ring object for the ring `R`.
        * ``derivation``: a :class:`~sage.categories.all.Morphism` from `R` to itself that satisfies 
          the Leibniz rule.

        EXAMPLES::

            sage: from dalgebra import DifferentialRing
            sage: R = DifferentialRing(QQ['x'], lambda p: p.derivative(x))
            sage: R
            Differential Ring (Univariate Polynomial Ring in x over Rational Field, ...) 
    '''
    def __init__(self, base, derivation):
        ## We initialize first the same structure as in base
        base.__class__.__init__(self)

        if(not isinstance(derivation, Morphism)):
            raise TypeError("The derivation must be a morphism")
        if(derivation.domain() != base):
            raise TypeError("The domain of the derivation must be the base ring")
        if(derivation.codomain() != base):
            raise TypeError("The codomain of the derivation must be the base ring")

        self.__base = base
        self.__derivation = derivation

    def derivative(self, element, times=1):
        r'''
            Method to compute the derivation of an element of ``self``

            This method applied the derivation `\partial` that defines the 
            differential ring to an element of ``self`` and arbitrary number of times.

            INPUT:

            * ``element``: the element (must be in ``self``) to differentiate.
            * ``times``: optional argument indicating how many derivatives to compute.
        '''
        if((not times in ZZ) or (times <= 0)): raise ValueError("The argument 'times' must be a positive integer")

        element = self(element) # casting the element to this ring

        if(times > 1): return self.derivative(self.derivative(element, times-1))
        else: # the base case when we compute one derivative
            return self(self.__derivation(self.__base(element)))

    
