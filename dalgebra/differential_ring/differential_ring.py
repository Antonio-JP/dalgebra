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
    Differential Ring (Univariate Polynomial Ring in x over Rational Field) [...]

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

import logging

from sage.all import ZZ, latex
from sage.categories.all import Morphism, CommutativeRings
from sage.misc.classcall_metaclass import ClasscallMetaclass # pylint: disable=no-name-in-module
from sage.rings.ring import CommutativeRing

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)
logger = logging.getLogger(__name__)

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
            Differential Ring (Univariate Polynomial Ring in x over Rational Field) [...]
    '''
    def __init__(self, base, derivation, category=None):
        ## Checking the type of 'base'
        if(not isinstance(base, CommutativeRing)):
            raise TypeError("The base ring for a differential ring must be a Commutative Ring")


        ## We save the two objects for future use
        self.__base = base
        self.__derivation = derivation

        ## We initialize first the same structure as in base
        CommutativeRing.__init__(self, base.base(), category=base.categories())

    def __getattr__(self, attr):
        try:
            return super().__getattr__(attr)
        except AttributeError:
            return getattr(self.__base, attr)

    __CACHED_RINGS = {}
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        r'''
            Special builder for Differential Rings

            This method guarantees the uniqueness of the differential ring
            given a particular function. Remark that this method only
            checks equality of the derivation as a function. This may create
            two different rings for different derivations or, even worse, 
            create two different rings with the same derivation instanciated in 
            different functions.
        '''
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        ## Extracting the input from args and kwds
        if(len(args) == 0):
            base = kwds["base"]; derivation = kwds.get("derivation", None)
        elif(len(args) == 1):
            base = args[0]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            derivation = kwds.get("derivation", None)
        else:
            base = args[0]; derivation = args[1]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            if("derivation" in kwds):
                raise TypeError("Duplicated value for the derivation")   

        ## Checking for existing ring in the Cache
        if(not base in DifferentialRing.__CACHED_RINGS):
            DifferentialRing.__CACHED_RINGS[base] = [] 
        for el in DifferentialRing.__CACHED_RINGS[base]:
            if(el[0] == derivation):
                return el[1]

        ## No cached ring found: we create one
        tmp = DifferentialRing.__new__(cls)
        cls.__init__(tmp, base, derivation)
        DifferentialRing.__CACHED_RINGS[base] += [derivation, tmp]
        return tmp

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

    
    #################################################
    ### Coercion methods
    #################################################
    def __contains__(self, element):
        if(not element in self.__base):
            raise NotImplementedError

    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        return self.__base._has_coerce_map_from(S)
        
    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.

            Need to be implemented to construct the elements inside the differential ring.
        '''
        return self(self.__base(x))

    def construction(self):
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DifferentialRing`, the associated functor class is :class:`DiffRingFunctor`.
            See its documentation for further information.

            TODO: add examples and tests.
        '''
        raise NotImplementedError

    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds):
        res = self.__base(*args, **kwds)
        raise NotImplementedError

    ## Other magic methods   
    def __repr__(self):
        return "Differential Ring (%s) [%s]" %(self.__base, self.__derivation)

    def _latex_(self):
        return r"(" + latex(self._base) + r", \partial)"

    ################################################
    ### Element generation methods
    #################################################
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra.differential_ring import *
                sage: R = DifferentialRing(QQ['x'], lambda p : diff(p))
                sage: R.one()
                1
        '''
        return self(self.__base.one())
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra.differential_ring import *
                sage: R = DifferentialRing(QQ['x'], lambda p : diff(p))
                sage: R.zero()
                0
        '''
        return self(self.__base.zero())
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a randome element in this ring.

            This method creates a random element in the base ring and 
            cast it into an element of ``self``.
        '''
        p = super().random_element(*args,**kwds)
        return self(p)

    