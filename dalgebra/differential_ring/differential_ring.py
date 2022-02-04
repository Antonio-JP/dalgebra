r"""
Module containing the basic definitions for differential rings.

This file contains the definition of the category :class:`DifferentialRings`
that will contain all the differential structures and will help in the 
coercion and dynamic class system of Sage.

This module also includes a factory :class:`DifferentialRingFactory` that will 
help in the creation of differential structures from other Sage structures, 
adding to them the corresponding category and unifying the derivation method to the 
standards of an element in :class:`DifferentialRings`.

The main structure to achieve this is a wrapper class :class:`DifferentialRing_Wrapper`
that includes the functionality of the wrapped structure and adds the differential methods
defined in the category.

EXAMPLES::

    TODO

AUTHORS:

    - Antonio Jimenez-Pastor (2022-02-02): initial version
"""

# ****************************************************************************
#  Copyright (C) 2022 Antonio Jimenez-Pastor <jimenezpastor@lix.polytechnique.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from sage.all import CommutativeRing, ZZ, latex
from sage.categories.all import Category, CommutativeRings
from sage.misc.abstract_method import abstract_method
from sage.structure.element import Element #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)

class DifferentialRings(Category):
    # methods of the category itself
    def super_categories(self):
        return [_CommutativeRings]

    # methods that all differential structures must implement
    class ParentMethods:
        @abstract_method
        def derivation(self, element):
            pass

    # methods that all differential elements must implement
    class ElementMethods:
        def derivative(self, times=1):
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self._derivative()
            else:
                return self.derivative(times=times-1).derivative()

        @abstract_method
        def _derivative(self, *_):
            r'''
                Method that actually computes the derivative of an element of a differential ring.
            '''
            raise NotImplementedError

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class DifferentialRingFactory(UniqueFactory):
    pass

DifferentialRing = DifferentialRingFactory("dalgebra.differential_ring.differential_ring.DifferentialRing")

class DifferentialRing_ElementWrapper(Element):
    def __init__(self, parent, element):
        if(not isinstance(parent, DifferentialRing_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        Element.__init__(self, parent=parent)
        self.__element = element

    @property
    def element(self): return self.__element

    def __getattribute__(self, name: str):
        if(name in ("element", "__element", "_derivative", "_add_","_sub_","_mul_","_rmul_","_lmul","__pow__")):
            return Element.__getattribute__(self,name)
        try:
            return getattr(self.element, name)
        except AttributeError:
            return Element.__getattribute__(self, name)

    # Arithmetic methods
    def _add_(self, x):
        return self.parent().element_class(self.parent(), self.element + x.element)
    def _sub_(self, x):
        return self.parent().element_class(self.parent(), self.element - x.element)
    def _mul_(self, x):
        return self.parent().element_class(self.parent(), self.element * x.element)
    def _rmul_(self, x):
        return self.parent().element_class(self.parent(), self.element * x.element)
    def _lmul_(self, x):
        return self.parent().element_class(self.parent(), self.element * x.element)
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), self.element ** n)

    def _derivative(self, *_):
        r'''
            Overridden method to implement properly the derivation in Fraction Field

            This method simply calls the method :func:`derivative`. See its documentation
            for further information on the input, output and examples.
        '''
        return self.parent().derivation(self)

class DifferentialRing_Wrapper(CommutativeRing):
    r'''
        Wrapper class for create differential rings.

        This class allows the user to add the differential functionality to algebraic structures 
        in Sage to be used in other places in the package :mod:`dalgebra`.

        Let `R` be a ring. We say that `\partial: R \rightarrow R` is a derivation on `R` if it satisfies
        the following two properties:
            * Is a group homomorphism w.r.t. `+`: `\partial(a+b) = \partial(a) + \partial(b)`.
            * Satisfies the Leibniz rule: `\partial(ab) = \partial(a)b + a\partial(b)`.

        The pair `(R, \partial)` is denoted as a differential ring. This structure can also be defined 
        in a similar way for fields, modules and other algebraic structures.

        This class allows to create these differential structures preserving the operations on the previous
        elements and adding the extra layer of differential operations that all differential structures may have.

        INPUT:

            * ``ring``: a commutative ring in Sage to be transformed into a differential ring
            * ``derivation``: a morphism or method from the ``ring`` to itself that satisfies 
              the derivation properties.

        OUTPUT:

        The wrapped differential structure. See the category :class:`DifferentialRings` for further information.

        EXAMPLES::

            TODO
    '''
    Element = DifferentialRing_ElementWrapper

    def __init__(self, ring, derivation, category=None):
        self.__base = ring
        self.__derivation = derivation
        categories = [DifferentialRings(), ring.category()]
        if(isinstance(category, (list, tuple))):
            categories += list(category)
        elif(category != None): 
            categories.append(category) 
        CommutativeRing.__init__(self, ring.base(), category=tuple(categories))

    @property
    def wrapped(self): return self.__base
    @property
    def d(self): return self.__derivation

    ## Methods for Parent from DifferentialRings
    def derivation(self, element):
        if(not element in self):
            raise TypeError("The element [%s] can not be differentiated as element of [%s]" %(element, self))
        return self.d(element)

    ## Coercion methods
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))

    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into a :class:`~dalgebra.differential_polynomial.differential_polynomial_element.DiffPolynomial`.
        '''
        p = self.wrapped._element_constructor_(x)
        return self.element_class(self, p)

    def __call__(self, *args, **kwds):
        try:
            res = self.wrapped(*args, **kwds)
            return self.element_class(self, res)
        except:
            super().__call__(*args, **kwds)

    def __contains__(self, element):
        if(isinstance(element.parent(), DifferentialRing_Wrapper)):
            return element.parent() == self
        return element in self.wrapped        

    ## Representation methods
    def __repr__(self) -> str:
        return f"Diff. Ring [{self.wrapped}] with derivative [{self.d}]"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        return r"\left(" + latex(self.wrapped) + ", " + latex(self.d) + r"\right)"

    ## Element generation
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.zero()
                0
        '''
        return self(0)
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a randome element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        p = self.wrapped.random_element(*args,**kwds)
        return self(p)

    