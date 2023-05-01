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

import logging

from sage.all import cached_method, Parent
from sage.categories.all import Morphism, Category
from sage.categories.pushout import ConstructionFunctor
from sage.rings.polynomial.multi_polynomial_libsingular import MPolynomialRing_libsingular #pylint: disable=no-name-in-module
from sage.rings.polynomial.multi_polynomial_ring import MPolynomialRing_base
from sage.rings.ring import Ring #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from typing import Collection

from .dextension_element import DExtension_Element, DExtension_Element_libsingular
from ..dring import AdditiveMap

logger = logging.getLogger(__name__)

## Factories for all structures
class DExtensionFactory(UniqueFactory):
    r'''
        TODO: add documentation
    '''
    def create_key(self, base, *names : str, **kwds):
        raise NotImplementedError("[DExtensionFactory] create_key not implemented")

    def create_object(self, _, key):
        raise NotImplementedError("[DExtensionFactory] create_key not implemented")

DExtension = DExtensionFactory("dalgebra.dextension.dextension_parent.DExtension")

class DExtension_generic(MPolynomialRing_base):
    r'''
        TODO: add documentation
    '''
    Element = DExtension_Element # TODO: add the class for elements

    def _base_category(self) -> Category:
        raise NotImplementedError("[DExtension] _base_category not implemented")

    def _set_categories(self, base : Parent) -> list[Category]: 
        raise NotImplementedError("[DExtension] _set_categories not implemented")

    def __init__(self, base : Parent, names : Collection[str]):
        raise NotImplementedError("[DExtension] __init__ not implemented")

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S: Parent) -> bool:
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension] _has_coerce_map_from not implemented")
        
    def _element_constructor_(self, x) -> DExtension_Element:
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension] _element_constructor_ not implemented")

    def _pushout_(self, other):
        raise NotImplementedError("[DExtension] _pushout_ not implemented")
    
    @cached_method
    def gen(self, i: int = None) -> DExtension_Element:
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension] gen not implemented")
                
    def construction(self) -> DExtensionFunctor:
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension] construction not implemented")
    
    def change_ring(self, R):
        r'''
            TODO: add documentation
        '''
        raise NotImplementedError("[DExtension] change_ring not implemented")

    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        raise NotImplementedError("[DExtension] __repr__ not implemented")

    def _latex_(self):
        raise NotImplementedError("[DExtension] _latex_ not implemented")
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self) -> DExtension_Element:
        r'''
            TODO: add documentation
        '''
        return self(1)
    
    def zero(self) -> DExtension_Element:
        r'''
            TODO: add documentation
        '''
        return self(0)
    
    def random_element(self,
        deg_bound : int = 0,order_bound : int = 0, sparsity : float = 0.75,
        *args,**kwds
    ):
        r'''
            Creates a random element in this ring.

            This method receives a bound for the degree and order of all the variables
            appearing in the ring and also a sparsity measure to avoid dense polynomials.
            Extra arguments are passed to the random method of the base ring.

            INPUT:

            * ``deg_bound``: total degree bound for the resulting polynomial.
            * ``order_bound``: order bound for the resulting polynomial.
            * ``sparsity``: probability of a coefficient to be zero.
        '''
        raise NotImplementedError("[DExtension] random_element not implemented")
      
    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[Morphism]:
        raise NotImplementedError("[DExtension] operators not implemented")

    def operator_types(self) -> tuple[str]:
        raise NotImplementedError("[DExtension] operator_types not implemented")

    def _create_operator(self, operation: int, ttype: str) -> AdditiveMap:
        r'''
            Method to create a map on the ring of polynomials from an operator on the base ring.

            We create an :class:`AdditiveMap` from the given operator assuming the type given in ``ttype``.
            This type will determine how the multiplication behaves with respect to the different variables.
        '''
        operator : AdditiveMap = self.base().operators()[operation] 
        if ttype == "homomorphism":
            raise NotImplementedError("[DExtension] _create_operator - homomorphism not implemented")
        elif ttype == "derivation":
            raise NotImplementedError("[DExtension] _create_operator - derivation not implemented")
        elif ttype == "skew":
            raise NotImplementedError("[DExtension] _create_operator - skew not implemented")
        else:
            raise ValueError(f"The type {ttype} is not recognized as a valid operator.")

        # return AdditiveMap(self, func) 
    
    def linear_operator_ring(self) -> Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the 
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError("[DExtension] __init__ not implemented")

    def inverse_operation(self, element: DExtension_Element, operation: int = 0) -> DExtension_Element:
        if not element in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if self.operator_types()[operation] == "homomorphism":
            return self.__inverse_homomorphism(element, operation)
        elif self.operator_types()[operation] == "derivation":
            return self.__inverse_derivation(element, operation)
        elif self.operator_types()[operation] == "skew":
            return self.__inverse_skew(element, operation)
        else:
            raise NotImplementedError("[inverse_operation] Inverse for unknown operation not implemented")
    
    def __inverse_homomorphism(self, element: DExtension_Element, operation: int):
        raise NotImplementedError("[DExtension] __init__ not implemented")
    
    def __inverse_derivation(self, element: DExtension_Element, operation: int):
        raise NotImplementedError("[DExtension] __init__ not implemented")
   
    def __inverse_skew(self, element: DExtension_Element, operation: int):
        raise NotImplementedError("[DExtension] Skew-derivation operation not yet implemented")
    
def is_DExtension(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, DExtension_generic)

class DExtension_libsingular (DExtension_generic, MPolynomialRing_libsingular):
    r'''
        Implementation of a d-extension using the Singular library
    '''
    Element = DExtension_Element_libsingular

    def __init__(self, *args, **kwds):
        raise NotImplementedError("[DExtension_libsingular] __init__ operation not yet implemented")


class DExtensionFunctor (ConstructionFunctor):
    r'''
        TODO: update documentation

        Class representing Functor for creating :class:`DPolynomialRing_dense`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential 
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DifferentialPolynomialRing_dense`)
    '''
    def __init__(self, variables):
        raise NotImplementedError("[DExtensiongFunctor] __init__ not implemented")
        
    ### Methods to implement        
    def _apply_functor(self, x):
        raise NotImplementedError("[DExtensiongFunctor] _apply_functor not implemented")
        
    def _repr_(self):
        raise NotImplementedError("[DExtensiongFunctor] _repr_ not implemented")
        
    def __eq__(self, other):
        raise NotImplementedError("[DExtensiongFunctor] __eq__ not implemented")

    def merge(self, other):
        raise NotImplementedError("[DExtensiongFunctor] merge not implemented")

class DExtensionSimpleMorphism (Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`DExtension_generic` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        if(p.degree() == 0):
            return self.codomain()(p.coefficients()[0])

        return self.codomain()(str(p))

__all__ = [
    "DExtension", "is_DExtension" # names imported
]