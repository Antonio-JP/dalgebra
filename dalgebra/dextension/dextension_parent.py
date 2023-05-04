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

from itertools import chain, islice

from sage.all import cached_method, Parent, CommutativeRing, latex, prod, PolynomialRing, ZZ
from sage.categories.all import Morphism, CommutativeAlgebras
from sage.categories.pushout import ConstructionFunctor
from sage.rings.polynomial.multi_polynomial_ring import MPolynomialRing_polydict_domain
from sage.rings.ring import Ring #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from typing import Collection, Any

from .dextension_element import DExtension_element
from ..dring import AdditiveMap, DRings

logger = logging.getLogger(__name__)

_DRings = DRings.__classcall__(DRings)

## Factories for all structures
class DExtensionFactory(UniqueFactory):
    r'''
        TODO: add documentation
    '''
    def create_key(self, base: Parent, values_operations: Collection[Collection[Any]], *names : str, **kwds):
        names = kwds["names"] if len(names) == 0 and "names" in kwds else names
        
        if not base in _DRings:
            raise TypeError(f"[DExtensionFactory] The base ring ({base}) must be a d-ring.")
        aux_R = PolynomialRing(base, names)
        noperators = base.noperators()
        ngens = len(names)

        if ngens > 1 and noperators > 1: # we require list of lists
            if ((not isinstance(values_operations, (list, tuple)) or len(values_operations) != ngens) or 
                any((not isinstance(imgs, (list, tuple)) or len(imgs) != noperators) for imgs in values_operations)):
                raise TypeError(f"[DExtensionFactory] For {ngens} variables and {noperators} operators, we require a list of lists as ``value_operations`` argument.")
        elif ngens > 1 and noperators == 1: # we allow list of lists or a simple list
            if (not isinstance(values_operations, (list, tuple)) or len(values_operations) != ngens):
                raise TypeError(f"[DExtensionFactory] For {ngens} variables and {noperators} operator, we require a list of elements.")
            if any(isinstance(imgs, (list, tuple) and len(imgs) > 1) for imgs in values_operations):
                raise TypeError(f"[DExtensionFactory] For {ngens} variables and {noperators} operator, images must be elements or lists of length 1")
            values_operations = [imgs if isinstance(imgs, list(tuple)) else [imgs] for imgs in values_operations]
        elif ngens == 1 and noperators > 1: # we allow list of lists or a simple list
            if not isinstance(values_operations, (list, tuple)):
                raise TypeError(f"[DExtensionFactory] For {ngens} variable and {noperators} operators, we require a list of elements or a list with one list of elements")
            elif len(values_operations) == 1 and (not isinstance(values_operations[0], (list,tuple)) or len(values_operations[0], noperators)):
                raise TypeError(f"[DExtensionFactory] For {ngens} variable and {noperators} operators, we require a list with one list of elements")
            elif len(values_operations) > 1 and len(values_operations) != noperators:
                raise TypeError(f"[DExtensionFactory] For {ngens} variable and {noperators} operators, we require a list of elements")
            elif len(values_operations) == noperators: # we convert the input into a list of lists
                values_operations = [values_operations]
        else: # ngens = noperators = 1 --> we allow the list of lists, list of element or an element
            if not isinstance(values_operations, (list, tuple)):
                values_operations = [[values_operations]]
            elif len(values_operations) != 1:
                raise TypeError(f"[DExtensionFactory] For {ngens} variable and {noperators} operator, we require a list with one element or a list with one list")
            elif not isinstance(values_operations[0], (list, tuple)):
                values_operations = [values_operations]
            elif len(values_operations[0]) != 1:
                raise TypeError(f"[DExtensionFactory] For {ngens} variable and {noperators} operator, we require a list with one element or a list with one list")
        
        # We transform eh images of the operations into polynomial elements in ``self``
        values_operations = tuple([tuple([aux_R(img) for img in imgs]) for imgs in values_operations])

        return (base, tuple(names), values_operations)

    def create_object(self, _, key):
        base, names, values_operations = key
        return DExtension_parent(base, values_operations, names)
        
DExtension = DExtensionFactory("dalgebra.dextension.dextension_parent.DExtension")

class DExtension_parent(MPolynomialRing_polydict_domain):
    r'''
        Polynomial d-extension for a d-ring.

        Let `(R, \Delta)` be a d-ring with operators `\Delta = \{\sigma_1,\ldots, \sigma_m\}` (see 
        :mod:`~dalgebra.dring` for further information), and consider now the polynomial ring 
        `R[y_1,\ldots,y_n]`. If the operations are all well-behaved with the product (i.e., they are 
        homomorphisms, derivations or skew-derivations) they can be easily extended to the new polynomial ring.
        Only the images of the generators are needed to uniquely defined the extension operations.

        Although the same behavior can be achieved directly with d-rings, this class is more specific and provide
        more methods for working with these particular extensions. In particular, these rings and their elements 
        can implement some of the theory that can be found in:

        * *M. Bronstein*: **Symbolic Integration I**. `ISBN:978-3-662-03386-9 <https://link.springer.com/book/10.1007/978-3-662-03386-9>`_: look 
          into *monomial extensions*, for the differential case.
        * *M. van der Put* and *M.F. Singer*: **Galois Theory of Difference Equations**. `ISBN:978-3-540-63243-6 <https://link.springer.com/book/10.1007/BFb0096118>`_: 
          analog of previous for the difference case.
        * :arxiv:`2005.0494` (*Abramov*, *Bronstein*, *Petkovsek* and *Schneider*): look into `\Sigma\Pi`-extensions for deeper study on the difference case.

        INPUT:

        * ``values_operations``: list of images (list of elements) of the generators. They must be able to be casted into multi-variate polynomials
          that will be generated by this ring. In case only one generator is given, we allow only its image to be given (without tuple/list format). 
          In case only one operator is present in the base ring, we allow the image to be given without the list/tuple format.
        * ``names``: names to be given to the new variables of the ring.

        EXAMPLES::

            sage: from dalgebra import *
            sage: B = DifferentialRing(QQ) # (QQ, 0)
            sage: R.<x> = DExtension(B, 1) # (QQ[x], \partial_x)
            sage: S.<ex> = DExtension(R, 'ex') # (QQ[x, e^x], \partial_x)
            sage: T.<sin,cos> = DExtension(B, ['cos', '-sin']) # (QQ[sin(x),cos(x)], \partial_x)

        This class can also extend several operators at once::

            sage: B = DifferenceRing(DifferentialRing(QQ)) # (QQ (0, id))
            sage: R.<x> = DExtension(B, [1, 'x+1']) # (QQ[x], (\partial_x, x -> x+1))
            sage: T.<sin,cos> = DExtension(B, [['cos','sin'], ['-sin', 'cos']]) # (QQ[sin(x),cos(x)], (\partial_x, id))

        This class allows several types of inputs for the images of the new variables. When only one variable/operator is present, we do not
        require the input to be in format list, but the output ring will be the same::

            sage: # Case with 1 operator and 1 variable
            sage: B = DifferentialRing(QQ) # (QQ, 0)
            sage: R1.<x> = DExtension(B, 1)
            sage: R2.<x> = DExtension(B, [1])
            sage: R3.<x> = DExtension(B, [[1]])
            sage: R1 is R2 and R2 is R3
            True
            sage: # Case with 1 operator and several variables
            sage: R1.<x,y> = DExtension(B, [1,0])
            sage: R2.<x,y> = DExtension(B, [[1],[0]])
            sage: R1 is R2
            True
            sage: # Case with several operators and 1 variable
            sage: B = DifferenceRing(DifferentialRing(QQ)) # (QQ (0, id))
            sage: R1.<x> = DExtension(B, [1, 'x+1'])
            sage: R2.<x> = DExtension(B, [[1, 'x+1']])
            sage: R1 is R2
            True
    '''
    Element = DExtension_element # TODO: add the class for elements

    def __init__(self, base : Parent, values_operations: Collection[Collection[Any]], names : Collection[str]):
        ## Resetting the category to be the appropriate
        CommutativeRing.__init__(self, base, category=[_DRings, CommutativeAlgebras(base)])
        MPolynomialRing_polydict_domain.__init__(self, base, len(names), names, "degrevlex")
        CommutativeRing.__init__(self, base, category=[_DRings, self.category()])
        ## Setting the generators to proper type
        self._gens = tuple(self.gen(i) for i in range(self.ngens()))

        self.__hash = (base, values_operations, names)
        ## Checking the type and shape of the input
        if not base in _DRings:
            raise TypeError(f"[DExtension] The base ring ({base}) must be a d-ring.")
        noperators = base.noperators()
        ngens = len(names)

        if (not isinstance(values_operations, Collection) or 
            len(values_operations) != ngens or 
            any((not isinstance(values, Collection) or len(values) != noperators) for values in values_operations)
        ):      
            raise TypeError("The structure for the values for the opearations does not match the number of operations and variables.") 

        # Registering conversion to simpler structures
        current = self.base()
        morph = DExtensionSimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DExtensionSimpleMorphism(self, current)
            current.register_conversion(morph)
            
        # We create now the operations for this d-ring
        values_for_each_operation = list(map(list, zip(*values_operations)))
        self.__operators : tuple[Morphism] = tuple([
            self._create_operator(i, ttype, values) 
            for (i,(ttype, values)) in enumerate(zip(base.operator_types(), values_for_each_operation))
        ])

    #################################################
    ### Coercion methods
    #################################################             
    def _element_constructor_(self, x) -> DExtension_element:
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into the corresponding type for ``self``.
        '''
        p = super()._element_constructor_(x)
        return self.element_class(self, p)

    def gen(self, i: int = None) -> DExtension_element:
        r'''
            TODO: add documentation 
        '''
        if isinstance(i, str):
            i = self.variable_names().index(i)
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return self.element_class(self, {(i+1,): 1})
     
    def construction(self) -> DExtensionFunctor:
        r'''
            TODO: add documentation
        '''
        return DExtensionFunctor(self.variable_names(), [[self.operation(g, i) for i in range(self.noperators())] for g in self.gens()]), self.base()
    
    def change_ring(self, R) -> DExtension_parent:
        r'''
            TODO: add documentation
        '''
        if not R in _DRings:
            raise TypeError(f"[change_ring] The new ring must be a d-ring (got: {R})")
        
        return DExtension(R, [[self.operation(i, g) for i in range(self.noperators())] for g in self.gens()], names=self.variable_names())

    def base_ring(self):
        return self.base().sage_ring()

    #################################################
    ### Magic python methods
    #################################################
    def __hash__(self) -> int:
        return hash(self.__hash)

    def __repr__(self) -> str:
        return f"DExtension({self.__hash})"

    def _latex_(self):
        raise r"\left(" + super()._latex_() + ",".join([f"{latex(g)} \\mapsto [{','.join(self.operation(i,g) for i in range(self.noperators()))}]" for g in self.gens()]) + r"\right)"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self) -> DExtension_element:
        r'''
            TODO: add documentation
        '''
        return self(1)
    
    def zero(self) -> DExtension_element:
        r'''
            TODO: add documentation
        '''
        return self(0)
    
    def random_element(self,
        degree: int = 2, terms: int = 5, choose_degree: bool = False, *args, **kwargs
    ) -> DExtension_element:
        return self.element_class(self, super().random_element(degree, terms, choose_degree, *args, **kwargs))
      
    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[Morphism]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()
    
    def _create_operator(self, operation: int, ttype: str, values: list[DExtension_element]) -> Morphism:
        r'''
            Method to create a map on the ring of polynomials from an operator on the base ring.

            We create an :class:`Morphism` from the given operator assuming the type given in ``ttype``.
            This type will determine how the multiplication behaves with respect to the different variables.
        '''
        operator = self.base().operators()[operation] 
        if ttype == "homomorphism":
            new_operator = self.Hom(self)(values, base_map=operator)
        elif ttype == "derivation":
            def __skip_i(seq, i):
                return chain(islice(seq, 0, i), islice(seq, i+1, None))
            def __extended_derivation(element: DExtension_element):
                if element.is_monomial():
                    if element == self.one():
                        return self.zero()
                    variables, degrees = list(zip(*[(var, deg) for var,deg in zip(self.gens(), element.degrees()) if deg > 0]))
                    base = prod(g**(d-1) for g,d in zip(variables, degrees))
                    return base*sum(degree*prod(__skip_i(variables, i)) for (i,degree) in enumerate(degrees) if degree > 0)
                else:
                    return sum(
                        operator(self.base()(coeff)) * monom + coeff * __extended_derivation(monom)
                        for coeff, monom in zip(element.coefficients(), element.monomials())
                    )
            new_operator = AdditiveMap(self, __extended_derivation)
        elif ttype == "skew":
            raise NotImplementedError("[DExtension] _create_operator - skew not implemented")
        else:
            raise ValueError(f"The type {ttype} is not recognized as a valid operator.")

        return new_operator
    
    def linear_operator_ring(self) -> Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the 
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError("[DExtension] __init__ not implemented")

    def inverse_operation(self, element: DExtension_element, operation: int = 0) -> DExtension_element:
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
    
    def __inverse_homomorphism(self, element: DExtension_element, operation: int):
        raise NotImplementedError("[DExtension] __inverse_homomorphism not implemented")
    
    def __inverse_derivation(self, element: DExtension_element, operation: int):
        raise NotImplementedError("[DExtension] __inverse_derivation not implemented")
   
    def __inverse_skew(self, element: DExtension_element, operation: int):
        raise NotImplementedError("[DExtension] __inverse_skew not implemented")
    
def is_DExtension(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, DExtension_parent)

class DExtensionFunctor (ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DExtension_parent`.

        This class represents the functor that adds new variables to a d-ring 
        extending the operations with polynomial images. This functor requires that the
        number of operations matches the number of images in the functor.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DifferentialPolynomialRing_dense`)
        * ``images``: values (something that ca be casted) for the variables for each of the 
          operations.
    '''
    def __init__(self, variables: Collection[str], images: Collection[Collection[Any]]):
        if len(variables) == 0:
            raise ValueError("At least one new variable has to be added")
        self.__variables = variables
        if len(images) != len(variables):
            raise TypeError("The same number of variables must be given for the images.")
        if any(len(v) != len(images[0]) for v in images[1:]):
            raise ValueError("Incosistent number of images for each operator.")
        self.__images = images
        super().__init__(_DRings,_DRings)
        
    ### Methods to implement        
    def _apply_functor(self, x):
        if x.noperators() != len(self.__images[0]):
            raise TypeError(f"{x} do not have appropriate number of operations ({len(self.__images[0])}")
        
        return DExtension(x, names=self.__variables, values_operations=self.__images)
        
    def _repr_(self):
        return f"DExtension(*, {self.__images}, names={self.__variables})"
        
    def __eq__(self, other):
        if not isinstance(other, DExtensionFunctor):
            return False
        if self.__variables != other.__variables:
            return False
        return all([str(img) for img in s_image] == [str(img) for img in o_image] for (s_image, o_image) in zip(self.__images, other.__images))

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