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

from collections.abc import Sequence
from functools import reduce
from itertools import chain, islice

from sage.all import cached_method, Parent, latex, prod, PolynomialRing, QQ, ZZ
from sage.categories.all import Morphism, IntegralDomains
from sage.categories.pushout import ConstructionFunctor
from sage.graphs.digraph import DiGraph
from sage.rings.polynomial.multi_polynomial_ring import MPolynomialRing_polydict_domain
from sage.rings.ring import IntegralDomain, Ring #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from typing import Collection, Any

from .dextension_element import DExtension_element
from ..dring import AdditiveMap, DRings, DFractionField

logger = logging.getLogger(__name__)

_DRings = DRings.__classcall__(DRings)
_IntegralDomains = IntegralDomains.__classcall__(IntegralDomains)

def is_sequence(element):
    return isinstance(element, Sequence) and not isinstance(element, str)

## Factories for all structures
class DExtensionFactory(UniqueFactory):
    r'''
        Factory for arbitrary d-extensions.

        This factory will take as input a d-Ring `R` (see module :mod:`..dring`) a set of names for new variables and 
        a sequence of all the necessary values for extending the operations in `R` to the extended ring ``R[names]``. 
        To allow flexibility in the objects we can create with this class, we allow the images to be in 
        the Field of Fractions of the polynomial ring ``R[names]``. This is handled using the extension of 
        fraction fields for d.rings implemented in :class:`..dring.DFractionField`.

        INPUT:

        * ``base``: a d-ring `R` to be extended.
        * ``values_operations``: input enough to extract the images of the new variables w.r.t. the operators in ``base``.
        * ``names``: names used for the new variables. This allows the SageMath syntax ``.<*>``.
    '''
    def create_key(self, base: Parent, values_operations: Sequence[Sequence[Any]], *names : str, **kwds):
        ## Checking the argument "names"
        names = kwds["names"] if len(names) == 0 and "names" in kwds else names
        ## Checking argument "_recursive" (private argument)
        _recursive = kwds.get("_recursive", False)
        
        ## Checking the ``base`` ring is a d-ring
        if not base in _DRings:
            raise TypeError(f"[DExtensionFactory] The base ring ({base}) must be a d-ring.")
        
        noperators = base.noperators()
        ngens = len(names)

        ## Checking the argument ``values_operations`` is correct
        if not is_sequence(values_operations): # element input
            if noperators == 1 and ngens == 1:
                values_operations = [[values_operations]]
            else:
                raise TypeError(f"[DExtensionFactory - single] for more than one operation ({noperators}) or one generator ({ngens}) more values are required")
        elif all(not is_sequence(vals) for vals in values_operations): # just a list input
            if noperators == 1 and ngens == 1 and len(values_operations) != 1:
                raise TypeError(f"[DExtensionFactory - list] For 1 operation and 1 generator required a list on length 1 (got {len(values_operations)})")
            elif noperators == 1 and ngens == 1: # we convert the input into a list of lists
                values_operations = [values_operations]
            elif noperators == 1: # we interpret the list as images for the only operation
                values_operations = [[el] for el in values_operations]
            elif ngens == 1: # we interpret the list as the image fot the first generator
                values_operations = [values_operations]
        
        # Now values_operations must be a list of `ngens` lists with `noperators` elements each
        if not is_sequence(values_operations):
            raise TypeError(f"[DExtensionFactory] 'values_operations' must be a list")
        elif len(values_operations) != ngens:
            raise TypeError(f"[DExtensionFactory] 'values_operations' must be a list with {ngens} elements")
        elif any(not is_sequence(vals) for vals in values_operations):
            raise TypeError(f"[DExtensionFactory] 'values_operations' must be a list of {ngens} lists")
        elif any(len(vals) != noperators for vals in values_operations):
            raise TypeError(f"[DExtensionFactory] 'values_operations' must be a list of {ngens} lists with {noperators} elements each")
        
        # We transform the images of the operations into rational elements in ``self``
        ## Special case when `base` is already a DExtension
        if isinstance(base, DExtension_parent) and not _recursive:
            base_names = [str(g) for g in base.gens()]
            if any(base_name in names for base_name in base_names):
                raise ValueError(f"[DExtensionFactory - base] repeated name in the base ring and the requested new variables")
            names = base_names + list(names)
            values_operations = [[str(g.operation(i)) for i in range(noperators)] for g in base.gens()] + list(values_operations)
            base = base.base()

        aux_R = PolynomialRing(base.wrapped if hasattr(base, "wrapped") else base, names) # use to better capture the nature of the values.
        aux_F = aux_R.fraction_field()
        values_operations = {name : tuple([aux_F(img) for img in vals]) for (name, vals) in zip(names, values_operations)}

        return (base, tuple(names), frozenset(values_operations.items()))

    def create_object(self, _, key):
        base, names, values_operations = key
        values_operations = dict(values_operations)
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

        * ``base``: a d-ring where this ring will be based on.
        * ``values_operations``: a dictionary ``name -> values`` where the values is a tuple of values of the images of the new variables
          with the old operations.
        * ``names``: names to be given to the new variables of the ring. All names must be included in ``values_operations``

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
    Element = DExtension_element 

    def __init__(self, base : Parent, values_operations: dict[str,Sequence[Any]], names : Sequence[str], category=_DRings):
        ## Calling previous classes __init__ methods
        MPolynomialRing_polydict_domain.__init__(self, base.wrapped if hasattr(base, "wrapped") else base, len(names), names, "degrevlex")
        self._refine_category_(category)
        self.__base = base

        ## Setting the generators to proper type
        self._gens = tuple(self.gen(i) for i in range(self.ngens()))
        self.__hash = (base, tuple(names), frozenset(values_operations.items())) # same as the key for DExtensionFactory

        ## Checking the type and shape of the input
        if not base in _DRings:
            raise TypeError(f"[DExtension] The base ring ({base}) must be a d-ring.")
        noperators = base.noperators()
        ngens = len(names)

        if (not isinstance(values_operations, dict) or 
            len(values_operations) != ngens or 
            any((not is_sequence(values) or len(values) != noperators) for values in values_operations.values())
        ):      
            raise TypeError("The structure for the values for the operations does not match the number of operations and variables.") 

        # Registering conversion to simpler structures
        current = self.base()
        morph = DExtensionSimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DExtensionSimpleMorphism(self, current)
            current.register_conversion(morph)
            
        # We create now the operations for this d-ring
        self.__operators : tuple[Morphism] = tuple([
            self._create_operator(i, ttype) 
            for (i,ttype) in enumerate(base.operator_types())
        ])
        
        # Values for caching output of methods
        self.__fraction_field = None
        # Storing the values for the operations
        self.__values = [{g: self.fraction_field()(values_operations[str(g)][i]) for g in self.gens()} for i in range(self.noperators())]
        # raise RuntimeError

    #################################################
    ### Getting information methods
    #################################################             
    def base(self):
        return self.__base

    def base_ring(self):
        if hasattr(self, "_DExtension_parent__base"):
            return self.base()
        else:
            return super().base_ring()

    def gen(self, i: int = 0) -> DExtension_element:
        r'''
            TODO: add documentation 
        '''
        if isinstance(i, str):
            i = self.variable_names().index(i)
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return self.element_class(
            self, {
                tuple(1 if j == i else 0 for j in range(len(self._names))): QQ(1) if not hasattr(self, "_DExtension_parent__base") else self.base().one() # degree 1 in the index `i`, coefficient 1
            })
    
    @cached_method
    def operation_on_gens(self, operation: int) -> dict[DExtension_element, DExtension_element]:
        return self.__values[operation]
    
    @cached_method
    def operations_on_gen(self, gen: DExtension_element) -> Sequence[DExtension_element]:
        return tuple(self.__values[i][gen] for i in range(self.noperators()))
    
    @cached_method
    def operations_on_gens(self):
        return self.__values
    
    #################################################
    ### Coercion methods
    #################################################
    def __call__(self, x=0, check=True):
        from sage.all import parent
        if parent(x) is self: # avoiding weird recursions on the coercion system (?)
            return x
        super_call = super().__call__(x, check)
        return self.element_class(self, super_call.dict()) if hasattr(super_call,"dict") else super_call

    def _coerce_map_from_(self, S):
        from sage.categories.pushout import pushout
        if not isinstance(S, DExtension_parent):
            try:
                return super()._coerce_map_from_(S)
            except:
                return None
        
        try:
            return pushout(self, S) == self
        except:
            return None

    def _pushout_(self, other):
        r'''
            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(DifferentialRing(QQ))
                sage: Q.<x,y,z> = DExtension(B, [[1, 'x+1'],[0,'y'],['z','y*z']]) # y = e, z = e^x
                sage: R = Q.univariate_ring(x)
        '''
        from sage.categories.pushout import pushout
        from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing

        # Special case when comparing with a polynomial ring with same variables as ``self``
        if isinstance(other, DExtension_parent):
            R = self.base(); S = other.base()
            try:
                newB = pushout(self, S)
                if newB == S: return other
            except: pass
            try:
                newB = pushout(R, other)
                if newB == R: return self
            except: pass
            try:
                if ((self.noperators(), self.ngens(), self.variable_names()) == (other.noperators(), other.ngens(), other.variable_names())):
                    newB = pushout(R,S)
                    aux_output = PolynomialRing(newB, self.variable_names())
                    for name in self.variable_names():
                        img_self = [aux_output(str(el)) for el in self.operations_on_gen(self(name))]
                        img_other = [aux_output(str(el)) for el in other.operations_on_gen(other(name))]
                        if any(a != b for a,b in zip(img_self,img_other)):
                            return None # impossible to do pushout in canonical way. Falling back to other implementations
                    return DExtension(newB, [[str(el) for el in self.operations_on_gen(g)] for g in self.gens()], names=self.variable_names()) 
            except: pass
        elif is_MPolynomialRing(other):
            true_base = self.base_ring().wrapped if hasattr(self.base_ring(), "wrapped") else self.base_ring()
            if ((self.ngens(), self.variable_names()) == (other.ngens(), other.variable_names())):
                return DExtension(pushout(self.base(), other.base_ring()), [self.operations_on_gen(g) for g in self.gens()], names=self.variable_names())
        return None

    def construction(self) -> DExtensionFunctor:
        r'''
            TODO: add documentation
        '''
        return DExtensionFunctor(self.variable_names(), {str(g): self.operations_on_gen(g) for g in self.gens()}), self.base()
    
    def change_ring(self, R) -> DExtension_parent:
        r'''
            TODO: add documentation
        '''
        if not R in _DRings:
            raise TypeError(f"[change_ring] The new ring must be a d-ring (got: {R})")
        
        return DExtension(R, [[str(el) for el in self.operations_on_gen(g)] for g in self.gens()], names=self.variable_names())

    #################################################
    ### Magic python methods
    #################################################
    def __hash__(self) -> int:
        return hash(self.__hash)

    def __repr__(self) -> str:
        return f"DExtension({self.base()}, [{','.join(f'{g} -> {self.operations_on_gen(g)}' for g in self.gens())}]"

    def _latex_(self):
        raise r"\left(" + super()._latex_() + ",".join([f"{latex(g)} \\mapsto [{','.join(self.operation(i,g) for i in range(self.noperators()))}]" for g in self.gens()]) + r"\right)"
            
    #################################################
    ### Element generation methods
    #################################################    
    def random_element(self, degree: int = 2, terms: int = 5, choose_degree: bool = False, *args, **kwargs) -> DExtension_element:
        return self.element_class(self, super().random_element(degree, terms, choose_degree, *args, **kwargs).dict())
      
    #################################################
    ### Method the MPolynomialRing class
    #################################################
    def fraction_field(self):
        try:
            if self.is_field():
                return self
        except NotImplementedError:
            pass

        if not self.is_integral_domain():
            raise TypeError("self must be an integral domain.")

        if self.__fraction_field is not None:
            return self.__fraction_field
        else:
            K = DFractionField(self)
            self.__fraction_field = K
        return self.__fraction_field

    def remove_var(self, *var):
        r'''
            Remove variables preserving the d-structure if possible.

            If not possible, we raise a TypeError.

            TODO: Check if it is possible to create coercion and conversion maps 
            between ``self`` and the resulting ring from this method.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(DifferentialRing(QQ))
                sage: Q.<x,y,z> = DExtension(B, [[1, 'x+1'],[0,'y'],['z','y*z']]) # y = e, z = e^x
                sage: Q
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [x -> (1, x + 1),y -> (0, y),z -> (z, y*z))
                sage: Q.remove_var(x)
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [y -> (0, y),z -> (z, y*z))
                sage: Q.remove_var(z)
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [x -> (1, x + 1),y -> (0, y))
                sage: Q.remove_var(x,z)
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [y -> (0, y))
                sage: Q.remove_var(z,x)
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [y -> (0, y))
                sage: Q.remove_var(y)
                Traceback (most recent call last):
                ...
                TypeError: Impossible to remove [y] from DExtension...
                sage: Q.remove_var(y,z)
                DExtension(Ring [[Rational Field], (0, Hom({1: 1}))], [x -> (1, x + 1))
                sage: Q.remove_var(x,y,z)
                Ring [[Rational Field], (0, Hom({1: 1}))]
        '''
        var = [self(v) for v in var] # casting to elements in ``self``
        rem_vars = [v for v in self.gens() if not v in var] # getting list of remaining variables
        ## Extreme case: we remove all variables
        if len(rem_vars) == 0:
            return self.base()

        rem_ops = [self.operations_on_gen(v) for v in rem_vars]

        if any((v not in rem_vars) for imgs in rem_ops for el in imgs for v in el.variables()):
            raise TypeError(f"Impossible to remove {var} from {self} since operations over {rem_vars} require of these variables.")
        
        return DExtension(self.base(), [[str(el) for el in imgs] for imgs in rem_ops], names=[str(v) for v in rem_vars])

    def univariate_ring(self, var):
        if not var in self.gens():
            raise ValueError(f"Variable {var} not in {self}")
        return DExtension(
            self.remove_var(var), 
            [tuple(str(el) for el in self.operations_on_gen(var))],
            names=[str(var)],
            _recursive=True
        )

    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[Morphism]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()
    
    def _create_operator(self, operation: int, ttype: str) -> Morphism:
        r'''
            Method to create a map on the ring of polynomials from an operator on the base ring.

            We create an :class:`Morphism` from the given operator assuming the type given in ``ttype``.
            This type will determine how the multiplication behaves with respect to the different variables.
        '''
        operator = self.base().operators()[operation] 
        if ttype == "homomorphism":
            def __extended_homomorphism(element: DExtension_element):
                if element in self.base():
                    return self(operator(self.base()(element)))
                if element.is_monomial():
                    variables, degrees = list(zip(*[(var, deg) for var,deg in zip(self.gens(), element.degrees()) if deg > 0]))
                    return prod((self.__values[operation][g]**d for g,d in zip(variables, degrees)), z = self.one())
                else:
                    return sum(operator(coeff) * __extended_homomorphism(monom) for coeff, monom in zip(element.coefficients(), element.monomials()))
            new_operator = AdditiveMap(self, __extended_homomorphism)
        elif ttype == "derivation":
            def __skip_i(seq, i):
                return chain(islice(seq, 0, i), islice(seq, i+1, None))
            def __extended_derivation(element: DExtension_element):
                if element in self.base():
                    return self(operator(self.base()(element)))
                if element.is_monomial():
                    if element == self.one():
                        return self.zero()
                    variables, degrees = list(zip(*[(var, deg) for var,deg in zip(self.gens(), element.degrees()) if deg > 0]))
                    base = prod(g**(d-1) for g,d in zip(variables, degrees))
                    return base*sum(
                        (self.__values[operation][variables[i]] * self(degree) * prod(
                            __skip_i(variables, i),
                            z = self.one()
                        ) for (i,degree) in enumerate(degrees) if degree > 0),
                        self.zero()
                    )
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
    
    #################################################
    ### Specific methods for DExtensions
    #################################################
    @cached_method
    def dependency_graph(self, operation: int = None) -> DiGraph:
        r'''
            Method that return a graph of dependency between the variables of a d-Extension.

            This method build a directed graph where the vertices are the variables that are created 
            in this d-extension and the edge `(u,v)` is in the graph if the variable `v` appears 
            in the image by an operator (any if ``operation`` is ``None``) applied to `u`.
        '''
        vertices = self.gens()
        edges = []
        for u in vertices:
            if operation is None:
                deps = tuple(reduce(lambda p,q: p.union(q), (set(el.variables()) for el in self.operations_on_gen(u))))
            else:
                deps = self.operations_on_gen(u)[operation].variables()
            for v in deps:
                if v != u: edges.append((u,v))
        
        return DiGraph((vertices, edges), format="vertices_and_edges", immutable=True)

def is_DExtension(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, DExtension_parent)

class DExtensionFunctor(ConstructionFunctor):
    """
    A constructor for d-extensions
    """

    rank = 11 # just above d-rings

    def __init__(self, vars, values: dict[str,Any]):
        super().__init__(_DRings, _DRings)
        self.vars = vars
        self.values = values

    def _apply_functor(self, R):
        return DExtension(R, [[str(el) for el in self.values[v]] for v in self.vars], names=self.vars, _recursive=True)

    def __eq__(self, other):
        if isinstance(other, DExtensionFunctor):
            return (self.vars == other.vars and
                    self.values == other.values)
        else:
            return False

    def __ne__(self, other):
        return not (self == other)

    def __hash__(self):
        return hash(frozenset(self.values))

    def merge(self, other):
        if self == other:
            return self
        else:
            return None

    def _repr_(self):
        """
        TESTS::

            sage: QQ['x,y,z,t'].construction()[0]
            MPoly[x,y,z,t]
        """
        return f"DExtension[{','.join(self.vars)}]({self.values})"

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