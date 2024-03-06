r'''
    Module with the implementation of d-monomials.

    Given a number of operations and a set of variables, the associated d-monomials form a 
    commutative Monoid (see :class:`sage.categories.monoids.Monoids`). This is a set
    with an operation `*` that is associative, commutative and with a unit `1`.

    This module includes all the classes necessary to implement these d-monomials. In particular,
    this will include a bijection between `\mathbb{N}` and `\mathbb{N}^d` for any `d \in \mathbb{N}`
    (see :func:`IndexBijection`), a Parent structure for the d-monoids (see :class:`DMonomialMonoid`) 
    and the Element class associated for these Parent structures (see :class:`DMonomial`).

    One of the key characteristics of a monoid of d-monomials is that they are free monoids over an
    infinite set of generators. For any given variable `a_*`, we need to consider as free variables
    of the monoid all the elements `a_{I}` for `I \in \mathbb{N}^d` where `d` is the number of operations
    associated with the monoid.

    That is why we also provide a class :class:`DMonomialGen` that will represent the `a_*` that will
    generate all the associated free variables given the indices.
'''
from __future__ import annotations

import logging

from sage.all import (binomial, cached_method, cartesian_product, ZZ, Parent)
from sage.categories.all import Morphism
from sage.categories.monoids import Monoids
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.sets.family import LazyFamily
from sage.structure.element import Element #pylint: disable=no-name-in-module

from typing import Collection

logger = logging.getLogger(__name__)
_CommutativeMonoids = Monoids.Commutative.__classcall__(Monoids.Commutative)

__BIJECTIONS = {}
def IndexBijection(size : int):
    r'''
        Factory for the bijections of a given size.

        This method returns a unique bijection object that allow to map integers to tuples of 
        the given size in a specific order. This order tries to have the appearance of all
        tuples whose sum is fixed as soon as possible.

        For example, for size `3` the tuples generated would be as follows:

        .. MATH::

            (0,0,0) \rightarrow (0,0,1) \rightarrow (0,1,0) \rightarrow (1,0,0) \rightarrow (0,0,2) \rightarrow (0,1,1) 
            \rightarrow (0,2,0) \rightarrow (1,0,1) \rightarrow (1,1,0) \rightarrow (2,0,0) \rightarrow \ldots

        These bijections cache some of its results, hence the convenience of always returning the same 
        bijection object.

        INPUT:

        * ``size``: number of elements of the tuples generated by the bijection.

        OUTPUT:

        A :class:`IndexBijection_Object` with the given bijection.

        EXAMPLES::

            sage: from dalgebra.dpolynomial.dpolynomial_element import IndexBijection
            sage: size2 = IndexBijection(2)
            sage: size2(0)
            (0, 0)
            sage: size2(10)
            (0, 4)
            sage: size2(100)
            (9, 4)
            sage: size4 = IndexBijection(4)
            sage: [size4(i) for i in range(5)]
            [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0), (1, 0, 0, 0)]

        Since we have a bijection, we can also go back:

            sage: IndexBijection(10).inverse((1,2,3,4,5,6,7,8,9,10)) # around 2ms
            156289762326
    '''
    if not size in __BIJECTIONS:
        __BIJECTIONS[size] = IndexBijection_Object(size)    
    return __BIJECTIONS[size]
 
class IndexBijection_Object (Morphism):
    def __init__(self, size : int):
        Morphism.__init__(self, NN, cartesian_product(size*[NN]))
        self.dim = size

    @staticmethod
    def elements_summing(n: int, l: int) -> int:
        r'''Number of elements summing `n` in `l` elements'''
        return binomial(n+l-1, n)

    @staticmethod
    def tuple_summing(index: int, n: int, l: int) -> tuple[int]:
        r'''Tuple in position ``index`` summing `n` in `l` elements'''
        if index < 0 or index >= IndexBijection_Object.elements_summing(n,l):
            raise ValueError
        if l == 1:
            return tuple([n])
        elif n == 0:
            return tuple(l*[0])
        first = 0
        while index >= IndexBijection_Object.elements_summing(n-first, l-1):
            index -= IndexBijection_Object.elements_summing(n-first, l-1); first += 1
        return tuple([first] + list(IndexBijection_Object.tuple_summing(index, n-first, l-1)))

    @cached_method
    def _call_(self, index: int) -> Element:
        r'''Computes the image of a natural number'''
        if self.dim == 1:
            return index
        sum_of_elements = 0
        while index >= IndexBijection_Object.elements_summing(sum_of_elements, self.dim):
            index -= IndexBijection_Object.elements_summing(sum_of_elements, self.dim)
            sum_of_elements += 1
        return self.codomain()(IndexBijection_Object.tuple_summing(index, sum_of_elements, self.dim))

    @cached_method
    def inverse(self, image: Element) -> int:
        r'''Computes the pre-image of a tuple of ``self.dim`` natural numbers'''
        if self.dim == 1:
            return image
        if not len(image) == self.dim:
            raise TypeError("Given element has inappropriate length")
        sum_of_elements = sum(image)
        result = IndexBijection_Object.elements_summing(sum_of_elements-1, self.dim+1) # elements summing less than "sum_of_elements"
        for i in range(len(image)-1):
            result += sum(IndexBijection_Object.elements_summing(sum_of_elements - j, self.dim - i-1) for j in range(image[i]))
            sum_of_elements -= image[i]
        return self.domain()(result)

    def iter(self, sum_bound : int):
        quantity = IndexBijection_Object.elements_summing(sum_bound, self.dim + 1)
        for i in range(quantity): yield self(i) 

class DMonomial(Element):
    r'''
        Class to represent a differential monomial. 

        We represent a differential monomial in a sparse way where we have a map
        `(v, o) -> e`,
        where `v` is the index of a variable, `o` is the order (i.e., a tuple of integers non-negative),
        and `e` is the exponent in the monomial.

        We allow to provide the input in dictionary format or tuple format. In the tuple format, we allow 
        the key to be just a number, representing the element `(v, 0)`.

        We *do not* allow to modify this object once is created.

        EXAMPLES::

            sage: from dalgebra import *
            sage: from dalgebra.dpolynomial.dpolynomial import *
            sage: R = DPolynomialRing(DifferentialRing(DifferenceRing(QQ)), names=("a","b")) # ring with two variables and two operators
            sage: a, b = R.gens()
            sage: a[(0,5)]
            a_0_5
            sage: a[10]
            a_0_4
            sage: a[(2,3)]*b[(1,0)]
            a_2_3*b_1_0
            sage: b[0]**2*a[10]*b[1]
            a_0_4*b_0_0**2*b_0_1
    '''
    def __init__(self, parent: DMonomialMonoid, input: DMonomial | dict[tuple[int,tuple[int]|int],int] | tuple[tuple[int,tuple[int]|int]|int, int]):
        self._variables = dict()
        self._parent = parent
        if isinstance(input, DMonomial):
            input = tuple(input._variables.items())
        elif isinstance(input, dict):
            input = tuple(input.items())

        if not isinstance(input, (tuple, list)):
            raise TypeError(f"[DMonomial] Incorrect type for a DMonomial")
        
        for element in input: # We iterate through each element
            if len(element) == 2:
                key, e = element
                if isinstance(key, (tuple, list)):
                    if len(key) > 2: raise TypeError("[DMonomial] Format of tuples incorrect.")
                    if len(key) == 2: v, o = key
                    else: v, o = key[0], 0
                else:
                    v, o = key, 0
            if len(element) == 3:
                v,o,e = element

            ## Checking the arguments
            if (not v in ZZ) or v < 0 or v > parent.ngens():
                raise ValueError("[DMonomial] Variable index not valid.")
            
            if (not isinstance(o, (list,tuple))) and ((not o in ZZ) or o < 0):
                raise ValueError(f"[DMonomial] Order indication not valid ({o})")
            elif not isinstance(o, (list, tuple)):
                o = (ZZ(o),)

            if not isinstance(o, (list,tuple)) or len(o) != parent.noperators(): 
                raise TypeError(f"[DMonomial] Invalid input for order ({o}) for {parent.noperators()} operations")
            elif any((not oo in ZZ or oo < 0 for oo in o)):
                raise ValueError(f"[DMonomial] Order indication not valid ({o})")
            o = tuple(ZZ(oo) for oo in o)
                
            if (not e in ZZ) or e < 0: 
                raise ValueError("[DMonomial] Value for exponent not value")
            
            if e != 0:
                self._variables[(ZZ(v), o)] = self._variables.get((ZZ(v), o), ZZ.zero()) + ZZ(e)
        super().__init__(parent)

    def _mul_(self, other: DMonomial) -> DMonomial:
        # We assume the object is a DMonomial since it has passed the coercion system
        # We also assume same parent
        new_dict = self._variables.copy()
        for (k,v) in other._variables.items():
            new_dict[k] = new_dict[k] + v if (k in new_dict) else v
        return self._parent.element_class(self._parent, new_dict)
    
    ##############################################################################
    ### PROPERTY METHODS
    ##############################################################################        
    def is_one(self) -> bool: #: Checker for the one (i.e., no variables in the dictionary) 
        return len(self._variables) == 0
    
    def is_variable(self) -> bool: #: Checker for a variable (i.e., only one element in the dictionary and degree 1)
        return len(self._variables) == 1 and next(iter(self._variables.items()))[1] == 1
    
    ##############################################################################
    ### MONOID ELEMENT METHODS --> There are none
    ############################################################################## 
    def __invert__(self) -> DMonomial:
        if self.is_one(): return self
        raise ValueError(f"The d-monomial {self} has no inverse as a monomial")

    ##############################################################################
    ### SUBGROUP ELEMENT METHODS --> There are none
    ############################################################################## 
    
    ##############################################################################
    ### MAGMA ELEMENT METHODS
    ############################################################################## 
    def is_idempotent(self) -> bool: return False

    ##############################################################################
    ### COMPUTATIONAL METHODS
    ##############################################################################
    @cached_method
    def _derivative_(self, operation: int = 0) -> tuple[tuple[DMonomial,int]]:
        r'''
            Method to compute the derivative of a monomial. 
            
            Due to the Leibniz tule, this is a sum, so we return a tuple of monomials that appear in the derivative with the coefficient.
            This is valid for any derivation, since the differential variables do not concrete into any further operation.

            EXAMPLES::

                sage: from dalgebra.dpolynomial.dmonoids import *
                sage: MM = DMonomialMonoid(2, "a", "b")
                sage: a,b = MM.gens()
                sage: a[5]
                a_2_0
                sage: a[5]._derivative_(0)
                ((a_3_0, 1),)
                sage: a[5]._derivative_(1)
                ((a_2_1, 1),)
                sage: (a[(0,0)]^2*b[1]^3)._derivative_(1)
                ((a_0_0*a_0_1*b_0_1^3, 2), (a_0_0^2*b_0_1^2*b_0_2, 3))
        '''
        result = list()
        for (v, o), e in self._variables.items():
            copy = self._variables.copy()
            od = list(o); od[operation] += 1; od = tuple(od)
            copy[(v, od)] = 1
            if e == 1: copy.pop((v, o))
            else: copy[(v,o)] = e - 1
            result.append((self._parent.element_class(self._parent, copy), e))

        return tuple(result)
    
    @cached_method
    def _shift_(self, operation: int = 0) -> DMonomial:
        r'''
            Method to compute the derivative of a monomial. 
            
            Since shifts operations are homomorphisms, then the output is a DMonomial with shifted indices
        '''
        copy = self._variables.copy()
        for (v, o) in self._variables:
            od = list(o); od[operation] += 1; od = tuple(od)
            copy[(v,od)] = copy.pop((v,od))

        return self._parent.element_class(self._parent, copy)
    
    @cached_method
    def _inverse_(self, operation: int = 0) -> DMonomial:
        r'''
            Tries to get the previous element of an operation.

            It only works when we have a variable, otherwise,  we would need more information.
        '''
        if not self.is_variable():
            raise TypeError("Impossible to invert an operation for a non-variable")
        v = next(iter(self._variables))
        if v[1][operation] != 0:
            raise ValueError("Impossible to invert an operation that has not been applied")
        new_orders = list(v[1]); v[1][operation] -= 1; new_orders = tuple(new_orders)
        return self._parent.element_class(self._parent, (((v[0], new_orders), 1),))
    
    @cached_method
    def variables(self) -> set[DMonomial]:
        r'''
            Return a set of variables (i.e., Monomials with only 1 element in the dictionary with degree 1) 
        '''
        return set(self._parent.gens()[v[0]][v[1]] for v in self._variables.keys())
    
    @cached_method
    def orders(self, operation:int = -1) -> dict[int, int]: #: Compute the orders for each variable
        output = dict()
        for (v,o) in self._variables:
            output[v] = max(output.get(v, -1), o[operation] if operation != -1 else sum(o))
        
        return output
    
    @cached_method
    def order(self, variable: int , operation: int = -1): #: Get the order for a particular variable
        return self.orders(operation).get(variable, -1)
    
    @cached_method
    def lorders(self, operation: int = -1) -> dict[int, int]: #: Compute the lower orders for each variable
        output = dict()
        for (v,o) in self._variables:
            output[v] = min(output.get(v, self.order(v, operation)), o[operation] if operation != -1 else sum(o))
        
        return output
    
    @cached_method
    def lorder(self, variable: int , operation: int = -1): #: Get the lower order for a particular variable
        return self.lorders(operation).get(variable, -1)

    @cached_method
    def degree(self, variable: DMonomial = None) -> int: #: Method to get the degree of a variable (0 if not present)
        if variable != None:
            return self._variables.get(next(iter(variable._variables)), ZZ(0))
        else:
            return sum(self._variables.items())
        
    ##############################################################################
    ### MAGIC METHODS
    ##############################################################################
    @cached_method
    def __hash__(self) -> int: #: hashing the dictionary using the tuples of items
        return hash(tuple(sorted(self._variables.items())))
    
    def __eq__(self, other: DMonomial) -> bool:
        if other == 1: return self.is_one()
        
        if isinstance(other, DMonomial): # the equality goes through the dictionary
            return self._variables == other._variables
        else:
            return NotImplemented
    def __ne__(self, other: DMonomial) -> bool: return not (self == other)

    @cached_method
    def __repr__(self) -> str:
        if self.is_one():
            return "1"
        
        variable_names = self._parent.variable_names()
        elements = sorted(self._variables.items())
        return "*".join(f"{variable_names[v]}_{'_'.join(str(oo) for oo in o)}{f'^{e}' if e != 1 else ''}" for ((v,o),e) in elements)
    
    def __str__(self) -> str: return repr(self)
   
class DMonomialGen:
    def __init__(self, parent: DMonomialMonoid, name: str, *, index: int = -1):
        if(not isinstance(parent, DMonomialMonoid)):
            raise TypeError("The DPolynomialGen must have a ring of polynomial with an operator as parent")

        self.index_map = IndexBijection(parent.noperators())
        self._name = name
        self._parent = parent
        self._output = {}

        self._index = index if index != -1 else parent.variable_names().index(name)

    #########################################################################
    ### GETTER METHODS
    #########################################################################
    def variable_name(self) -> str:
        r'''
            Method that returns the variable name of ``self``
        '''
        return self._name

    #########################################################################
    ### COMPUTATIONAL METHODS
    #########################################################################
    def contains(self, element: DMonomial) -> bool:
        r'''
            Method to know if an object can be generated using ``self``.

            This method analyzes the string associated with ``element`` to determined
            if it is of the appropriate shape to be generated by ``self``.

            INPUT:

            * ``element``: the element to be checked.
            
            OUTPUT:

            ``True`` if the string of the element is of the shape ``X_Y`` where ``X`` is the 
            value of ``self._name``.
        '''
        try:
            element = self._parent(element) # Casting to DMonomial
            if len(element._variables) != 1: return False
            (v, _), e = next(iter(element._variables.items()))
            return  v == self._index and e == 1
        except:
            return False
        
    def index(self, element: DMonomial, as_tuple : bool = None) -> int | tuple[int]:
        r'''
            Method to know the index to generate ``element`` using ``self``.

            This method analyzes the string associated with ``element`` to determined
            the appropriate index to generated ``element`` using ``self``.

            INPUT:

            * ``element``: the element to be checked.
            
            OUTPUT:

            Assumed the string form of ``X_Y`` from :func:`contains`, this method returns
            the numerical value of ``Y`` or an error if not possible.
        '''
        as_tuple = self._parent.noperators() > 1 if as_tuple is None else as_tuple # defaulting value for as_tuple
        if(self.contains(element)):
            element = self._parent(element) # Casting to DMonomial --> It is a variable
            
            index = next(iter(element._variables.keys()))[1] ## This gets the order tuple
            if self._parent.noperators() > 1 and not as_tuple:
                index = self.index_map.inverse(index)
            elif self._parent.noperators() == 1 and not as_tuple:
                index = index[0]
            return index

    ###################################################################################
    ### MAGIC METHODS
    ###################################################################################
    def __eq__(self, other: DMonomialGen) -> bool:
        if not isinstance(other, DMonomialGen): return False
        return (self._index, self._parent) == (other._index, other._parent)
    
    def __ne__(self, other: DMonomialGen) -> bool:
        return not (self == other)
    
    def __hash__(self) -> int:
        return hash((self._index, self._parent))
    
    def __getitem__(self, i : int | tuple[int]) -> DMonomial:
        if self._parent.noperators() > 1 and not isinstance(i, (list,tuple)):
            i = self.index_map(i)
        elif self._parent.noperators() > 1 and len(i) != self._parent.noperators():
            raise ValueError("Incorrect indices for an element")
        elif self._parent.noperators() == 1 and not isinstance(i, (list,tuple)):
            i = (i,)

        return self._parent.element_class(self._parent, [(self._index, tuple(i), 1)])

    def __contains__(self, other: DMonomial) -> bool:
        return self.contains(other)

    def __repr__(self) -> str:
        return self._name+'_*'
    
    def __str__(self) -> str:
        return repr(self)

    def _latex_(self) -> str:
        from sage.misc.latex import latex_variable_name
        return latex_variable_name(self._name + "ast" if "_" in self._name else "_ast")

RWOPolynomialGen = DMonomialGen #: alias for DMonomialGen (used for backward compatibility)

class DMonomialMonoid(Parent):
    r'''
        Class for the monoid generated by some d-variables.

        A d-variable can be seen as a variable indexed by several indices, indicating several operations (either shifts or derivations)
        over a fully independent variable (i.e., no relation or reduction after applying these operations).

        This form a commutative monoid (i.e., a set with a commutative associative operation `*` and a unit element).

        Then, a :class:`DPolynomialRing_Monoid` is a free `\mathbb{K}`-module over a :class:`DMonomialMonoids`. All these structures
        should help SageMath to do all conversions between the elements.

        EXAMPLES::

            sage: from dalgebra.dpolynomial.dmonoids import DMonomialMonoid
            sage: MM = DMonomialMonoid(2, "a", "b"); MM
            Monoid of d-monomials with 2 operations with generators (a_*, b_*)
            sage: a, b = MM.gens()
            sage: a[(2,3)]
            a_2_3
            sage: b[10]
            b_0_3
            sage: a[(0,0)]^2*b[1]^3
            a_0_0^2*b_0_1^3
            sage: MM.one()
            1

        We can see that the implementation of a DMonomialMonoid pass all the tests niherited by the category::

            sage: from sage.misc.sage_unittest import TestSuite
            sage: TestSuite(MM).run()
            sage: TestSuite(MM._an_element_()). run()
    '''
    Element = DMonomial

    def __init__(self, noperators: int, *names: str, category=None):
        if len(names) == 0: raise ValueError("Monoid with 0 generators is not allowed")
        if (not noperators in ZZ) or noperators <= 0: raise ValueError("Number of operations (i.e., indices) must be a positive integer")
        self.__noperators = ZZ(noperators)
        self.__variable_names = tuple(names)

        self.__gens = tuple(DMonomialGen(self, name, index=i) for (i,name) in enumerate(names))

        super().__init__(category=(_CommutativeMonoids, category) if category != None else _CommutativeMonoids)

    ################################################################################
    ### ATTRIBUTE METHODS
    ################################################################################
    def variable_names(self) -> tuple[str]:
        return self.__variable_names
    
    def noperators(self) -> int:
        return self.__noperators
    
    def gens(self) -> DMonomialGen:
        return self.__gens
    
    def ngens(self) -> int: return len(self.gens())

    ################################################################################
    ### MONOIDS METHODS (from Monoids.ParentMethods)
    ################################################################################
    def semigroup_generators(self) -> LazyFamily:
        def _gen_from_index(tuple):
            if tuple[0] == 0:
                return self.one()
            return self.gens()[tuple[0]-1][tuple[1]]
        return LazyFamily(cartesian_product([NN, cartesian_product(self.ngens()*[NN])]), _gen_from_index)

    def submonoid(self, generators: Collection[str | int], category=None) -> DMonomialMonoid:
        generators = list(set([g if isinstance(g, str) else self.__variable_names[g] for g in generators]))
        return DMonomialMonoid(self.__noperators, *generators, category=category)
    
    def one(self) -> DMonomial:
        return self.element_class(self, tuple())
    
    def _an_element_(self) -> DMonomial:
        return self.one()
    
    ################################################################################
    ### MAGIC METHODS
    ################################################################################
    def __repr__(self) -> str:
        return f"Monoid of d-monomials with {self.noperators()} with generators {self.gens()}"
    def __str__(self) -> str: return repr(self)
    def __eq__(self, other: DMonomialMonoid) -> bool:
        if not isinstance(other, DMonomialMonoid): return False
        return (self.__noperators, self.variable_names()) == (other.__noperators, other.variable_names())
    def __ne__(self, other: DMonomialMonoid) -> bool: return not (self == other)
    def __hash__(self) -> int:
        return hash((self.__noperators, self.variable_names()))

__all__ = [
    "IndexBijection", "DMonomialMonoid"
]