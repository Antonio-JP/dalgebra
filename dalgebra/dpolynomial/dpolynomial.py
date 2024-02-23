from __future__ import annotations

from sage.all import ZZ

class DPolynomialRing_new:
    pass

class DMonomial:
    r'''
        Class to represent a differential monomial. 

        We represent a differential monomial in a sparse way where we have a map
        `(v, o) -> e`,
        where `v` is the index of a variable, `o` is the order (i.e., integer non-negative),
        and `e` is the exponent in the monomial.

        We allow to provide the input in dictionary format or tuple format. In the tuple format, we allow 
        the key to be just a number, representing the element `(v, 0)`.

        We *do not* allow to modify this object once is created.
    '''
    def __init__(self, parent: DPolynomialRing_new, input: dict[tuple[int,int],int] | tuple[tuple[int,int]|int, int]):
        self.__variables = dict()
        self.__parent = parent
        if isinstance(input, dict):
            for key in input:
                if isinstance(key, tuple):
                    if len(key) != 2: raise TypeError("[DMonomial] Key in dictionary of incorrect length")
                    v, o = key
                    if (not v in ZZ) or v < 0 or v > parent.ngens():
                        raise ValueError("[DMonomial] Variable index not valid.")
                    elif (not o in ZZ) or o < 0: 
                        raise ValueError("[DMonomial] Order indication not valid.")
                    
                    e = input[key]
                    if (not e in ZZ) or e < 0: raise ValueError("[DMonomial] Value for exponent not value")
                    if e != 0: # we have somethig to add
                        self.__variables[(ZZ(v), ZZ(o))] = ZZ(e)
        elif isinstance(input, (tuple, list)):
            for element in input:
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
            if (not v in ZZ) or v < 0 or v > parent.ngens():
                raise ValueError("[DMonomial] Variable index not valid.")
            elif (not o in ZZ) or o < 0: 
                raise ValueError("[DMonomial] Order indication not valid.")
            elif (not e in ZZ) or e < 0: 
                raise ValueError("[DMonomial] Value for exponent not value")
            
            if e != 0:
                self.__variables[(ZZ(v), ZZ(o))] = ZZ(e)

    def parent(self):
        return self.__parent

    ## Multiplication of monomials
    def __mul__(self, other: DMonomial):
        if not isinstance(other, DMonomial): raise TypeError("[DMonomial] Multiplication only valid with other monomials.")
        if self.parent() != other.parent(): raise TypeError("[DMonomial] Multipliaction of monomials only valid with same parent.")
        keys = set(self.__variables.keys()).union(other.__variables.keys())
        return DMonomial(self.parent(), {key: self.__variables.get(key, 0)+other.__variables.get(key, 0) for key in keys})
    
    def __derivative__(self) -> tuple[DMonomial]:
        r'''
            Method to compute the derivative of a monomial. Due to the Leibniz tule, this is a sum, so we return a tuple of monomials that 
            appear in the derivative
        '''
                    