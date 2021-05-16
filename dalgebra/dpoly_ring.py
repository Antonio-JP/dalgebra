
from sage.categories.all import Morphism, Rings
from sage.categories.pushout import pushout
from sage.categories.pushout import ConstructionFunctor

#Private variables for module
_Rings = Rings.__classcall__(Ring)

class DiffPolynomialRing ():
    r'''
        EXAMPLES::

            sage: from dalgebra import *
    '''
    
    Element = None
        
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        pass
    
    def __init__(self, base):
        pass

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_(self, S):
        pass
        
    def _pushout_(self, S):
        pass
        
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, *args, **kwds):
        pass
            
    def gens(self):
        pass
    
    def ngens(self):
        r'''
            TODO: do the documentation
        '''
        return len(self.gens())
            
    def construction(self):
        pass
        
    def __contains__(self, X):
        pass
    
    #################################################
    ### Magic python methods
    #################################################
    def __hash__(self):
        pass

    def __eq__(self, other):
        pass
     
    ## Other magic methods   
    def _repr_(self):
        pass

    def _latex_(self):
        pass
            
    #################################################
    ### Integral Domain and Ring methods
    #################################################
    def _an_element_(self):
        pass
    
    def random_element(self,**kwds):
        pass

    def characteristic(self):
        pass
        
    def base_ring(self):
        pass
        
    def is_field(self, **kwds):
        pass
        
    def is_finite(self, **kwds):
        pass
        
    def is_noetherian(self, **kwds):
        pass

class DPolyRingFunctor (ConstructionFunctor):
    def __init__(self, variables):
        self.__variables = variables
        super().__init__(_Rings,_Rings)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _apply_functor(self, x):
        return DiffPolynomialRing(x,self.__variables)
        
    def _repr_(self):
        return "DiffPolynomialRing(*,%s)" %(self.__variables)
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.__variables == self.__variables)

    def merge(self, other):
        pass

    def variables(self):
        return self.__variables