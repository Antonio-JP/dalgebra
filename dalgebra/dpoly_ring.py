
from sage.all import latex, cached_method, ZZ, diff, prod
from sage.categories.all import Morphism, Rings
from sage.categories.pushout import ConstructionFunctor
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialGen
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense, InfinitePolynomial_sparse

#Private variables for module
_Rings = Rings.__classcall__(Rings)

def is_InfinitePolynomial(element):
    R = element.parent()
    return (isinstance(R, InfinitePolynomialRing_dense) or isinstance(R, InfinitePolynomial_sparse))

class DiffPolynomialRing (InfinitePolynomialRing_dense):
    r'''
        EXAMPLES::

            sage: from dalgebra import *
    '''
    
    Element = None
    __CACHED_RINGS = {}
        
    @staticmethod
    def __classcall__(cls, *args, **kwds):
        if(len(args) == 1 and type(args) in (list, tuple)):
            args = args[0]
        
        base, names = (None, None)
        if(len(args) == 1 and isinstance(args, InfinitePolynomial_dense)):
            base = args[0].base()
            names = args[0]._names
        else:
            base = kwds.get("base", args[0])
            names = kwds.get("names", args[1])

        key = (base, names)
        if(not (key in DiffPolynomialRing.__CACHED_RINGS)):
            DiffPolynomialRing.__CACHED_RINGS[key] = DiffPolynomialRing(base, names)
        return DiffPolynomialRing.__CACHED_RINGS[key]
    
    def __init__(self, base, names):
        super().__init__(base, names, 'deglex')

        # cache variables
        self.__cache_derivatives = {}

        # registering conversion to simpler structures
        current = self.base()
        morph = DiffPolySimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DiffPolySimpleMorphism(self, current)
            current.register_conversion(morph)

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, x):
        p = super()._element_constructor_(x)
        return DiffPolynomial(self, p)

    @cached_method
    def gen(self, i=None):
        r'''
            Override method to create the `i^{th}` generator (see method 
            :func:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse.gen`).
        '''
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return DiffPolynomialGen(self, self._names[i])
                
    def construction(self):
        return DPolyRingFunctor(self._names), self._base
    
    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds):
        res = super().__call__(*args, **kwds)
        return DiffPolynomial(self, res)

    ## Other magic methods   
    def __repr__(self):
        return "Differential ring of polynomials in %s over %s" %(self._names, self._base)

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self):
        return self(1)
    
    def zero(self):
        return self(0)
    
    def random_element(self,**kwds):
        p = super().random_element(**kwds)
        return self(p)

    def derivation(self, element):
        if(element in self):
            element = self(element)
        else:
            element=self(str(element))
            
        if(element in self.base()):
            return diff(self.base()(element))
        
        if(not element in self.__cache_derivatives):
            generators = self.gens()
            if(element.is_monomial()):
                c = element.coefficients()[0]
                m = element.monomials()[0]
                v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                v = [self(str(el)) for el in v]
                base = c*prod([v[i]**(d[i]-1) for i in range(len(v))], self.one())

                first_term = self.derivation(c)*self(str(m))
                second_term = self.zero()
                for i in range(len(v)):
                    to_add = prod([v[j] for j in range(len(v)) if j != i], self.one())
                    for g in generators:
                        if(g.contains(v[i])):
                            to_add *= g[g.index(v[i])+1]
                            break
                    second_term += to_add
                self.__cache_derivatives[element] = first_term + base*second_term
            else:
                c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                self.__cache_derivatives[element] = sum(self.derivation(c[i])*m[i] + c[i]*self.derivation(m[i]) for i in range(len(m)))
                
        return self.__cache_derivatives[element]

    def eval(self, element, *args, **kwds):
        raise NotImplementedError("Evaluation not yet implemented")
                                
class DiffPolynomialGen (InfinitePolynomialGen):
    r'''
        TODO: do documentation
    '''
    def __init__(self, parent, name):
        if(not (isinstance(parent, DiffPolynomialRing))):
            raise TypeError("The DiffPolynomialGen must have a DiffPolynomialRing parent")
        super().__init__(parent, name)

    def __getitem__(self, i):
        return self._parent(super().__getitem__(i))

    def contains(self, element):
        name = str(element)
        spl = name.split("_")
        first = "_".join(spl[:-1])
        return first == self._name

    def index(self, element):
        if(self.contains(element)):
            return int(str(element).split("_")[-1])


class DiffPolynomial (InfinitePolynomial_dense):
    r'''
        TODO: do documentation
    '''
    def __init__(self, parent, polynomial):   
        if(is_InfinitePolynomial(polynomial)):
            polynomial = polynomial.polynomial()
        super().__init__(parent, polynomial)

    # Magic methods
    def __call__(self, *args, **kwargs):
        return self.parent().eval(self, *args, **kwargs)

    # Arithmetic methods
    def _add_(self, x):
        return DiffPolynomial(self.parent(), super()._add_(x))
    def _sub_(self, x):
        return DiffPolynomial(self.parent(), super()._sub_(x))
    def _mul_(self, x):
        return DiffPolynomial(self.parent(), super()._mul_(x))
    def _rmul_(self, x):
        return DiffPolynomial(self.parent(), super()._rmul_(x))
    def _lmul_(self, x):
        return DiffPolynomial(self.parent(), super()._lmul_(x))
    def __pow__(self, n):
        return DiffPolynomial(self.parent(), super().__pow__(n))

    # Differential methods
    @cached_method
    def derivative(self, times=1):
        if((not times in ZZ) or (times < 0)):
            raise ValueError("A differential polynomial can not be differentiated %s times" %times)
        elif(times == 0):
            return self
        elif(times > 1):
            return self.derivative(times=times-1).derivative()
        else:
            return self.parent().derivation(self)

DiffPolynomialRing.Element = DiffPolynomial

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

class DiffPolySimpleMorphism (Morphism):
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        if(p.degree() == 0):
            return self.codomain()(p.coefficients()[0])

        return self.codomain(str(p))