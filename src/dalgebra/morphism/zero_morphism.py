
from sage.categories.morphism import is_Morphism, Morphism;
from sage.categories.homset import Homset, Hom;

class ZeroMorphism(Morphism):

    def __init__(self, parent):

        if not isinstance(parent, Homset):
	    self.__zero = parent.zero();	    
            parent = Hom(parent, parent);
	else:
	    self.__zero = parent.codomain().zero();

        Morphism.__init__(self, parent);

    def _repr_type(self):
        return "Zero";

    def _call_(self, x):
        return self.__zero;

    def _call_with_args(self, x, args=(), kwds={}): 
        if len(args) == 0 and len(kwds) == 0:
            return self.__zero;
        C = self._codomain
        if C._element_init_pass_parent:
            return C._element_constructor(C, self.__zero, *args, **kwds)
        else:
            return C._element_constructor(self.__zero, *args, **kwds)

    def __mul__(left, right):
        if not isinstance(right, Map):
            raise TypeError("right (=%s) must be a map to multiply it by %s"%(right, left))
        if not isinstance(left, Map):
            raise TypeError("left (=%s) must be a map to multiply it by %s"%(left, right))
        if right.codomain() != left.domain():
            raise TypeError("self (=%s) domain must equal right (=%s) codomain"%(left, right))
        return ZeroMorphism(Hom(rigth.domain(),left.codomain()));

    def _pow_int(self, n):
        return self

    def is_identity(self):
        return False;

    def is_surjective(self):
        return False;

    def is_injective(self):
        return False;

