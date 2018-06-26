
from sage.all import *;

from sage.categories.morphism import is_Morphism;
from sage.categories.morphism import IdentityMorphism;

from dalgebra.morphism.zero_morphism import ZeroMorphism;

class SkewField(Field):
	Element = None;

	def __init__(self,base, auto=None, der=None):
		'''
		Builder of a Skew-differential field. We require the base field
		where the elements will belong.

		An automorphism 'auto' and a skew-derivation 'der' must be also 
		provided. A skew-derivation is an endomorphism such that:
			d(ab) = d(a)b + s(a)d(b)
		where d is the derivation and s an automorphism over the field.

		WARNING: As we can not check the automorphism properties or 
		the skew-Leibniz rule for the derivation, we encourage
		the user to be careful when adding those.

		INPUT:
			- 'base': the basic field to add the differential structure
			- 'auto': automorphism. By default the identity map
			- 'der': skew-derivation. By default the zero map
		'''
		## Building of the Field class with the appropriate base
		Field.__init__(self,base);

		## Checking the argument 'auto'
		if(auto is None):
			_auto = IdentityMorphism(self.base());
		elif(is_Morphism(auto) and auto.domain() is self.base() and auto.codomain() is self.base()):
			_auto = auto;
		else:
			raise TypeError("Invalid automorphism given. Expected a morphism from %s to itself.\n\t- Got: %s" %(self.base(), auto));

		## Checking the argument 'der'
		if(der is None):
			_der = ZeroMorphism(self.base());
		elif(is_Morphism(der) and der.domain() is self.base() and der.codomain() is self.base()):
			_der = der;
		else:
			raise TypeError("Invalid skew-derivation given. Expected a morphism from %s to itself.\n\t- Got: %s" %(self.base(), der));
		## After all checkings, assigning the methods to attributes
		self.__s = _auto;
		self.__d = _der;

		## Registering the conversion to the base ring
		morph = _SimpleMorphism(self, self.base());
		self.base().register_conversion(morph);

	def shift(self, element):
		element = self(element);
		return self.__s(element);

	def derivative(self, element):
		element = self(element);
		return self.__d(element);

	def __repr__(self):
		return "Skew-differential Field with base %s.\n\t- Shift:\t%s\n\t- Derivation:\t%s" %(self.base(), self.__s, self.__d);

	def __contains__(self, element):
		if(isinstance(element, SkewField.Element)):
			return (element.parent() is self);
		return element in self.base();
	
	## SAGE categories methods
	def _coerce_map_from_(self, S):
		return (self.base().has_coerce_map_from(S));

	def _element_constructor_(self, *args):
		if(len(args) > 0):
			if(args[0] is self):
				return SkewField.Element(self,self.base()(args[1]));
			return SkewField.Element(self,self.base()(args[0]));
		raise TypeError("The input for 'element_constructor' is not recognized\n\tInput: %s" %args);

	## Ore-algebra methods
	def ore_algebra(self):
		raise NotImplementedError();

class _SkewFieldElement(FieldElement):
	def __init__(self, parent, el):
		if(not isinstance(parent, SkewField)):
			raise TypeError("Parent of a SkewFieldElement must be a SkewField\n\t- Got: %s" %parent);

		if(not el in parent.base()):
			raise ValueError("Element to create is not in the base field of %s\n\t- Got: %s (%s)" %(parent, el, el.parent()));
		self.__element = parent.base()(el);

		FieldElement.__init__(self, parent);

	def _original(self):
		return self.__element;

	## Arithmetic methods
	def _add_(self, other):
		R = self.parent().base();
		return self.parent()(R(self)+R(other));
	def _sub_(self, other):
		R = self.parent().base();
		return self.parent()(R(self)-R(other));
	def _mul_(self, other):
                R = self.parent().base();
                return self.parent()(R(self)*R(other));
	def _div_(self, other):
                R = self.parent().base();
                return self.parent()(R(self)/R(other));
	def _pow_(self, other):
                R = self.parent().base();
                return self.parent()(R(self)**other);
	
	## Equality methods
	def __eq__(self, other):
                R = self.parent().base();
                return R(self)==other;
	def __hash__(self):
		return hash(self._original());
	def __nonzero__(self):
		return self._original() == 0;	

	## Representation methods
	def __repr__(self):
		return repr(self._original());

	## Proper methods
	def derivative(self):
		return self.parent()(self.parent().derivative(self));

	def shift(self):
		return self.parent()(self.parent().shift(self));

SkewField.Element = _SkewFieldElement;

class _SimpleMorphism (sage.categories.map.Map):
	def __init__(self, domain, codomain):
		super(_SimpleMorphism, self).__init__(domain, codomain);
        
	def _call_(self, p):
		if(p in self.domain()):
			p = self.domain()(p);
			return self.codomain()(p._original());
		raise TypeError("Impossible perform conversion of %s from %s to %s" %(p, self.domain(), self.codomain()));
