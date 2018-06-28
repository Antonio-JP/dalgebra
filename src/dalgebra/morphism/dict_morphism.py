
################################################################
###
### File for the class DictMorphism
###
### A DictMorpism is a morphism defined over the ring
### of rational functions over some ring structure.
###
### The idea is to have a basic morphism for the elements
### of the base ring and a dictionary for each of the generators
################################################################

from sage.categories.morphism import is_Morphism, Morphism;
from sage.categories.homset import Homset, Hom;
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing;
from sage.misc.misc_c import prod;

class DictMorphism(Morphism):
	def __init__(self, base, morph, dic):
		'''
		DictMorphism is a morphism class within the field of rational
		functions of a ring using a base morphism and a dictionary
		for the image of the generators.

		INPUT:
			- base: a field in top of which we will consider the
			field of rational functions.
			- morph: morphism from base to base.
			- dic: a dictionary (var -> value). It is necessary
			that var are generators of the field of rational
			functions we will consider and value elements of that
			field.
		'''
		## Checking the input
		if((not hasattr(base, "is_field")) or (not base.is_field())):
			raise TypeError("The base element for a DictMorphism must be a field");

		if(not (is_Morphism(morph) and morph.domain() is base and morph.codomain() is base)):
			raise TypeError("The base-morphism for a DictMorphism must be an endomorphism of 'base'");
		self.__morph = morph;

		## We cast the variables to strings to avoid problems of types
		new_dic = {str(el) : dic[el] for el in dic};

		## We build the field of rational functions
		F = PolynomialRing(base, tuple(new_dic.keys())).fraction_field();
		self.__dic = {F(el) : F(dic[el]) for el in new_dic};

		Morphism.__init__(self, Hom(F, F));

	def _repr_type(self):
        	return "DictMorphism";

    	def _call_(self, x):
		## Casting element x to the domain
		F = self.domain();
		x = F(x);
		
		## Differentiating between numerator and denominator
		n = x.numerator(); d = x.denominator();

		## Computing the image of each part
		if(self.domain().ngens() == 1):
			im_gen = self.__dic[F.gens()[0]];
			## Univariate case
			coeffs_n = n.coefficients(sparse=False); coeffs_d = d.coefficients(sparse=False);
			im_n = sum([coeffs_n[i]*(im_gen**i) for i in range(len(coeffs_n))], F.zero());
			im_d = sum([coeffs_d[i]*(im_gen**i) for i in range(len(coeffs_d))], F.zero());
		else:
			## Multivariate case
			m_var = [self.__dic[el] for el in F.gens()];
			im_n = sum([self.__morph(n.dict()[mon])*prod(m_var[i]**mon[i] for i in range(F.ngens())) for mon in n.dict()], F.zero());
			im_d = sum([self.__morph(d.dict()[mon])*prod(m_var[i]**mon[i] for i in range(F.ngens())) for mon in d.dict()], F.zero());

		## Returning the quotient of both images
        	return im_n/im_d;

    	def is_identity(self):
		return False;
