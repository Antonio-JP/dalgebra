from __future__ import annotations
r'''
    Module for monomial extensions on D-Algebra.

    Let `(K, (d_1,\ldots,d_n))` be a D-field (a field with several operations - both 
    derivations and shifts). We say that `t` is a monomial over this D-field if it 
    is a transcendental element over `K` and, for all `i =1,\ldots n`, `d_i(t) \in K[t]`.

    In this cases, we know that `d_i` are closed in `K[t]`: let `p(t) \in K[t]`, then

    * If `d` is a derivation, then `d(p(t)) = \partial_t(p(t)) + \kappa_d(p(t))`, where 
      `\partial_t` is the partial derivative, and `\kappa_d` is the derivation where
      all coefficients are differentiated using `d` over `K`, but `t` remains intact.
    * If `d` is a shift, then `d(p(t)) = \kappa_d(p(t))(d(t))`.

    This module aims to provide a full implementation as univariate polynomials and their
    fraction fields of monomial extensions. It is of crucial importance that we can iterate 
    this construction building a "tower of monomials".  
'''

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex, latex_variable_name
from sage.rings.infinity import Infinity as oo
from sage.rings.polynomial.multi_polynomial_ring import MPolynomialRing_base
from sage.rings.polynomial.polynomial_ring import PolynomialRing_generic
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Iterator

from ..dring import AdditiveMap, DRings, DFractionField

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)

## Notes for module:
#  - DMonomialFactory -> factory to create a tower of monomials provided a set of variables 
#    and images w.r.t. the operations.
#  - DMonomial_Element -> implementation of a univariate polynomial.
#  - DMonomial_Parent -> implementation of the polynomial ring `K[t]`
#  - DMonomialFunctor -> ConstructionFunctor for D-monomial extensions.
#  - DMM_ParentToBase -> Conversion morphism from DMonomial_Parent to their bases
#  - DMM_BaseToPArent -> Coercion morphism from a base field to DMonomial_Parent
#  - DMM_BetweenBases -> Coercion morphism between two DMonomial_Parent with different bases
## After these classes, everything else should be done by SageMath code. Things to be checked 
#  in the future
#  - Vectors -> free modules over these rings and fields
#  - Matrices -> matrices ring over these ring and fields
#  - DElliptic -> how these DMonomial interact with DElliptic?


#####################################
### FACTORY CLASS
#####################################
class DMonomialFactory (UniqueFactory):
  pass

DMonomial = DMonomialFactory("dalgebra.dextension.dmonomial.DMonomial")

#####################################
### ELEMENT CLASS
#####################################
class DMonomial_Element (Element):
  r'''
    Implementation of a DMonomial Element

    This is a normal implementation of a univariate polynomial in dense 
    representation, i.e., the coefficients are stored in a list
    where the empty coefficients are represented with zeros.

    INPUT:

    * ``parent``: the parent of this polynomial. It **has** to be a 
      DMonomial_Parent.
    * ``data``: the coefficients of the polynomial. It can be a list/tuple of elements
      that will be interpreted as the coefficients sorted by degree; or a dictionary where
      the keys will be the degree and the values the corresponding coefficients. In any case
      the coefficients must be already casted into ``parent.base()``.
  '''
  def __init__(self, parent: DMonomial_Parent, data: list[Element] | tuple[Element] | dict[Element]):
    ## Initializing the Element structure
    super().__init__(parent)

    if isinstance(data, dict): # special case of dictionary
      degree = max(data)+1 if len(data) > 0 else 0
      data = tuple(data.get(i,self.parent().zero()) for i in range(degree+1))
    
    ## We clean the data if the coefficients are zero
    i = len(data)
    while i > 0 and data[i-1] == 0:
      i -= 1
    self.__coefficients = data[:i]
    
    ## Other cached values
    self.__algebraic = None

  ## Getter and attribute methods
  def degree(self) -> int:
    if not self.__coefficients:
      return -oo
    return len(self.__coefficients)-1
  
  def leading_coefficient(self) -> Element:
    return self.__coefficients[-1]
  
  lc = leading_coefficient

  def constant_coefficient(self) -> Element:
    return self.__coefficients[0]
  
  cc = constant_coefficient

  def monomials(self) -> tuple[DMonomial_Element]:
    v = self.parent().gen()
    return tuple(v**i for i,c in enumerate(self.__coefficients) if c != 0)

  def coefficients(self, sparse=True) -> tuple[Element]:
    if sparse:
      return tuple(c for c in self.__coefficients if c != 0)
    else:
      return tuple(self.__coefficients)
    
  def mons_cons_iter(self) -> Iterator[tuple[DMonomial_Element,Element]]:
    return zip(self.monomials(), self.coefficients())

  def coefficient(self, index: int) -> Element:
    try:
      return self.__coefficients[index]
    except IndexError:
      return self.parent().base().zero()
  
  def __getitem__(self, i: int) -> Element:
    return self.coefficient(i)
  
  def numerator(self) -> DMonomial_Element:
    return self
  
  def denominator(self) -> DMonomial_Element:
    return self.parent().one()
  
  def is_zero(self) -> bool:
    return not self.__coefficients
  
  def is_one(self) -> bool:
    return len(self.__coefficients) == 1 and self[0] == 1
  
  def is_constant(self) -> bool:
    return len(self.__coefficients) <= 1
  
  def is_monomial(self) -> bool:
    coeffs = self.coefficients()
    return len(coeffs) == 1 and coeffs[0] == self.parent().base().one()
  
  @cached_method
  def algebraic(self) -> Element:
    return self.parent().to_sage()(self)

  def to_sage(self) -> Element:
    return self.algebraic()
  
  ## Useful derivation methods
  @cached_method
  def kappa(self, operation: int = 0) -> DMonomial_Element:
    return self.parent().element_class(
      self.parent(),
      [c.operation(operation) for c in self.__coefficients] # apply the operation to each coefficient
    )

  @cached_method
  def partial(self) -> DMonomial_Element:
    if self.is_constant():
      return self.parent().zero()
    return self.parent().element_class(
      self.parent(), 
      [i*self.__coefficients[i] for i in range(1, self.degree()+1)]
    )
  
  ## Other operational methods
  def conditions_to_zero(self) -> tuple[tuple[DMonomial_Element,Element]]:
    return tuple((m,c) for (m,c) in self.mons_cons_iter())

  ## Arithmetic methods
  def _add_(self, other: DMonomial_Element) -> DMonomial_Element:
    if self.is_zero():
      return other
    elif other.is_zero():
      return self
    return self.parent().element_class(
      self.parent(),
      [self[i] + other[i] for i in range(max(self.degree(), other.degree())+1)])
    
  def _neg_(self) -> DMonomial_Element:
    return self.parent().element_class(
      self.parent(),
      [-c for c in self.coefficients(sparse=False)]
    )

  def _sub_(self, other: DMonomial_Element) -> DMonomial_Element:
    return self + (-other)

  def _mul_(self, other: DMonomial_Element) -> DMonomial_Element:
    # TODO: add a better implementation for multiplication of polynomials
    if self.is_zero() or other.is_zero():
      return self.parent().zero()
    elif self.is_one():
      return other
    elif other.is_one():
      return self
    elif other.is_constant():
      return self.parent().element_class(
        self.parent(),
        [c*other[0] for c in self.__coefficients]
      )
    elif other.is_monomial():
      other_degree = other.degree()
      return self.parent().element_class(
        self.parent(),
        {m.degree()+other_degree : c for m,c in self.mons_cons_iter()}
      )
    else:
      return sum(((self*m)*c for (m,c) in other.mons_cons_iter()), start=self.parent().zero())

  @cached_method
  def __pow__(self, power: int) -> DMonomial_Element:
    if power == 0:
      return self.parent().one()
    elif power == 1:
      return self
    elif power < 0:
      return (~self)**(-power)
    else:
      a,A = (self**(power//2 + power % 2), self**(power//2))
      return a*A

  def __eq__(self, other) -> bool:
    if not isinstance(other, self.__class__) or other.parent() != self.parent():
      try:
        other = self.parent()(other)
      except Exception:
        return False

    return self.__coefficients == other.__coefficients

  def __ne__(self, other) -> bool:
    return not (self == other)
  
  def hash(self) -> int:
    return hash(self.__coefficients)

  ## Other functions
  def __repr__(self) -> str:
    if self.is_zero():
      return "0"
    else:
      t = self.parent().varname()
      coeffs = tuple((m.degree(),str(c)) for (m,c) in self.mons_cons_iter())

      if coeffs[0][0] == 0:
        output = coeffs[0][1]
      else:
        d,c = coeffs[0]
        output = (f"{'' if c == '1' else f'({c})' if len(c) > 1 else f'{c}'}" + 
                f"{'' if c == '1' else '*'}{t}{f'^{d}' if d > 1 else ''}")
      
      for d,c in coeffs[1:]:
        if c.startswith("-"):
          output += " - "
          c = c[1:] # we remove the minus sign
        else:
          output += (" + " + 
                f"{'' if c == '1' else f'({c})' if len(c) > 1 else f'{c}'}" + 
                f"{'' if c == '1' else '*'}{t}{f'^{d}' if d > 1 else ''}")
      return output
  
  def _latex_(self) -> str:
    return latex(self.algebraic())
      
#####################################
### PARENT CLASS
#####################################
class DMonomial_Parent (Parent):
  Element = DMonomial_Element

  def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base)] + ([category] if category is not None else [])

  def __init__(self, base : Parent, varname:str, gen_images: tuple[str], category=None):
    if not base in _Fields or not base in _DRings:
      raise TypeError(f"The base must be a field and have d-operations")
    
    ## Calling the super __init__ to stablish the categories and the main attributes
    super().__init__(base, category=tuple(self._set_categories(base, category)))

    ## Variables for cached attributes
    self.__varname = varname
    self.__algebraic = None
    self.__images = None
    self.__gen = None
    self.__operators = None

    self._initialize_algebraic()
    self._initialize_data(gen_images)

    ## Extending the operations of ``base``
    if any(el not in ("derivation", "homomorphism") for el in self.base().operator_types()):
      raise TypeError(f"DMonomial extension only valid for derivation and homomorphisms")
    self.__operators = [
      self.extend_derivation(i) if ttype == "derivation" else
      self.extend_homomorphism(i)
      for (i, ttype) in enumerate(self.base().operator_types())
    ]

  ## Initialization methods
  def _initialize_algebraic(self):
    ## We create the algebraic base structure
    self.__algebraic = PolynomialRing(self.base().to_sage(), self.varname())
    
    ## Adding coercion and conversion morphisms
    self.__algebraic.register_coercion(DMM_ParentToAlgebraic(self))
    self.register_coercion(DMM_AlgebraicToParent(self))

  def _initialize_data(self, images: tuple[str]):
    self.__images = tuple(self(self.to_sage()(img)) for img in images)

  def varname(self) -> str:
    return self.__varname
  
  def gen(self) -> DMonomial_Element:
    if self.__gen is None:
      self.__gen = self.element_class(self, [self.base().zero(), self.base().one()])
    return self.__gen
  
  def gens(self) -> tuple[DMonomial_Element]:
    return (self.gen(),)
  
  def ngens(self) -> int:
    return 1
  
  def one(self) -> DMonomial_Element:
    return self.element_class(self, [self.base().one()])
  
  def zero(self) -> DMonomial_Element:
    return self.element_class(self, [self.base().zero()])
  
  ## Derivation methods
  def extend_derivation(self, operation: int) -> AdditiveMap:
    def __derivation(element: DMonomial_Element) -> DMonomial_Element:
      return element.partial() * self.__images[operation] + element.kappa(operation) 
    
    return AdditiveMap(self, __derivation)

  def extend_homomorphism(self, operation: int) -> AdditiveMap:
    def __homomorphism(element: DMonomial_Element) -> DMonomial_Element:
      return sum(
        c.operation(operation)*self.__images[operation]**i 
        for (i,c) in enumerate(element.coefficients(sparse=False))
      )
    
    return AdditiveMap(self, __homomorphism)

  ## Coercion methods
  def _coerce_map_from_base_ring(self) -> Morphism:
    return DMM_BaseToParent(self)
  
  def construction(self) -> tuple[ConstructionFunctor, Parent]:
    return DMonomialFunctor(self.__varname, tuple(self.__images)), self.base()
  
  def fraction_field(self) -> DFractionField:
    return DFractionField(self)
  
  def change_ring(self, new_base: Parent) -> DMonomial_Parent:
    old_base = self.base()
    if isinstance(old_base, DMonomial_Parent) and (not isinstance(new_base, DMonomial_Parent)):
      new_base = old_base.change_ring(new_base)
    
    output = DMonomial(new_base, self.varname(), tuple(str(img) for img in self.__images))
    # coercion old -> new
    coercion = new_base.coerce_map_from(self.base())
    if coercion is not None:
      try:
        output.register_coercion(DMM_BetweenBases(self, output, coercion))
      except AssertionError:
        pass # the ring was already created
    # coercion new -> old
    coercion = self.base().coerce_map_from(new_base)
    if coercion is not None:
      try:
        output.register_coercion(DMM_BetweenBases(output, self, coercion))
      except AssertionError:
        pass # the ring was already created
    # conversion old -> new
    conversion = new_base.convert_map_from(self.base())
    if conversion is not None:
      try:
        output.register_conversion(DMM_BetweenBases(self, output, conversion))
      except AssertionError:
        pass # the ring was already created
    # conversion new -> old
    conversion = self.base().convert_map_from(new_base)
    if conversion is not None:
      try:
        output.register_conversion(DMM_BetweenBases(output, self, conversion))
      except AssertionError:
        pass # the ring was already created
  
  ## Representation methods
  def __repr__(self) -> str:
    return f"D-Monomial extension of {self.base()} with variable {self.varname()} extending operations by {self.__images}"

  def _latex_(self) -> str:
    return (latex(self.base()) + 
            r"[" + latex_variable_name(self.varname()) + 
            r"\mapsto (" + ", ".join(latex(img) for img in self.__images) + 
            r")]") 

  ## DRing category methods
  def operators(self) -> Collection[AdditiveMap]:
    return self.__operators

  def operator_types(self) -> tuple[str]:
    return self.base().operator_types()

  def add_constants(self, *new_constants: str) -> DMonomial_Parent:
    return self.change_base(self.base().add_constants(*new_constants))
  
  def linear_operator_ring(self) -> DMonomial_Parent:
    r'''
      Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

      This method builds the ring of linear operators on the base ring. It only works when the
      ring of operator polynomials only have one variable.
    '''
    raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

  def inverse_operation(self, element: DMonomial_Element, operation: int = 0) -> DMonomial_Element:
    raise NotImplementedError(f"The integration in these fields is not yet implemented")
    
  def _lcm_denominators(self, *_: DMonomial_Element) -> DMonomial_Element:
    return self.parent().one() # no denominators in this ring

  def to_sage(self):
    return self.__algebraic
  
#####################################
### FUNCTOR CLASS
#####################################
class DMonomialFunctor (ConstructionFunctor):
  r'''
    Class for a functor that creates a d-monomial extension.

    It receives the name of the new added variable and the images of the variable
    in a string/element format.
  '''
  def __init__(self, varname: str, images: tuple[str|Element]):
    super().__init__(_DRings,_DRings)
    self.rank = 10 # just below DPolyRingFunctor

    self.__varname = varname
    self.__images = images

  def _apply_functor(self, x):
    return DMonomial(x, self.__varname, self.__images)
  
  def _repr_(self) -> str:
    return f"DMonomial(*, {self.__varname}, {self.__images})"
  
  def __eq__(self, other) -> bool:
    if not isinstance(other, DMonomialFunctor):
      return False
    return self.__varname == other.__varname and self.__images == other.__images

#####################################
### MORPHISM CLASSES
#####################################
class DMM_ParentToBase (Morphism):
  def __init__(self, parent):
    super().__init__(parent, parent.base())

  def _call_(self, element: DMonomial_Element) -> Element:
    if not element.degree() == 0:
      raise ValueError(f"{element} is not a constant element")
    return element[0]

class DMM_BaseToParent (Morphism):
  def __init__(self, parent):
    super().__init__(parent.base(), parent)

  def _call_(self, element: Element) -> DMonomial_Element:
    return self.codomain().element_class(self.codomain(), [element])

class DMM_ParentToAlgebraic (Morphism):
  def __init__(self, domain: DMonomial_Parent):
    super().__init__(domain, domain.to_sage())

  def _call_(self, element: DMonomial_Element) -> Element:
    v = self.codomain()(self.domain().varname())
    return sum(self.codomain()(c.to_sage())*v**m.degree() for (m,c) in element.mons_cons_iter())

class DMM_AlgebraicToParent (Morphism):
  def __init__(self, codomain: DMonomial_Parent):
    super().__init__(codomain.to_sage(), codomain)

  def _call_(self, element: Element) -> DMonomial_Element:
    if isinstance(self.domain(), MPolynomialRing_base):
      element = element.polynomial(self.codomain()(self.domain().varname()))
    elif not isinstance(self.domain(), PolynomialRing_generic):
      raise TypeError(f"Weird algebraic ring for a d-Monomial extension")
    
    return self.codomain().element_class(
      self.codomain(),
      [
        self.codomain().base()(c)
        for c in element.coefficients(sparse=False)
      ]
    )

class DMM_BetweenBases (Morphism):
  def __init__(self, 
               domain: DMonomial_Parent, 
               codomain: DMonomial_Parent, 
               map_bases: Morphism):
    if not (map_bases.domain() == domain.base() and map_bases.codomain() == codomain.base()):
      raise TypeError(f"Incompatible map given for coercion between bases")
    super().__init__(domain, codomain)
  
  def _call_(self, element: DMonomial_Element) -> DMonomial_Element:
    return self.codomain().element_class(
      self.codomain(),
      [self.__map(c) for c in element.coefficients(sparse=False)]
    )