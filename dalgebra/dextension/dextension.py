from __future__ import annotations

r'''
    Module to create D-Extensions with several operations.
'''
from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent
from sage.symbolic.ring import SR

from typing import Collection

from ..dring import AdditiveMap, DFractionField, DRings

_DRings = DRings.__classcall__(DRings)

class DExtensionFactory(UniqueFactory):
    r'''
        Factory to create a D-Extension.
    '''
    def create_key(self, base, names: list[str] = None, imgs: list[Element] = None, map: dict[str, Element | list[Element]] = None, **kwds):
        # We check now whether the base ring is valid or not
        if base not in _DRings:
            raise TypeError("The base ring must have operators attached")

        # We check the format of the input
        if names is not None:
            if imgs is None:
                raise ValueError(f"When providing names, we need to provide the images")
            map = dict(zip(names, imgs))

        if map is None:
            raise ValueError(f"No information provided for new d-variables")
        else:
            if base.noperators() == 1: # Common format to tuples
                map = {k : v if isinstance(v, (list, tuple)) else (v,) for (k,v) in map.items()}
            if not all(
                isinstance(value, (list, tuple)) and
                len(value) == base.noperators() and
                all(isinstance(v, (Element, str)) for v in value)
                for value in map.values()
            ):
                raise TypeError(f"Error in the format to provide the images of the new variables")
            map = {k : tuple(str(v) if isinstance(v, Element) else v for v in value) for (k,value) in map.items()}

        return (base,tuple(sorted(map.items())))

    def create_object(self, _, key) -> DExtension_PolyRing:
        base, map = key
        map = dict(map) # reconverting to dictionary

        return DExtension_PolyRing(base, map)


DExtension = DExtensionFactory("dalgebra.dpolynomial.pseudo_doperator.DExtension")

class DExtension_Monomial(dict):
    def __init__(self, *args, **kwds):
        self.__blocked = False
        super().__init__(*args, **kwds)

        to_rem = [k for k in self if self[k] == 0]
        for k in to_rem:
            del self[k]

        self.__blocked = True

    def is_one(self) -> bool: #: Checks if the monomial is the 1 (i.e., it is empty)
        return len(self) == 0

    def degree(self) -> int:
        return sum(self.values())

    def __setitem__(self, key, value) -> None:
        if not self.__blocked:
            return super().__setitem__(key, value)
        raise NotImplementedError(f"DExtension_Monomial are ummutable objects")

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.items())))

    def __mul__(self, other) -> DExtension_Monomial:
        if isinstance(other, DExtension_Monomial):
            result = self.copy() # this is a dict
            for k in other:
                if k in self:
                    result[k] += other[k]
                else:
                    result[k] = other[k]

            return DExtension_Monomial(result)
        return NotImplemented

    def __rmul__(self, other) -> DExtension_Monomial:
        return self.__mul__(other)

    def __truediv__(self, other) -> DExtension_Monomial:
        if isinstance(other, DExtension_Monomial):
            if all((k in self and self[k] > other[k]) for k in other):
                result = self.copy()
                for k in other:
                    result[k] -= other[k]
                return DExtension_Monomial(result)
        return NotImplemented

class DExtensionElement(Element):
    def __init__(self, parent, *monomials: tuple[dict, Element], dic: dict[DExtension_Monomial, Element] = None):
        if len(monomials) > 0 and dic is not None:
            raise ValueError(f"Too much information to create a DExtensionElement")
        elif dic is None:
            self.__content = {DExtension_Monomial(k) : parent()(v) for (k,v) in monomials}
        else:
            self.__content = dic

        super().__init__(parent)

    ###################################################################################
    ### Property methods
    ###################################################################################
    def is_zero(self) -> bool: #: Checker for the zero element
        return len(self.__content) == 0

    def is_one(self) -> bool: #: Checker for the one element
        if len(self.__content) != 1:
            return False
        m, c = next(iter(self.__content.items()))
        return m.is_one() and c == self.parent().base().one()

    def is_monomial(self) -> bool: #: Checker for an element to be a monomial
        if len(self.__content) != 1:
            return False
        c = next(iter(self.__content.values()))
        return c == 1

    def is_variable(self) -> bool: #: Checker for an element to be a variable
        return self.is_monomial() and self.degree() == 1

    @cached_method
    def monomials(self) -> tuple[DExtensionElement]:
        P = self.parent()
        return tuple(P.element_class(P, (m, P.base().one())) for m in self.__content.keys())

    @cached_method
    def coefficients(self) -> tuple[Element]:
        return tuple(self.__content.values())

    def degree(self, variable: DExtensionElement = None):
        variable = variable if variable is None else self.parent()(variable)
        if variable is not None and not variable.is_variable():
            raise TypeError(f"The input to check a degree must be a variable")

        if self.is_zero():
            return -Infinity

        if variable is None:
            return max(m.degree() for m in self.__content)
        else:
            i = self.parent().gen_index(str(variable))
            return max(m.get(i,0) for m in self.__content)

    # ###################################################################################
    # ### Arithmetic operations
    # ###################################################################################
    # def _add_(self, other: PseudoDOperator) -> PseudoDOperator:
    #     ## Adding the positive parts
    #     positive = self.__positive.copy()
    #     for (k, element) in other.__positive.items():
    #         if k in positive:
    #             element = element + positive[k]
    #         positive[k] = element

    #     ## Adding the negative parts (if possible)
    #     negative = self.__negative.copy()
    #     for (k, oa), ob in other.__negative.items():
    #         if (k, oa) not in negative:
    #             negative[(k, oa)] = ob
    #         else:
    #             negative[(k, oa)] += ob

    #     return self.parent().element_class(self.parent(), positive, negative)

    # def __neg__(self) -> PseudoDOperator:
    #     positive = {k: -element for (k,element) in self.__positive.items()}
    #     negative = {(k, after): -before for ((k, after), before) in self.__negative.items()}

    #     return self.parent().element_class(self.parent(), positive, negative)

    # def _sub_(self, other: PseudoDOperator) -> PseudoDOperator:
    #     return self + (-other)

    # def _mul_(self, other: PseudoDOperator) -> PseudoDOperator:
    #     sp, sn = self.__positive, self.__negative
    #     op, on = other.__positive, other.__negative

    #     positive = dict()
    #     negative = dict()

    #     ## POSITIVE PART OF SELF
    #     for (k, a) in sp.items():
    #         ## POSITIVE PART OF OTHER
    #         for (n, c) in op.items():
    #             for i in range(k+1):
    #                 if (k-i+n) not in positive:
    #                     positive[k-i+n] = self.parent().base().zero()
    #                 positive[k-i+n] = a*binomial(k, i)*c.derivative(times=i)
    #         ## NEGATIVE PART OF OTHER
    #         for ((n, d), c) in on.items():
    #             n = -n # we make n positive
    #             for i in range(0, k-n+1):
    #                 for j in range(0, k-i-n+1):
    #                     if (k-i-n-j) not in positive:
    #                         positive[k-i-n-j] = self.parent().base().zero()
    #                     positive[k-i-j-n] += binomial(k,i)*a*c.derivative(times=i)*binomial(k-i-n,j)*d.derivative(times=j)
    #             for i in range(max(0,k-n+1), k+1):
    #                 if (k-i-n, d) not in negative:
    #                     negative[(k-i-n, d)] = binomial(k,i) * a * c.derivative(times=i)
    #                 else:
    #                     negative[(k-i-n, d)] += binomial(k,i) * a * c.derivative(times=i)

    #     ## NEGATIVE PART OF SELF
    #     for ((k, b), a) in sn.items():
    #         k = -k # we make it positive
    #         ## POSITIVE PART OF OTHER
    #         for (n, c) in op.items():
    #             for i in range(0,n-k+1):
    #                 for j in range(0,n-k-i+1):
    #                     if (n-k-i-j) not in positive:
    #                         positive[n-k-i-j] = (-1)**i*a*binomial(n-k-i,j)*binomial(n,i)*(b*c).derivative(times=i+j)
    #                     else:
    #                         positive[n-k-i-j] += (-1)**i*a*binomial(n-k-i,j)*binomial(n,i)*(b*c).derivative(times=i+j)
    #             for i in range(max(0,n-k+1), n+1):
    #                 after = (b*c).derivative(times=i)
    #                 if (n-k-i, after) not in negative:
    #                     negative[(n-k-i, after)] = (-1)**i*a*binomial(n,i)
    #                 else:
    #                     negative[(n-k-i, after)] += (-1)**i*a*binomial(n,i)
    #         ## NEGATIVE PART OF OTHER
    #         for ((n, d), c) in on.items():
    #             n = -n # we make it positive
    #             if (b*c).derivative() == 0: # we can do something
    #                 if (-n-k, d) not in negative:
    #                     negative[(-n-k, d)] = a*b*c
    #                 else:
    #                     negative[(-n-k, d)] += a*b*c
    #             else:
    #                 return NotImplemented ## These cases are not well implemented yet

    #     return self.parent().element_class(self.parent(), positive, negative)

    # @cached_method
    # def __pow__(self, power: int) -> PseudoDOperator:
    #     if power == 0:
    #         return self.parent().one()
    #     elif power == 1:
    #         return self
    #     elif power < 0:
    #         raise NotImplementedError("Negative powers not allowed")
    #     else:
    #         a,A = (self**(power//2 + power % 2), self**(power//2))
    #         return a*A

    # def __eq__(self, other) -> bool:
    #     if not isinstance(other, self.__class__) or other.parent() != self.parent():
    #         try:
    #             other = self.parent()(other)
    #         except Exception:
    #             return False

    #     return (self - other).is_zero()

    # def __ne__(self, other) -> bool:
    #     return not (self == other)

    # def __hash__(self) -> int:
    #     return hash((sorted(self.__positive.items()), sorted(self.__negative.items(), key=lambda t : (t[0][0], len(str(t[0][1]))))))

    # def __call__(self, element: Element) -> Element:
    #     result = sum((C*element.derivative(times=i) for (i, C) in self.__positive.items()), self.parent().base().zero())
    #     for ((i,a), b) in self.__negative.items():
    #         result += b * (element*a).integrate(times=-i)

    #     return result

    # @cached_method
    # def __repr__(self) -> str:
    #     if self.is_zero():
    #         return "0"
    #     elif self.is_identity():
    #         return "1"

    #     ## We know there is something in the element
    #     g = self.parent().gen_name()
    #     def term_str(order, element):
    #         if isinstance(order, (list, tuple)):
    #             order, after = order
    #             before = "" if element == 1 else f"({element})"
    #             after = "" if after == 1 else f"({after})"
    #         else:
    #             before = "" if element == 1 else f"({element})"
    #             after = ""
    #         order = f"{g}^({order})" if order < 0 else f"{g}^{order}" if order > 1 else g if order == 1 else ""

    #         return "*".join([el for el in [before, order, after] if el != ""])

    #     def sorting_key(_tuple):
    #         if not isinstance(_tuple[0], (list, tuple)):
    #             return (_tuple[0],)
    #         else:
    #             return (_tuple[0][0], len(str(_tuple[0][1])), str(_tuple[0][1]))

    #     return " + ".join(
    #         term_str(o, el) for (o,el) in
    #         sorted(list(self.__positive.items()) + list(self.__negative.items()), key=sorting_key, reverse=True)
    #     )

    # @cached_method
    # def _latex_(self) -> str:
    #     if self.is_zero():
    #         return "0"
    #     elif self.is_identity():
    #         return "1"

    #     ## We know there is something in the element
    #     g = self.parent().gen_name()
    #     def term_str(order, element):
    #         if isinstance(order, (list, tuple)):
    #             order, after = order
    #             before = "" if element == 1 else f"\\left({latex(element)}\\right)"
    #             after = "" if after == 1 else f"\\left({latex(after)}\\right)"
    #         else:
    #             before = "" if element == 1 else f"\\left({latex(element)}\\right)"
    #             after = ""
    #         order = f"{g}^{{{order}}}" if order not in {0,1} else g if order == 1 else ""

    #         return f"{before}{order}{after}"

    #     def sorting_key(_tuple):
    #         if not isinstance(_tuple[0], (list, tuple)):
    #             return (_tuple[0],)
    #         else:
    #             return (_tuple[0][0], len(str(_tuple[0][1])), str(_tuple[0][1]))

    #     return " + ".join(term_str(o, el) for (o,el) in sorted(list(self.__positive.items()) + list(self.__negative.items()), key=sorting_key, reverse=True))
    pass

class DExtension_PolyRing(Parent):
    r'''
        TODO: Write documentation
    '''
    Element = DExtensionElement

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, map: dict[str, str], category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## Creating the main attributes of the DExtension
        self.__var_names = [list(map.keys())]

        ## Creating the equivalent polynomial ring
        try:
            self.__poly_ring = PolynomialRing(base.to_sage(), self.__var_names)
        except NotImplementedError:
            self.__poly_ring = PolynomialRing(base, self.__var_names)
        map_imgs = {self.__poly_ring(k) : tuple(self.__poly_ring(v) for v in value) for (k,value) in map.values()}

        ## Creating the conversion maps
        self.register_conversion(MapSageToDalgebra_PolyRing(self.__poly_ring, self, dict(zip(self.__var_names,self.__var_names))))
        self.register_conversion(MapDalgebraToSage_PolyRing(self.__poly_ring, self, dict(zip(self.__var_names,self.__var_names))))

        self.__imgs = {self(k): tuple(self(v) for v in value) for (k,value) in map_imgs}
        self.__gens = tuple(self.__imgs.keys())

        self.__fraction_field = None

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gens(self) -> tuple[DExtensionElement]:
        return self.__gens

    def gen_index(self, variable: DExtensionElement | str):
        if not isinstance(variable, str):
            variable = str(variable)

        if variable not in self.__var_names:
            raise ValueError(f"Variable {variable} not found as a generator")

        return self.__var_names.index(variable)

    def variable(self, name) -> DExtensionElement:
        r'''Create the variable object for a given name'''
        return self.element_class(self, ({self.gen_index(name) : 1}, self.base().one()))

    def one(self) -> DExtensionElement:
        return self.element_class(self, (dict(), self.base().one()))
    def zero(self) -> DExtensionElement:
        return self.element_class(self, tuple())

    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        return CoerceFromBase(self.base(), self)

    def construction(self) -> tuple[DExtensionFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return DExtensionFunctor(self.__var_names[0], self.__imgs), self.base()

    def fraction_field(self):
        if self.__fraction_field is None:
            self.__fraction_field = DFractionField(self)

    def change_base(self, R) -> DExtension_PolyRing:
        new_ring = DExtension(R, self.__var_names, list(self.__imgs.values()))
        ## Creating the coercion map if possible
        try:
            M = CoerceBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Ring of pseudo-differential operators over {self.base()}"

    def _latex_(self):
        return latex(self.base()) + r"\langle" + self.__gens[0] + r"\rangle"

    #################################################
    ### Element generation methods
    #################################################
    def random_element(self,
        up_bound : int = 0, lower_bound : int = 0,
        *args,**kwds
    ) -> DExtensionElement:
        r'''
            Creates a random element in this ring.

            This method receives a bound for the degree and order of all the variables
            appearing in the ring and also a sparsity measure to avoid dense polynomials.
            Extra arguments are passed to the random method of the base ring.

            INPUT:

            * ``deg_bound``: total degree bound for the resulting polynomial.
            * ``order_bound``: order bound for the resulting polynomial.
            * ``sparsity``: probability of a coefficient to be zero.
        '''
        up_bound = 0 if ((up_bound not in ZZ) or up_bound < 0) else up_bound
        lower_bound = 0 if ((lower_bound not in ZZ) or lower_bound < 0) else lower_bound

        rand = lambda : self.base().random_element(*args, **kwds)
        pos_coeffs = [rand() for _ in range(up_bound+1)]
        neg_coeffs = {(-i, rand()): rand() for i in range(1, lower_bound)}

        return self.element_class(self, pos_coeffs, neg_coeffs)

    #################################################
    ### Method from DRing category
    #################################################
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> DExtension_PolyRing:
        return DExtension(self.base().add_constants(*new_constants), self.__var_names, self.__imgs)

    def linear_operator_ring(self) -> DExtension_PolyRing:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DExtensionElement, operation: int = 0) -> DExtensionElement:
        if element not in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if operation != 0:
            raise ValueError(f"The given operation({operation}) is not valid")

        try:
            return self.Di * element
        except Exception:
            raise NotImplementedError(f"The multiplication of {self.__gens[0]}^(-1) * {element} can not be computed.")

    def to_sage(self):
        return self.__poly_ring

class DExtensionFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DPolynomialRing_Monoid`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see
          the input ``names`` in :class:`DPolynomialRing_Monoid`)
    '''
    def __init__(self, names: tuple[str], imgs: tuple[str]):
        self.__names = names
        self.__imgs = [tuple(str(SR(i)) for i in img) for img in imgs] # Simplifying the equality check for merging
        super().__init__(_DRings,_DRings)
        self.rank = 11 # just below DPolyRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        return DExtension(x,self.__names,self.__imgs)

    def _repr_(self):
        return f"DExtension(*,{dict(zip(self.__names, self.__imgs))})"

    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return self.__names == other.__names and self.__imgs == other.__imgs

    def merge(self, other):
        if isinstance(other, DExtensionFunctor):
            sdict = dict(zip(self.__names, self.__imgs))
            odict = dict(zip(other.__names, other.__imgs))

            for v in sdict:
                if v in odict:
                    if sdict[v] != odict[v]:
                        return None # Incompatible images for the same variable

            ## All chekings done
            sdict.update(odict) # since when they coincide they are equal, this simply adds the new
            return DExtensionFunctor(tuple(sdict.keys()), tuple(sdict.values()))
        return None

class MapSageToDalgebra_PolyRing(Morphism):
    def __init__(self, domain, codomain, map_variables: dict[str, str]):
        super().__init__(domain, codomain)
        self.__map = map_variables

    def _call_(self, element):
        deg = lambda e, v : e.degree(v) if hasattr(element, "coefficient") else e.degree()
        result = self.codomain().zero()
        for (c, m) in zip(element.coefficients(), element.monomials()):
            nc = self.codomain().base()(c)
            nm = self.codomain().one()
            for v in m.variables():
                nm *= self.codomain().variable(self.__map[str(v)])**deg(m,v)
            result += nc*nm
        return result

class MapDalgebraToSage_PolyRing(Morphism):
    def __init__(self, domain, codomain, map_variables: dict[str, str]):
        super().__init__(domain, codomain)
        self.__map = map_variables

    def _call_(self, element):
        result = self.codomain().zero()
        for (c, m) in zip(element.coefficients(), element.monomials()):
            nc = self.codomain().base()(c)
            nm = self.codomain().one()
            for v in m.variables():
                nm *= self.codomain().variable(self.__map[str(v)])**m.degree(v)
            result += nc*nm
        return result

class CoerceFromBase(Morphism):
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element):
        return self.codomain().element_class(self.codomain(), (dict(), element))

class CoerceBetweenBases(Morphism):
    def __init__(self, domain, codomain):
        if not isinstance(domain, DExtension_PolyRing) or not isinstance(codomain, DExtension_PolyRing):
            raise TypeError("Inconsistent domain/codomain for Morphism")
        elif domain.construction()[0] != codomain.construction()[0]:
            raise ValueError("It seems domain and codomain are not related with the same d-variables")

    def _call_(self, element):
        return self.codomain().element_class(self.codomain(), *((m, self.codomain().base()(c)) for (m,c) in element._DExtensionElement__content.items))