from __future__ import annotations
r'''
    Module to create D-extensions with elliptic behavior.

    Let `(K, (d_1,\ldots,d_n))` be a d-Field with multiple difference-differential operators. 
    It is very common to add an element `x` and impose some conditions on the derivative in 
    order to extend the field.

    This is the case of many special functions for the differential case or with many special sequences
    in the difference case. For example, if we consider the differential field `\mathbb{Q}(x)` with the 
    standard derivation `d/dx`, we may want to add the exponential function:

    .. MATH::

        \mathbb{K} = \mathbb{Q}(x,e^x),
    
    where the derivative is defined as `d/dx(e^x) = e^x`. Another classical example is the p-Weierstrass 
    elliptic function. In this case, we add a new element `P` that satisfies

    .. MATH::

        (P')^2 = P^3 + g_2P + g_3.

    In all these cases, we observe that the applied operation over the new element is algebraic over the 
    field of fractions with this new element. We will call this type of extension "elliptic" (mainly because
    they extend the behavior of the p-Weierstrass function.

    ## The case with one operation

    In the case with just one variable, we start with a d-field `K` with just one operation and add a new 
    element `\eta`. Then we stablish that `d(\eta)` is algebraic over `K(\eta)`, meaning that there is a 
    minimal polynomial `p(y) \in K(\eta)[y]` such that `p(d(\eta)) = 0`.

    In this case we can build the field `K(\eta)[y]/(p) \simeq K(\eta) + d(\eta)K(\eta) + \ldots (d(\eta))^{\deg(p)-1}K(\eta)`.
    This field can be seen as a `K(\eta)`-vector space, so addition and multiplication by elements in `K(\eta)` can 
    be trivially implemented.

    However, we would need to implement a multiplication by `d(\eta)`. This is a `K(\eta)`-linear map and has as 
    matrix representation the companion matrix of the polynomial `p(y)`. Hence, we can easily implement the 
    ring structure of the full d-extension.

    The only piece that would need to be added is the operation `d`. It is clear what the image of `\eta` will be. But what
    about the image of `d(\eta)`, namely, `d^2(\eta)`. For this we can follow the notes on Bronstein book and see that the 
    minimal polynomial for `d(\eta)` is providing the value for `d^2(\eta)`.

    * In the differential case: we have that `0 = d(p(d(\eta)))`. If we write `p(y) = p_0 + p_1 y + \ldots + p_n y^n`, 
      then we have that

      .. MATH::

        d(p(y)) = d(p_0) + d(p_1)y + \ldots + d(p_n)y^n + p_1 d(y) + 2p_2 y d(y) + \ldots + np_n y^{n-1} d(y)
                = \kappa_d(p(y)) + \partial_y(p(y)) d(y).

      Evaluating this formula with `y=d(\eta)`, we get

      .. MATH::

        d^2(\eta) = -\kappa_d(p(d(\eta)))/\partial_y(p(d(\eta))).

      Once we have this value fully computed, then the operation `d` is fully defined by observing that the elements of 
      the extension are of the form: `X = a_0(\eta) + a_1(\eta)d(\eta) + \ldots + a_{n-1}(\eta)d(\eta)^{n-1}`, so the 
      derivative can be seen as an operation on vectors as follows:

      .. MATH::

        d(X) = \sum_{i=0}^{n-1} \left(d(a_i(\eta)) d(\eta) + \sum_{j=0}^{n-1} a_i(\eta) \alpha_{i,j}(\eta)\right)(d(\eta))^i,

      which can be seen as an operation with vectors and matrices: `X \equiv \mathbf{a} = (a_0,\ldots,a_{n-1})^T`, then

      .. MATH::

        d(X) \equiv \kappa_d(\mathbf{a}) + M_d \mathbf{a},
      
      where `M_d` is the matrix whose columns are the derivative of `d(\eta)^k`.

    * In the difference case: similar computations lead to the fact that `d^2(\eta)` is algebraic of the same degree
      as `d(\eta)` over the field `K(\eta)`. This is too complicated to implement right now, so we leave it undone.

    EXAMPLES:

        sage: from dalgebra import *
        sage: R = DifferentialRing(QQ[x], [1]).fraction_field()
        sage: x = R('x')
        sage: S = DElliptic(R, "y_p - y", "y") # this means that 'y' is the exponential
        sage: y = S.gen()
        sage: T.<z> = DElliptic(R, "z_p^2 - z^3 - z - 1") # this means that 'z' is an elliptic function
        sage: y
        y
        sage: z
        z

    We can see we can perform aritmetic operations with these objects::

        sage: (x^2 - 1)*y - x^3
        (x^2 - 1)*y - x^3
        sage: (x*y^2).derivative() # y^2 + 2*x*y*y' = y^2 + 2*x*y^2 = (1+2*x)*y^2
        (2*x + 1)*y^2
        sage: (x*z).derivative()
        x*z_p + z
        sage: (x*z).derivative(times=2) # x*z'' + 2*z' = x*(3/2 * z^2 + 1/2) + 2z'
        2*z_p + 3/2*x*z^2 + 1/2*x

    These fields can be easily combined with the ring of differential polynomials::

        sage: W.<u> = DifferentialPolynomialRing(T)
        sage: (u[1]^2 - u[0]^3 - u[0] - 1)(u=z)
        0
        sage: (u[2] * z + u[1]).derivative()
        (z_p + 1)*u_2 + z*u_3
        sage: (u[1]*z.derivative() - u[2]*z).derivative()
        (3/2*z^2 + 1/2)*u_1 - z*u_3

    LIMITATIONS:

    * This structure *do not* work with several d-elliptic variables. If some _monomial_ extensions are used, check the 
      usual Wrapper differential ring.
    * This structure only works with 1 derivation. Shifts, skew-derivations and rings with multiple operations *do not work*.
    * Integration of these objects is not yet implemented.
    * Te computation of all new constants is not yet implemented.
'''

from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.fields import Fields
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection

from ..dring import AdditiveMap, DRings

_DRings = DRings.__classcall__(DRings)
_Fields = Fields.__classcall__(Fields)

#########################################################################
### UNIQUE FACTORY TO CREATE ELLIPTIC EXTENSIONS
#########################################################################
class DEllipticFactory(UniqueFactory):
    r'''
        Factory to create a D-Extension.
    '''
    def create_key(self, base, polynomial: str | Element, varname: str = None, *, names: tuple[str] = None, category = None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        elif base.noperators() != 1 or not base.is_differential():
            raise TypeError(f"The base ring must be a differential ring with just 1 operation")
        elif not base.is_field():
            raise TypeError(f"The base structure must be a differential field")

        # We make 'varname' the name of the variable
        if varname is not None and names is not None and len(names) > 0:
            raise ValueError(f"Repeated information provided by arguments. Either use 'varname' (thord argument) or 'names")
        elif varname is None and names is not None and len(names) > 1:
            raise ValueError(f"Incorrect use of 'names' argument. Only 1 name is allowed")
        elif varname is None and names is None:
            raise ValueError(f"Incorrect call: we need a `varname` or a list of one ``names``")
        elif varname is None:
            varname = names[0]
        
        # We convert `polynomial` into a string
        polynomial = str(polynomial)

        return (base, polynomial, varname, category)

    def create_object(self, _, key) -> DElliptic_Field:
        base, polynomial, varname, category = key

        return DElliptic_Field(base, polynomial, varname, category)


DElliptic = DEllipticFactory("dalgebra.dpolynomial.pseudo_doperator.DElliptic")

#########################################################################
### ELEMENT AND PARENT CLASSES FOR ELLIPTIC EXTENSIONS
#########################################################################
class DElliptic_Element(Element):
    def __init__(self, parent: DElliptic_Field, *coefficients: Element):
        if len(coefficients) > parent.degree():
            raise ValueError(f"Too much information to create a DElliptic_Element")
        
        super().__init__(parent)

        ## We store in self.__coeffs the list of all coefficients corresponding to (1,eta',...,eta'^{n-1})
        ## We fill with zeros if not long enough sequence is provided.
        self.__coeffs = tuple(
            [parent.algebraic_base()(c) for c in coefficients] + 
            (parent.degree()-len(coefficients))*[parent.algebraic_base().zero()]
        )

    ###################################################################################
    ### Property methods
    ###################################################################################
    def is_zero(self) -> bool: #: Checker for the zero element
        return all(c == 0 for c in self.__coeffs)

    def is_simple(self) -> bool: #: Checker to see whether `\eta'` appears in ``self`` or not
        return all(c == 0 for c in self.__coeffs[1:])

    def is_one(self) -> bool: #: Checker for the one element
        return self.__coeffs[0] == 1 and self.is_simple()

    @property
    def coeffs(self) -> tuple[Element]:
        return self.__coeffs

    def numerator(self) -> DElliptic_Element:
        return self
    
    def denominator(self) -> DElliptic_Element:
        return self.parent().one()

    @cached_method
    def algebraic(self) -> Element:
        y = self.parent().variable_p()

        return sum(coeff*y**i for (i,coeff) in enumerate(self.__coeffs) if coeff != 0)

    @cached_method
    def partial(self) -> DElliptic_Element:
        r'''
            Method that computes the partial derivative with respect to `\eta'` when
            we consider the element as a pure algebraic polynomial in `\eta'`.
        '''
        return self.parent().element_class(self.parent(), *[(i+1)*coeff for (i,coeff) in enumerate(self.__coeffs[1:])])

    @cached_method
    def kappa(self) -> DElliptic_Element:
        r'''
            Method that computes the `\kappa_d` derivative of an element.

            This is the result of considering `\eta'` a constant and computing the resulting derivative.
            See method :func:`DElliptic_Field.inner_derivative` for further information.
        '''
        eta_p = self.parent().variable_p()
        as_algebraic = sum(self.parent().inner_derivative(coeff) * eta_p**i for (i,coeff) in enumerate(self.__coeffs) if coeff !=0)

        return self.parent()(as_algebraic)

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: DElliptic_Element) -> DElliptic_Element:
        return self.parent().element_class(self.parent(), *[self.__coeffs[i] + other.__coeffs[i] for i in range(self.parent().degree())])
    
    def _neg_(self) -> DElliptic_Element:
        return self.parent().element_class(self.parent(), *[-self.__coeffs[i] for i in range(self.parent().degree())])

    def _sub_(self, other: DElliptic_Element) -> DElliptic_Element:
        return self + (-other)

    def _mul_(self, other: DElliptic_Element) -> DElliptic_Element:
        return self.parent()(self.algebraic() * other.algebraic())

    def _inv_(self) -> DElliptic_Element:
        return self.parent()(~self.algebraic())
        
    @cached_method
    def __pow__(self, power: int) -> DElliptic_Element:
        if power == 0:
            return self.parent().one()
        elif power == 1:
            return self
        elif power < 0:
            raise NotImplementedError("Negative powers not allowed")
        else:
            a,A = (self**(power//2 + power % 2), self**(power//2))
            return a*A

    def __eq__(self, other) -> bool:
        if not isinstance(other, self.__class__) or other.parent() != self.parent():
            try:
                other = self.parent()(other)
            except Exception:
                return False

        return all(self.__coeffs[i] == other.__coeffs[i] for i in range(self.parent().degree()))

    def __ne__(self, other) -> bool:
        return not (self == other)

    def __hash__(self) -> int:
        return hash(self.__coeffs)

    @cached_method
    def __repr__(self) -> str:
        return repr(self.algebraic())

    @cached_method
    def _latex_(self) -> str:
        if self.is_zero():
            return "0"
        parts = []
        for i,coeff in enumerate(self.__coeffs):
            if coeff != 0:
                var = "" if i == 0 else f"{self.parent().varname()}'" if i == 1 else r"\left(" + f"{self.parent().varname()}'" + r"\right)^{" + i + r"}"
                parts.append(r"\left(" + coeff + r"\right)" + var)
        return "+".join(parts)

class DElliptic_Field(Parent):
    r'''
        TODO: Write documentation
    '''
    Element = DElliptic_Element
    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base), _Fields] + ([category] if category is not None else [])

    def __init__(self, base : Parent, polynomial: str | Element, varname:str = None, category=None):
        ## Calling the super __init__ to stablish the categories and the main attributes
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        ## Creating the inner structures necessary
        self.__algebraic_base = PolynomialRing(base.to_sage(), varname).fraction_field() ## F(eta)
        self.__variable = self.__algebraic_base.gens()[0] ## eta
        self.__algebraic_poly = PolynomialRing(self.__algebraic_base, varname + "_p") ## F(eta)[eta_p]
        self.__poly_var = self.__algebraic_poly.gens()[0] ## generic eta_p
        self.__min_poly = self.__algebraic_poly(polynomial)
        self.__algebraic = self.__algebraic_poly.quotient_by_principal_ideal(self.__min_poly, varname + "_p") ## F(eta)[eta_p]/(poly)
        self.__algebraic_var = self.__algebraic.gens()[0] ## real eta_p
        self.__varname = varname
        self.__variable_prime = varname + "_p"

        ## Derived attributes
        self.__degree = self.__min_poly.degree()

        ## Creating the conversion maps
        ## We force SageMath to find the coercions between the algebraic structures
        self.__algebraic_poly.coerce_map_from(self.__algebraic_base)
        self.__algebraic.coerce_map_from(self.__algebraic_poly)
        self.__algebraic.coerce_map_from(self.__algebraic_base)
        ## We add our own coercions with the new structure
        self.__algebraic_base.register_conversion(MapDEllipticToField(self, self.__algebraic_base)) # from ``self`` to `F(eta)[eta_p]`
        self.register_coercion(MapFieldToDElliptic(self.__algebraic_base, self)) # from `F(eta)[eta']` to ``self``
        self.__algebraic_poly.register_coercion(MapDEllipticToPoly(self, self.__algebraic_poly)) # from ``self`` to `F(eta)[eta_p]`
        self.register_coercion(MapPolyToDElliptic(self.__algebraic_poly, self)) # from `F(eta)[eta']` to ``self``
        self.__algebraic.register_coercion(MapDEllipticToAlgebraic(self, self.__algebraic)) # from ``self`` to `F(eta)[eta_p]/(p(eta'))`
        self.register_coercion(MapAlgebraicToDElliptic(self.__algebraic, self)) # from `F(eta)[eta_p]/(p(eta'))` to ``self``
        self.base().register_conversion(ConversionToBase_DElliptic(self, self.base())) # from ``self`` to `F`

        ## Extending the derivative of the base field
        self.__operators = [self.extend_derivation(self.base().operators()[0])]

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def varname(self) -> str: return self.__varname

    def gen(self) -> DElliptic_Element:
        r'''Method to obtain `\eta` as an element of ``self``'''
        return self(self.variable())

    def gen_p(self) -> DElliptic_Element:
        r'''Method to obtain `\eta'\ as an element of ``self``'''
        return self(self.variable_p())

    def gens(self) -> tuple[DElliptic_Element]:
        return (self.gen(),)

    def variable(self) -> Element:
        r'''Method to obtain the algebraic (without d-structure) variable for `\eta`'''
        return self.__variable

    def variable_poly(self) -> Element:
        r'''Method to obtain the algebraic (without d-structure) variable for `\eta'`'''
        return self.__poly_var

    def variable_p(self) -> Element:
        r'''Method to obtain the quotiented (without d-structure) variable for `\eta'`'''
        return self.__algebraic_var

    def algebraic_base(self) -> Parent:
        r'''Method to obtain the basic field `F(\eta)`'''
        return self.__algebraic_base

    def algebraic_poly(self) -> Parent:
        r'''Method to obtain the polynomial ring before we took a quotient'''
        return self.__algebraic_poly

    def algebraic(self) -> Parent:
        r'''Method to obtain the algebraic structure (quotient of a polynomial ring) behinf this field'''
        return self.__algebraic

    def degree(self) -> int:
        return self.__degree

    def one(self) -> DElliptic_Element:
        return self.element_class(self, 1)

    def zero(self) -> DElliptic_Element:
        return self.element_class(self, 0)

    #################################################
    ### Derivation methods
    #################################################
    def inner_derivative(self, element) -> Element:
        r'''
            Method that takes an element in `F(eta)` and computes its derivative as an element of ``self``.
        '''
        if isinstance(element, DElliptic_Element):
            if not element.is_simple():
                raise TypeError(f"Impossible to compute the inner derivative for an element with `eta'`")
            element = element.coeffs[0]
        
        if not element in self.__algebraic_base:
            raise TypeError(f"Impossible to compute the inner derivative if it is not a proper element")
        element = self.__algebraic_base(element)

        eta = self.__variable ## eta as a polynomial variable
        num = element.numerator() # numerator of element (i.e., polynomial in eta)
        den = element.denominator() # denominator of element (i.e., polynomial in eta)

        ## Computing the derivative of a polynomial
        ## p(y) --> d(p(y)) = \partial_y(p) * y' + \kappa_d(p)
        dnum = num.derivative(eta)
        dden = den.derivative(eta)
        knum = sum(
            self.__algebraic_base(
                self.base().to_sage()(self.base()(c).derivative())
            )*eta**i for (i,c) in enumerate(num.coefficients(False))
        )
        kden = sum(
            self.__algebraic_base(
                self.base().to_sage()(self.base()(c).derivative())
            )*eta**i for (i,c) in enumerate(den.coefficients(False))
        )

        der_num = self.algebraic()(dnum)*self.__algebraic_var + knum
        der_den = self.algebraic()(dden)*self.__algebraic_var + kden
        num = self.algebraic()(num)
        den = self.algebraic()(den)
        
        ## Now, as elements in the algebraic quotient, we compute the derivative using the quotient rule
        return (der_num * den - num * der_den) * (~den)**2

    @cached_method
    def variable_pp(self) -> Element:
        r'''Method to compute the second derivative of the added variable `\eta''`'''
        P = self.__min_poly
        eta_p = self.__poly_var
        dP = self.__algebraic(P.derivative()) ## partial derivative w.r.t. the variable eta_p`
        kappa_P = sum(self.__algebraic(self.inner_derivative(c))*eta_p**i for (i,c) in enumerate(self.__min_poly.coefficients(False)))

        # d^2(\eta) = -\kappa_d(p(d(\eta)))/\partial_y(p(d(\eta)))
        return -kappa_P * (~dP)

    def extend_derivation(self, derivation: AdditiveMap) -> AdditiveMap:
        variable_pp = self.variable_pp()

        def __derivation(element: DElliptic_Element) -> DElliptic_Element:
            kappa_element = self.__algebraic(element.kappa())
            partial_element = self.__algebraic(element.partial())

            return self(kappa_element + partial_element * variable_pp)

        return AdditiveMap(self, __derivation)
          
    #################################################
    ### Coercion methods
    #################################################
    def _coerce_map_from_base_ring(self):
        return CoerceFromBase_DElliptic(self.base(), self)

    def construction(self) -> tuple[DEllipticFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return DEllipticFunctor(self.__min_poly, self.__varname), self.base()

    def fraction_field(self):
        return self ## self is already a field

    def change_base(self, R) -> DElliptic_Field:
        new_ring = DElliptic_Field(R, self.__min_poly, self.__varname)
        ## Creating the coercion map if possible
        try:
            M = CoerceBetweenBases_DElliptic(self, new_ring, R.coerce_map_from(self.base()))
            new_ring.register_coercion(M)
        except AssertionError: # This ring was already created
            pass

        return new_ring

    # #################################################
    # ### Magic python methods
    # #################################################
    def __repr__(self):
        return f"D-Elliptic extension of {self.base()} with element {self.__varname} whose derivative satisfies \n\t[{self.__min_poly} = 0]"

    def _latex_(self):
        return r"\frac{" + latex(self.base()) + r"\langle" + self.__varname + r"\rangle[" + self.__variable_prime + r"]}{\left(" + latex(self.__min_poly) + r"\right)}"

    # #################################################
    # ### Method from DRing category
    # #################################################
    def operators(self) -> Collection[AdditiveMap]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def add_constants(self, *new_constants: str) -> DElliptic_Field:
        return self.change_base(self.base().add_constants(*new_constants))

    def linear_operator_ring(self) -> DElliptic_Field:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        raise NotImplementedError(f"Ring of linear operators not yet implemented for D-Extensions")

    def inverse_operation(self, element: DElliptic_Element, operation: int = 0) -> DElliptic_Element:
        raise NotImplementedError(f"The integration in these fields is not yet implemented")

    def to_sage(self):
        return self.__algebraic

#########################################################################
### CONSTRUCTIONS FUNCTOR FOR ELLIPTIC EXTENSIONS
#########################################################################
class DEllipticFunctor(ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DElliptic_Field`.

        This class represents the functor `F: R \mapsto R(\eta)[\eta']/(p(\eta'))`.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see
          the input ``names`` in :class:`DPolynomialRing_Monoid`)
    '''
    def __init__(self, polynomial: str | Element, varname: str):
        self.__min_poly = polynomial
        self.__varname = varname
        super().__init__(_DRings,_DRings)
        self.rank = 11 # just below DPolyRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        return DElliptic_Field(x,self.__min_poly,self.__varname)

    def _repr_(self):
        return f"DElliptic_Field(*,{self.__min_poly},{self.__varname})"

    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return str(self.__min_poly) == str(other.__min_poly) and self.__varname == other.__varname
        return False

#########################################################################
### COERCIONS AND CONVERSION MORPHISMS FOR ELLIPTIC EXTENSIONS
#########################################################################
class MapDEllipticToField(Morphism):
    r'''
        Conversion map between an Elliptic extension and the associated field `F(\eta)`.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the natural restriction map between the `\E_\eta` to `F(\eta)`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element: DElliptic_Element):
        if not element.is_simple():
            raise ValueError(f"This element does not belong to the main field {self.domain().algebraic_base()}")
        return self.domain().algebraic_base()(self.coeffs[0])

class MapFieldToDElliptic(Morphism):
    r'''
        Coercion map between the associated base field and the Elliptic extension.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the natural inclusion of `F(\eta)` into `\E_\eta`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element):
        return self.codomain().element_class(self.codomain(), self.codomain().algebraic_base()(element))

class MapDEllipticToPoly(Morphism):
    r'''
        Coercion map between an Elliptic extension and the associated polynomial ring.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the natural inclusion map (i.e., coercion map) between the `\E_\eta` and `F(\eta)[\eta']`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element: DElliptic_Element):
        return self.domain().algebraic()(element).lift()

class MapPolyToDElliptic(Morphism):
    r'''
        Coercion map between the associated polynomial ring and the Elliptic extension.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the natural projection map between `F(\eta)[\eta']` and `\E_\eta`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element):
        return self.codomain()(self.codomain().algebraic()(element))

class MapDEllipticToAlgebraic(Morphism):
    r'''
        Coercion map between the associated polynomial ring and the Elliptic extension.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the transformation on structure between the :class:`DElliptic_Field` and
        the plain algebraic structure given by `E_\eta`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element: DElliptic_Element):
        eta_p = self.domain().variable_p()

        return sum(c*eta_p**i for i,c in enumerate(element.coeffs))

class MapAlgebraicToDElliptic(Morphism):
    r'''
        Coercion map between the associated polynomial ring and the Elliptic extension.

        The elliptic extension can be written (algebraically speaking) as follows:

        .. MATH::

            E_\eta = \frac{F(\eta)[\eta']}{\left(p(\eta')\right)}

        This is the transformation on structure between the plain algebraic structure given by `E_\eta` and
        the :class:`DElliptic_Field`.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element):
        element_poly = element.lift() # univariate polynomial

        return self.codomain().element_class(self.codomain(), *element_poly.coefficients(False))

class CoerceFromBase_DElliptic(Morphism):
    r'''
        Basic coercion from the differential field that is the base of an elliptic extension and 
        the elliptic extension itself
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element):
        return self.codomain().element_class(self.codomain(), self.domain().to_sage()(element))

class ConversionToBase_DElliptic(Morphism):
    r'''
        Basic conversion from an elliptic extension to its differential field.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)

    def _call_(self, element: DElliptic_Element):
        if element.is_simple():
            element = element.coeffs[0] # this is a fraction in F(eta)
            if element.denominator() == 1 and element.numerator().degree() == 0:
                return self.codomain()(element.numerator().constant_coefficient())

        raise ValueError(f"The given element ({element}) is not in the base field.")

class CoerceBetweenBases_DElliptic(Morphism):
    r'''
        Conversion between elliptic extension when we change the base differential field.
    '''
    def __init__(self, domain, codomain, coerce_map):
        super().__init__(domain, codomain)

        self.__inner_coercion = coerce_map

    def _call_(self, element: DElliptic_Element) -> DElliptic_Element:
        new_coeffs = list()
        eta = self.codomain().variable()
        for coeff in element.coeffs: 
            # coeff is a rational function in F(eta)
            num = sum(
                self.codomain().base().to_sage()(self.__inner_coercion(self.domain().base()(coeff)))*eta**i 
                for i,coeff in enumerate(coeff.numerator().coefficients(False))
            )
            den = sum(
                self.codomain().base().to_sage()(self.__inner_coercion(self.domain().base()(coeff)))*eta**i 
                for i,coeff in enumerate(coeff.denominator().coefficients(False))
            )
            new_coeffs.append(num/den)
        return self.codomain().element_class(self.codomain(), *new_coeffs)

__all__ = ["DElliptic"]