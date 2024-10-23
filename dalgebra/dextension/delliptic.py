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
'''

class DElliptic_Element(Element):
    def __init__(self, parent: DElliptic_Field, *coefficients: Element):
        if len(coefficients) > parent.degree():
            raise ValueError(f"Too much information to create a DElliptic_Element")
        
        super().__init__(parent)

        ## We store in self.__coeffs the list of all coefficients corresponding to (1,eta',...,eta'^{n-1})
        ## We fill with zeros if not long enough sequence is provided.
        self.__coeffs = tuple([parent.algebraic().base()(c) for c in coeffs] + (parent.degree()-len(coefficients))*[parent.algebraic().base().zero()])

    ###################################################################################
    ### Property methods
    ###################################################################################
    def is_zero(self) -> bool: #: Checker for the zero element
        return all(c == 0 for c in self.__coeffs)

    def is_one(self) -> bool: #: Checker for the one element
        return self.__coeffs[0] == 1 and all(c == 0 for c in self.__coeffs[1:])

    @property
    def coeffs(self) -> tuple[Element]:
        return self.__coeffs

    @cached_method
    def algebraic(self) -> Element:
        y = self.parent().algebraic().gens()[0]

        return sum(self.__coeffs[i]*y**i for i in range(self.parent().degree()))

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: DElliptic_Element) -> DElliptic_Element:
        return DElliptic_Element(self.parent(), *[self.__coeffs[i] + other.__coeffs[i] for i in range(self.parent().degree())])
    
    def _neg_(self, other: DElliptic_Element) -> DElliptic_Element:
        return DElliptic_Element(self.parent(), *[-self.__coeffs[i] for i in range(self.parent().degree())])

    def _sub_(self, other: DElliptic_Element) -> DElliptic_Element:
        return self + (-other)

    def _mul_(self, other: DElliptic_Element) -> DElliptic_Element:
        return DElliptic_Element(self.parent(), *list(self.parent().matrix_mul()*vector(self.__coeffs)))

    def _inv_(self) -> DElliptic_Element:
        return self.parent()(~self.algebraic())
        
    @cached_method
    def __pow__(self, power: int) -> PseudoDOperator:
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
        if self.is_zero():
            return "0"
        parts = []
        for i,coeff in enumerate(self.__coeffs):
            if coeff != 0:
                var = f"" if i == 0 else f"{self.parent().varname()}'" if i == 1 else f"({self.parent().varname()}')^{i}"
                parts.append(f"({coeff})*{var}")
        return "+".join(parts)

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
    ## TODO: GO on here
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
