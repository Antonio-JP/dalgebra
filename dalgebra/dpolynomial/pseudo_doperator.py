from __future__ import annotations

r'''
    Module to create pseudo-differential operators.

    EXAMPLES::

        sage: from dalgebra import DifferentialPolynomialRing
        sage: from dalgebra.dpolynomial.pseudo_doperator import PseudoDOperatorRing
        sage: R.<u,v> = DifferentialPolynomialRing(QQ)
        sage: S = PseudoDOperatorRing(R, "D")
        sage: S
        Ring of pseudo-differential operators over Ring of operator polynomials in (u, v) over Differential Ring [[Rational Field], (0,)]
        sage: S.Di^2 * v[1] * S.D^2 * u[0] == u[0]*v[1] - 2*S.Di*(u[0]*v[2]) + S.Di^2*(u[0]*v[3])
        True
'''
from sage.categories.algebras import Algebras
from sage.categories.category import Category
from sage.categories.morphism import Morphism
from sage.categories.pushout import ConstructionFunctor
from sage.functions.other import binomial
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.rings.infinity import Infinity
from sage.rings.integer_ring import ZZ
from sage.structure.element import Element
from sage.structure.factory import UniqueFactory
from sage.structure.parent import Parent

from typing import Collection, Mapping

from ..dring import AdditiveMap, DRings

_DRings = DRings.__classcall__(DRings)

class PseudoDOperatorRingFactory(UniqueFactory):
    r'''
        Factory to create the ring of pseudo-differential operators.

        This allows to cache the same rings created from different objects. See
        :class:`PseudoDOperator_Ring` for further information on this structure.
    '''
    def create_key(self, base, name: str, **kwds):
        # We check now whether the base ring is valid or not
        if base not in _DRings:
            raise TypeError("The base ring must have operators attached")
        elif base.noperators() != 1 or not base.is_differential():
            raise TypeError("The given ring must e a differential ring with just 1 derivation.")
        
        if name in (str(v) for v in base.gens()):
            raise TypeError(f"The given name ({name}) already exist in the base ring.")

        # Now the names are appropriate and the base is correct
        return (base, name)

    def create_object(self, _, key) -> PseudoDOperator_Ring:
        base, name = key

        return PseudoDOperator_Ring(base, name)

PseudoDOperatorRing = PseudoDOperatorRingFactory("dalgebra.dpolynomial.pseudo_doperator.PseudoDOperator")

class PseudoDOperator(Element): 
    def __init__(self, parent: PseudoDOperator_Ring, positive: Collection[Element] | Mapping[int, Element], negative: Mapping[tuple[int,Element], Element]):
        base = parent.base()
        ## Managing the positive part (usual differential operator)
        if isinstance(positive, (list, tuple)):
            positive = {i : element for (i,element) in enumerate(positive)}
        elif not isinstance(positive, dict):
            raise TypeError(f"The positive part must be a dictionary")
        elif any(i not in ZZ or i < 0 for i in positive):
            raise TypeError(f"The keys for a positive part must be non-negative integers")
        self.__positive = dict()
        for i, element in positive.items():
            element = base(element)
            if element != base.zero(): # we clean trivial terms
                self.__positive[ZZ(i)] = element

        ## Managing the negative part (pseudo-differential part)
        ## We store elements of the form a*D^{-i}*b where `a, b` are elements in the parent
        if not isinstance(negative, dict):
            raise TypeError(f"The negative part must be a dictionary")
        elif any((i not in ZZ or i >= 0 or v not in parent.base()) for (i,v) in negative):
            raise TypeError(f"The keys for a negative part must be NEGATIVE integers")
        self.__negative = dict()
        for (i, after), before in negative.items():
            before, after = base(before), base(after)
            if before != base.zero() and after != base.zero(): # we clean trivial terms
                if after.derivative() == 0: # Simplifying constant on the right side of the product
                    before = before * after
                    after = base.one()
                key = (ZZ(i), after)
                if key not in self.__negative:
                    self.__negative[key] = before
                else:
                    self.__negative[key] += before

        super().__init__(parent)

    ###################################################################################
    ### Property methods
    ###################################################################################
    def is_zero(self) -> bool: #: Checker for the zero element
        return len(self.__positive) + len(self.__negative) == 0
    
    def is_identity(self) -> bool: #: Checker for the one element of the ring
        return (len(self.__positive) == 1 and len(self.__negative) == 0 
                and self.__positive.get(0, None) == self.parent().one())
    
    def is_differential(self) -> bool: #: Checker whether the operator is differential or not (i.e., has no pseudo part)
        return len(self.__negative) == 0
    
    def is_simple(self) -> bool: #: Checker for all pseudo part be of the form a*D^{-1} (without afters)
        return all(after == self.parent().one() for (_,after) in self.__negative.keys())
    
    def positive_order(self) -> int:
        r'''
            Method to get the positive order of a pseudo-differential operator.

            For the zero element we return -Infinity.
        '''
        if len(self.__positive) > 0:
            return max(self.__positive)
        elif len(self.__negative) > 0:
            return max(k for k,_ in self.__negative)
        else:
            return -Infinity
        
    def negative_order(self) -> int:
        r'''
            Method to get the positive order of a pseudo-differential operator.

            For the zero element we return -Infinity.
        '''
        if len(self.__negative) > 0:
            return min(k for (k,_) in self.__negative)
        elif len(self.__positive) > 0:
            return min(self.__positive)
        else:
            return Infinity
        
    def differential_part(self) -> PseudoDOperator:
        r'''Return a :class:`PseudoDOperator` that contains only the differential part of ``self``'''
        return self.parent().element_class(self.parent(), self.__positive, dict())
    
    def pseudo_part(self) -> PseudoDOperator:
        r'''Return a :class:`PseudoDOperator` that contains only the pseudo-differential part of ``self``'''
        return self.parent().element_class(self.parent(), dict(), self.__negative)
    
    def lie_bracket(self, other: PseudoDOperator) -> PseudoDOperator:
        if not isinstance(other, self.__class__) or other.parent() != self.parent():
            other = self.parent()(other)

        return self*other - other*self

    ###################################################################################
    ### Arithmetic operations
    ###################################################################################
    def _add_(self, other: PseudoDOperator) -> PseudoDOperator:
        ## Adding the positive parts
        positive = self.__positive.copy()
        for (k, element) in other.__positive.items():
            if k in positive:
                element = element + positive[k]
            positive[k] = element

        ## Adding the negative parts (if possible)
        negative = self.__negative.copy()
        for (k, oa), ob in other.__negative.items():
            if (k, oa) not in negative: 
                negative[(k, oa)] = ob
            else:
                negative[(k, oa)] += ob                
        
        return self.parent().element_class(self.parent(), positive, negative)
    
    def __neg__(self) -> PseudoDOperator:
        positive = {k: -element for (k,element) in self.__positive.items()}
        negative = {(k, after): -before for ((k, after), before) in self.__negative.items()}

        return self.parent().element_class(self.parent(), positive, negative)
    
    def _sub_(self, other: PseudoDOperator) -> PseudoDOperator:
        return self + (-other)
    
    def _mul_(self, other: PseudoDOperator) -> PseudoDOperator:
        sp, sn = self.__positive, self.__negative
        op, on = other.__positive, other.__negative

        positive = dict()
        negative = dict()

        ## POSITIVE PART OF SELF
        for (k, a) in sp.items():
            ## POSITIVE PART OF OTHER
            for (n, c) in op.items():
                for i in range(k+1):
                    if (k-i+n) not in positive:
                        positive[k-i+n] = self.parent().base().zero()
                    positive[k-i+n] = a*binomial(k, i)*c.derivative(times=i)
            ## NEGATIVE PART OF OTHER
            for ((n, d), c) in on.items():
                n = -n # we make n positive
                for i in range(0, k-n+1):
                    for j in range(0, k-i-n+1):
                        if (k-i-n-j) not in positive:
                            positive[k-i-n-j] = self.parent().base().zero()
                        positive[k-i-j-n] += binomial(k,i)*a*c.derivative(times=i)*binomial(k-i-n,j)*d.derivative(times=j)
                for i in range(max(0,k-n+1), k+1):
                    if (k-i-n, d) not in negative:
                        negative[(k-i-n, d)] = binomial(k,i) * a * c.derivative(times=i)
                    else:
                        negative[(k-i-n, d)] += binomial(k,i) * a * c.derivative(times=i)
        
        ## NEGATIVE PART OF SELF
        for ((k, b), a) in sn.items():
            k = -k # we make it positive
            ## POSITIVE PART OF OTHER
            for (n, c) in op.items():
                for i in range(0,n-k+1):
                    for j in range(0,n-k-i+1):
                        if (n-k-i-j) not in positive:
                            positive[n-k-i-j] = (-1)**i*a*binomial(n-k-i,j)*binomial(n,i)*(b*c).derivative(times=i+j)
                        else:
                            positive[n-k-i-j] += (-1)**i*a*binomial(n-k-i,j)*binomial(n,i)*(b*c).derivative(times=i+j)
                for i in range(max(0,n-k+1), n+1):
                    after = (b*c).derivative(times=i)
                    if (n-k-i, after) not in negative:
                        negative[(n-k-i, after)] = (-1)**i*a*binomial(n,i)
                    else:
                        negative[(n-k-i, after)] += (-1)**i*a*binomial(n,i)
            ## NEGATIVE PART OF OTHER
            for ((n, d), c) in on.items():
                n = -n # we make it positive
                if (b*c).derivative() == 0: # we can do something
                    if (-n-k, d) not in negative:
                        negative[(-n-k, d)] = a*b*c
                    else:
                        negative[(-n-k, d)] += a*b*c
                else:
                    return NotImplemented ## These cases are not well implemented yet
        
        return self.parent().element_class(self.parent(), positive, negative)
            
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
        
        return (self - other).is_zero()
    
    def __ne__(self, other) -> bool:
        return not (self == other)
    
    def __hash__(self) -> int:
        return hash((sorted(self.__positive.items()), sorted(self.__negative.items(), key=lambda t : (t[0][0], len(str(t[0][1]))))))
    
    def __call__(self, element: Element) -> Element:
        result = sum((C*element.derivative(times=i) for (i, C) in self.__positive.items()), self.parent().base().zero())
        for ((i,a), b) in self.__negative.items():
            result += b * (element*a).integrate(times=-i)

        return result
    
    @cached_method
    def __repr__(self) -> str:
        if self.is_zero():
            return "0"
        elif self.is_identity():
            return "1"
        
        ## We know there is something in the element
        g = self.parent().gen_name()
        def term_str(order, element):
            if isinstance(order, (list, tuple)):
                order, after = order
                before = "" if element == 1 else f"({element})"
                after = "" if after == 1 else f"({after})"
            else:
                before = "" if element == 1 else f"({element})"
                after = ""
            order = f"{g}^({order})" if order < 0 else f"{g}^{order}" if order > 1 else g if order == 1 else ""

            return "*".join([el for el in [before, order, after] if el != ""])
        
        def sorting_key(_tuple):
            if not isinstance(_tuple[0], (list, tuple)):
                return (_tuple[0],)
            else:
                return (_tuple[0][0], len(str(_tuple[0][1])), str(_tuple[0][1]))

        return " + ".join(
            term_str(o, el) for (o,el) in 
            sorted(list(self.__positive.items()) + list(self.__negative.items()), key=sorting_key, reverse=True)
        )
        
    @cached_method
    def _latex_(self) -> str:
        if self.is_zero():
            return "0"
        elif self.is_identity():
            return "1"
        
        ## We know there is something in the element
        g = self.parent().gen_name()
        def term_str(order, element):
            if isinstance(order, (list, tuple)):
                order, after = order
                before = "" if element == 1 else f"\\left({latex(element)}\\right)"
                after = "" if after == 1 else f"\\left({latex(after)}\\right)"
            else:
                before = "" if element == 1 else f"\\left({latex(element)}\\right)"
                after = ""
            order = f"{g}^{{{order}}}" if order not in {0,1} else g if order == 1 else ""

            return f"{before}{order}{after}"
        
        def sorting_key(_tuple):
            if not isinstance(_tuple[0], (list, tuple)):
                return (_tuple[0],)
            else:
                return (_tuple[0][0], len(str(_tuple[0][1])), str(_tuple[0][1]))
        
        return " + ".join(term_str(o, el) for (o,el) in sorted(list(self.__positive.items()) + list(self.__negative.items()), key=sorting_key, reverse=True))
    
class PseudoDOperator_Ring(Parent):
    r'''
        Class for a ring of pseudo-differential operators over a :class:`~dalgebra.dring.DRing`.

        Given a differential ring `(R, \partial)`, where `\partial` is a derivation, we can
        always define the ring of pseudo-differential operators `R\langle partial\rangle` whose elements
        are Laurent series in `\partial^{-1}`.

        Similar to the case of Ore Algebras, this ring of pseudo-differential operators is not commutative, meaning
        that `AB \neq BA`. The commutation rules that define this commutation, are induced by Leibniz derivation rule:

        .. MATH::

            \partial f = f' + f\partial,

        for any element `f \in R`. For the `\partial^{-1}`, we use the only reasonable choice, who leads to an infinite 
        tail of negative derivations:

        .. MATH::

            partial^{-1} f = f\partial^{-1} + \partial^{-1} f' \partial^{-1} = f\partial^{-1} - f'\partial^{-2} + f''\partial^{-3} - \ldots

        This make the computation with these objects terribly difficult. Hence we propose here an implementation of a *subring* 
        of the pseudo differential operators that include the ring of linear differential operators and allow all possible computations 
        that keep the tail as finit eas possible (keeping all computations exact).

        INPUT:

        * ``base``: a differential ring with just one operation.
        * ``name``: name that the differential operator will receive (use mostly for cosmetic reasons).

        TODO: add examples
    '''
    Element = PseudoDOperator

    def _set_categories(self, base : Parent, category=None) -> list[Category]: return [_DRings, Algebras(base)] + ([category] if category is not None else [])

    def __init__(self, base : Parent, name : str, category=None):
        if base not in _DRings:
            raise TypeError("The base must be a ring with operators")
        if base.noperators() != 1 or not base.is_differential():
            raise TypeError("The base must be a differential ring with 1 operation")
        
        ## Setting the inner variables of the ring
        super().__init__(base, category=tuple(self._set_categories(base, category)))

        self.__gens = [name]
        self.D = self.element_class(self, [0, base.one()], dict())
        self.Di = self.element_class(self, [], {(-1,base.one()): base.one()})
        self.__operators = [AdditiveMap(self, lambda p : self.D * p)]

    ################################################################################
    ### GETTER METHODS
    ################################################################################
    def gen_name(self) -> str:
        return self.__gens[0]
    #################################################
    ### Coercion methods
    #################################################
    def _element_constructor_(self, x) -> PseudoDOperator:
        if not isinstance(x, PseudoDOperator):
            x = self.base()(x) # Casting to the base ring
            return self.element_class(self, [x], dict())
        
        ## This should fail if the base of `x.parent()` is not included in `self.base()`
        return self.element_class(self, x._PseudoDOperator__positive, x._PseudoDOperator__negative)

    def _coerce_map_from_base_ring(self):
        return CoerceFromBaseMorphism(self.base(), self)

    def construction(self) -> tuple[PseudoDOperatorFunctor, Parent]:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.
        '''
        return PseudoDOperatorFunctor(self.__gens[0]), self.base()

    def fraction_field(self):
        raise NotImplementedError("Pseudo differential Operators does not allow a fraction field structure.")

    def change_base(self, R) -> PseudoDOperator_Ring:
        new_ring = PseudoDOperatorRing(R, self.gen_name())
        ## Creating the coercion map if possible
        try:
            M = CoerceMapBetweenBases(self, new_ring, R.coerce_map_from(self.base()))
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
    ) -> PseudoDOperator:
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

    def add_constants(self, *new_constants: str) -> PseudoDOperator_Ring:
        return PseudoDOperatorRing(self.base().add_constants(*new_constants), self.__gens[0])

    def linear_operator_ring(self) -> PseudoDOperator_Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the
            ring of operator polynomials only have one variable.
        '''
        return self

    def inverse_operation(self, element: PseudoDOperator, operation: int = 0) -> PseudoDOperator:
        if element not in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if operation != 0: 
            raise ValueError(f"The given operation({operation}) is not valid")

        try:
            return self.Di * element
        except Exception:
            raise NotImplementedError(f"The multiplication of {self.__gens[0]}^(-1) * {element} can not be computed.")

class PseudoDOperatorFunctor(ConstructionFunctor):
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
    def __init__(self, name: str):
        self.__operator_name = name
        super().__init__(_DRings,_DRings)
        self.rank = 13 # just above DPolyRingFunctor

    ### Methods to implement
    def _apply_functor(self, x):
        return PseudoDOperatorRing(x,self.__operator_name)

    def _repr_(self):
        return f"PseudoDOperators(*,{self.__operator_name})"

    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return self.__operator_name == other.__operator_name

class CoerceFromBaseMorphism(Morphism):
    def __init__(self, domain, codomain):
        if not codomain.base() == domain:
            raise ValueError(f"Morphism has incorrect parents as domain and codomain")

        super().__init__(domain, codomain)

    def _call_(self, element):
        return self.codomain().element_class(self.codomain(), [self.domain()(element)], dict())
    
class CoerceMapBetweenBases(Morphism):
    def __init__(self, domain, codomain, map):
        if not map.domain() == domain.base() or not map.codomain() == codomain.base():
            raise ValueError("Error in the format for the morphism")
        
        self.base_map = map

        super().__init__(domain, codomain)

    def _call_(self, element):
        positive = {k : self.base_map(e) for (k,e) in element._PseudoDOperator__positive.items()}
        negative = {(k, self.base_map(a)) : b for ((k,a), b) in element._PseudoDOperator__negative.items()}

        return self.codomain().element_class(self.codomain(), positive, negative)