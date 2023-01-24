r"""
File for the ring structure of Differential polynomials

This file contains all the parent structures for Differential polynomials
and all the coercion associated classes. Mainly, this module provides the 
class :class:`DifferentialPolynomialRing_dense`, which is the main parent class defining
a ring of differential polynomials.

EXAMPLES::

    sage: from dalgebra import DifferentialPolynomialRing
    sage: R.<y> = DifferentialPolynomialRing(QQ['x']) 
    sage: x = R.base().gens()[0] 
    sage: p = x^2*y[1]^2 - y[2]*y[1]; p
    -y_2*y_1 + x^2*y_1^2
    sage: R
    Ring of differential polynomials in (y) over Differential Ring [Univariate 
    Polynomial Ring in x over Rational Field] with derivation [Map from 
    callable d/dx]

AUTHORS:

    - Antonio Jimenez-Pastor (2021-05-19): initial version

"""

# ****************************************************************************
#  Copyright (C) 2021 Antonio Jimenez-Pastor <ajpastor@risc.uni-linz.ac.at>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import annotations

from itertools import product

from sage.all import cached_method, ZZ, latex, diff, prod, CommutativeRing, random, Parent
from sage.categories.all import Morphism, Category, CommutativeAlgebras
from sage.categories.pushout import ConstructionFunctor
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from typing import Collection

from .rwo_polynomial_element import RWOPolynomial, RWOPolynomialGen, IndexBijection
from ..ring_w_operator import RingsWithOperators, AdditiveMap, DifferentialRing, DifferenceRing

_RingsWithOperators = RingsWithOperators.__classcall__(RingsWithOperators)

## Factories for all structures
class RWOPolynomialRingFactory(UniqueFactory):
    r'''
        Factory to create a ring of polynomials over a ring with operators.

        This allows to cache the same rings created from different objects. See
        :class:`RWOPolynomialRing_dense` for further information on this structure.
    '''
    def create_key(self, base, *names : str, **kwds):
        if "names" in kwds and len(names) > 0:
            raise ValueError("Duplicated values for names")
        if len(names) == 1 and isinstance(names[0], (list, tuple)):
            names = names[0]
        names = tuple(kwds.pop("names", names))

        # We check now if base is an infinite polynomial ring to gather more names or not
        if isinstance(base, InfinitePolynomialRing_dense) or isinstance(base, InfinitePolynomialRing_sparse):
            names = tuple(list(base._names) + list(names))
            base = base.base()

        if len(names) == 0:
            raise ValueError("No variables given: impossible to create a ring")
        if len(set(names)) < len(names):
            raise ValueError("Repeated names given: impossible to create the ring")

        # We check now whether the base ring is valid or not
        base = self._check_base_ring(base)

        # Now the names are appropriate and the base is correct
        return (base, names)

    def _check_base_ring(self, base):
        if not base in _RingsWithOperators:
            raise TypeError("The base ring must have operators attached")
        return base

    def create_object(self, _, key):
        base, names = key

        return RWOPolynomialRing_dense(base, names)

class DifferentialPolynomialRingFactory(RWOPolynomialRingFactory):
    def _check_base_ring(self, base):
        if not base in _RingsWithOperators:
            return DifferentialRing(base, diff)
        if not base.is_differential():
            raise TypeError("The base ring must be a differential ring")
        return super()._check_base_ring(base)

class DifferencePolynomialRingFactory(RWOPolynomialRingFactory):
    def _check_base_ring(self, base):
        if not base in _RingsWithOperators:
            return DifferenceRing(base, base.Hom(base).one())
        if not base.is_difference():
            raise TypeError("The base ring must be a difference ring")
        return super()._check_base_ring(base)

RWOPolynomialRing = RWOPolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.RWOPolynomialRing")
DifferentialPolynomialRing = DifferentialPolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.DifferentialPolynomialRing")
DifferencePolynomialRing = DifferencePolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.DifferencePolynomialRing")

class RWOPolynomialRing_dense (InfinitePolynomialRing_dense):
    r'''
        Class for a ring of polynomials over a :class:`~dalgebra.ring_w_operator.RingWithOperators`.

        Given a ring with an associated operators `(R, (d_1,...,d_n))`, where `d_i : R \rightarrow R`, we can 
        always define the ring of polynomials on `y` as the *infinite polynomial ring*

        .. MATH::

            R[y_\sigma : \sigma \in \mathbb{N}^n]

        where the operations acts naturally (preserving all its properties) over this ring and,
        in particular, `d_i(y_\sigma) = y_{\sigma+e_i}` where `\e_i` is the `i`-th canonical vector
        of `\mathbb{N}^n` (i.e., all zeros but the `i`-th coordinate).

        This class represents exactly the ring of polynomials with these operator over the given ring ``base`` 
        with variables given in ``names``.

        This class inherits from :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`,
        which is the Sage structure to manipulate polynomial rings over infinitely many variables.

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R` (has to be in the 
          category :class:`RingsWithOperator`)
        * ``names``: set of names for the variables of the new ring.

        REMARK:

        The behavior of the operations with respect with the multiplication must be explicit (namely, they must 
        all be ''homomorphism'', ''derivation'' or ''skew''). See documentation of :mod:`dalgebra.ring_w_operator`
        for further information.

        EXAMPLES (FROM DIFFERENTIAL_POLYNOMIAL_RING)::

            sage: from dalgebra import DifferentialPolynomialRing
            sage: R.<y> = DifferentialPolynomialRing(QQ['x']); R
            Ring of differential polynomials in (y) over Differential Ring 
            [Univariate Polynomial Ring in x over Rational Field] with derivation 
            [Map from callable d/dx]
            sage: S.<a,b> = DifferentialPolynomialRing(ZZ); S
            Ring of differential polynomials in (a, b) over Differential Ring [Integer Ring] 
            with derivation [Map from callable 0]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: diff(y[1])
            y_2
            sage: diff(a[1]*b[0]) #Leibniz Rule
            a_2*b_0 + a_1*b_1

        EXAMPLES (FROM DERIVATIVE METHOD)::

            sage: from dalgebra import DifferentialPolynomialRing
            sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
            sage: R.derivation(y[0])
            y_1
            sage: R.derivation(x)
            1
            sage: R.derivation(x*y[10])
            x*y_11 + y_10
            sage: R.derivation(x^2*y[1]^2 - y[2]*y[1])
            -y_3*y_1 - y_2^2 + 2*x^2*y_2*y_1 + 2*x*y_1^2

        This derivation also works naturally with several infinite variables::

            sage: S = DifferentialPolynomialRing(R, 'a'); a,y = S.gens()
            sage: S.derivation(a[1] + y[0]*a[0])
            a_1*y_0 + a_0*y_1 + a_2

        EXAMPLES (FROM DIFFERENCE_POLYNOMIAL_RING)::

            sage: from dalgebra import DifferencePolynomialRing
            sage: R.<y> = DifferencePolynomialRing(QQ['x']); R
            Ring of difference polynomials in (y) over Difference Ring [Univariate 
            Polynomial Ring in x over Rational Field] with difference [Map from 
            callable [x] |--> [x]]
            sage: S.<a,b> = DifferencePolynomialRing(ZZ); S
            Ring of difference polynomials in (a, b) over Difference Ring [Integer Ring] 
            with difference [Map from callable [1] |--> [1]]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: y[1].difference()
            y_2
            sage: (a[1]*b[0]).difference() #Homomorphism rule
            a_2*b_1

        EXAMPLES (FROM DIFFERENCE METHOD)::

            sage: from dalgebra import DifferencePolynomialRing
            sage: R.<y> = DifferencePolynomialRing(QQ['x']); x = R.base().gens()[0]
            sage: R.difference(y[0])
            y_1
            sage: R.difference(x)
            x
            sage: R.difference(x*y[10])
            x*y_11
            sage: R.difference(x^2*y[1]^2 - y[2]*y[1])
            -y_3*y_2 + x^2*y_2^2

        This difference also works naturally with several infinite variables::

            sage: S = DifferencePolynomialRing(R, 'a'); a,y = S.gens()
            sage: S.difference(a[1] + y[0]*a[0])
            a_1*y_1 + a_2

        We can see other type of shifts or differences operators::

            sage: X = QQ[x]('x')
            sage: T.<z> = DifferencePolynomialRing(QQ[x], difference=lambda p : p(x=X+1)); x = T.base().gens()[0]
            sage: T.difference(z[0])
            z_1
            sage: T.difference(x)
            x + 1
            sage: T.difference(x^2*z[1]^2 - z[2]*z[1])
            -z_3*z_2 + (x^2 + 2*x + 1)*z_2^2
    '''
    Element = RWOPolynomial

    def _base_category(self) -> Category: return _RingsWithOperators

    def _set_categories(self, base : Parent) -> list[Category]: return [_RingsWithOperators, CommutativeAlgebras(base)]

    def __init__(self, base : Parent, names : Collection[str]):
        if not base in _RingsWithOperators:
            raise TypeError("The base must be a ring with operators")

        if any(ttype == "none" for ttype in base.operator_types()):
            raise TypeError(f"All operators in {base} must be typed")

        ## Line to set the appropriate parent class
        CommutativeRing.__init__(self, base, category=self._set_categories(base))
        ## Initializing the ring of infinitely many variables
        super().__init__(base, names, 'deglex')
        ## Resetting the category to be the appropriate
        CommutativeRing.__init__(self, base, category=self._set_categories(base))
        
        # registering conversion to simpler structures
        current = self.base()
        morph = RWOPolySimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = RWOPolySimpleMorphism(self, current)
            current.register_conversion(morph)

        self.__operators : tuple[AdditiveMap] = tuple([
            self._create_operator(operation, ttype) 
            for operation, ttype in enumerate(self.base().operator_types())
        ])
        self.__cache : list[dict[RWOPolynomial, RWOPolynomial]] = len(self.__operators)*[dict()]

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S: Parent) -> bool:
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, x) -> RWOPolynomial:
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into the corresponding type for ``self``.
        '''
        p = super()._element_constructor_(x)
        return self.element_class(self, p)

    @cached_method
    def gen(self, i: int = None) -> RWOPolynomialGen:
        r'''
            Override method to create the `i^{th}` generator (see method 
            :func:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse.gen`).

            For a :class:`RWOPolynomialRing_dense`, the generator type is 
            :class:`~dalgebra.diff_polynomial.diff_polynomial_element.RWOPolynomialGen`
            which provides extra features to know if an object can be generated by that generator.
            See tis documentation for further details.

            INPUT:

            * ``i``: index of the required generator.

            OUTPUT:

            A :class:`~dalgebra.diff_polynomial.diff_polynomial_element.RWOPolynomialGen`
            representing the `i^{th}` generator of ``self``.

            EXAMPLES::

                sage: from dalgebra import RWOPolynomialRing
                sage: from dalgebra.diff_polynomial.diff_polynomial_element import RWOPolynomialGen
                sage: R.<y> = RWOPolynomialRing(QQ['x'])
                sage: R.gen(0)
                y_*
                sage: R.gen(0) is y
                True
                sage: isinstance(R.gen(0), RWOPolynomialGen)
                True
                sage: S = RWOPolynomialRing(ZZ, ('a', 'b'))
                sage: S
                Ring of infinite polynomials in (a, b) over Ring [Integer Ring] with 
                operator [Map from callable <lambda>]
                sage: S.gen(0)
                a_*
                sage: S.gen(1)
                b_*
        '''
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return RWOPolynomialGen(self, self._names[i])
                
    def construction(self) -> RWOPolyRingFunctor:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`RWOPolynomialRing_dense`, the associated functor class is :class:`RWOPolyRingFunctor`.
            See its documentation for further information.
        '''
        return RWOPolyRingFunctor(self._names), self.base()
    
    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds) -> RWOPolynomial:
        res = super().__call__(*args, **kwds)
        if not isinstance(res, self.element_class):
            res = self.element_class(self, res)
        return res

    ## Other magic methods   
    def __repr__(self) -> str:
        return f"Ring of infinite polynomials in {self._names}) over {self.base()}"

    def _latex_(self) -> str:
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self) -> RWOPolynomial:
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RWOPolynomialRing, DifferentialRing
                sage: R.<y> = RWOPolynomialRing(DifferentialRing(QQ['x'], diff))
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self) -> RWOPolynomial:
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RWOPolynomialRing, DifferentialRing
                sage: R.<y> = RWOPolynomialRing(DifferentialRing(QQ['x'], diff))
                sage: R.zero()
                0
        '''
        return self(0)
    
    def random_element(self,
        deg_bound : int = 0,order_bound : int = 0, sparsity : float = 0.75,
        *args,**kwds
    ):
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
        deg_bound = 0 if ((not deg_bound in ZZ) or deg_bound < 0) else deg_bound
        order_bound = 0 if ((not order_bound in ZZ) or order_bound < 0) else order_bound
        gens = self.gens(); n = len(gens)
        p = 0
        for degrees in IndexBijection(n).iter(deg_bound):
            for list_orders in product(*(sum(degrees)*[IndexBijection(self.noperators()).iter(order_bound)])):
                if random() > sparsity:
                    p += self.base().random_element(*args, **kwds) * prod(gens[i][orders] for (i,orders) in enumerate(list_orders))
        
        return p
     
    def eval(self, element, *args, **kwds):
        r'''
            Method to evaluate elements in the ring of differential polynomials.

            Since the infinite polynomials have an intrinsic meaning (namely, the 
            variables are related by the operator), evaluating a polynomial
            is a straight-forward computation once the objects for the ``*_0`` term is given.

            This method evaluates elements in ``self`` following that rule.

            INPUT:

            * ``element``: element (that must be in ``self``) to be evaluated
            * ``args``: list of arguments that will be linearly related with the generators
              of ``self`` (like they are given by ``self.gens()``)
            * ``kwds``: dictionary for providing values to the generators of ``self``. The 
              name of the keys must be the names of the generators (as they can be got using 
              the attribute ``_name``).

            We allow a mixed used of ``args`` and ``kwds`` but an error will be raised if

            * There are too many arguments in ``args``,
            * An input in ``kwds`` is not a valid name of a generator,
            * There are duplicate entries for a generator.

            OUTPUT:

            The resulting element after evaluating the variable `\alpha_n = d^n(\alpha)`,
            where `\alpha` is the name of the generator.

            EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing
                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: R.eval(y[1], 0)
                0
                sage: R.eval(y[0] + y[1], x)
                x + 1
                sage: R.eval(y[0] + y[1], y=x)
                x + 1

            This method commutes with the use of :func:`derivation`::

                sage: R.eval(R.derivation(x^2*y[1]^2 - y[2]*y[1]), y=x) == R.derivation(R.eval(x^2*y[1]^2 - y[2]*y[1], y=x))
                True

            This evaluation also works naturally with several infinite variables::

                sage: S = DifferentialPolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.eval(a[1] + y[0]*a[0], a=x, y=x^2)
                x^3 + 1
                sage: in_eval = S.eval(a[1] + y[0]*a[0], y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of differential polynomials in (a) over Differential Ring [Univariate Polynomial Ring in x over 
                Rational Field] with derivation [Map from callable d/dx]
        '''
        # if(not element in self):
        #     raise TypeError("Impossible to evaluate %s as an element of %s" %(element, self))
        # g = self.gens(); final_input = {}
        # names = [el._name for el in g]
        # if(len(args) > self.ngens()):
        #     raise ValueError("Too many argument for evaluation: given %d, expected (at most) %d" %(len(args), self.ngens()))
        # for i in range(len(args)):
        #     final_input[g[i]] = args[i]
        # for key in kwds:
        #     if(not key in names):
        #         raise TypeError("Invalid name for argument %s" %key)
        #     gen = g[names.index(key)]
        #     if(gen in final_input):
        #         raise TypeError("Duplicated value for generator %s" %gen)
        #     final_input[gen] = kwds[key]

        # max_application = {gen: 0 for gen in final_input}
        # for v in element.variables():
        #     for gen in max_application:
        #         if(gen.contains(v)):
        #             max_application[gen] = max(max_application[gen], gen.index(v))
        #             break
        
        # to_evaluate = {}
        # for gen in max_application:
        #     for i in range(max_application[gen]+1):
        #         to_evaluate[str(gen[i])] = parent(final_input[gen])(self._apply_to_outside(final_input[gen], i))

        # ## Computing the final ring
        # values = list(final_input.values())
        # R = self.base()
        # for value in values:
        #     R = pushout(R, parent(value))

        # poly = element.polynomial()
        # ## Adding all the non-appearing variables on element
        # if(len(final_input) == len(g)):
        #     for v in poly.parent().gens():
        #         if (v not in poly.variables()) and (not str(v) in to_evaluate):
        #             to_evaluate[str(v)] = 0
        # else:
        #     left_gens = [gen for gen in g if gen not in final_input]
        #     R = self.construction()[0].__class__([el._name for el in left_gens])(R)
        #     for v in poly.parent().gens():
        #         if (not any(gen.contains(v) for gen in left_gens)) and (not str(v) in to_evaluate):
        #             to_evaluate[str(v)] = 0

        # return R(poly(**to_evaluate))
        raise NotImplementedError("Evaluation not yet implemented") # TODO

    #################################################
    ### Method from RingWithOperators category
    #################################################
    def operators(self) -> Collection[Morphism]:
        return self.__operators

    def operator_types(self) -> tuple[str]:
        return self.base().operator_types()

    def _create_operator(self, operation: int, ttype: str) -> AdditiveMap:
        r'''
            Method to create a map on the ring of polynomials from an operator on the base ring.

            We create an :class:`AdditiveMap` from the given operator assuming the type given in ``ttype``.
            This type will determine how the multiplication behaves with respect to the different variables.
        '''
        operator : AdditiveMap = self.base().operators()[operation] 
        if ttype == "homomorphism":
            def __extended_homomorphism(element : RWOPolynomial) -> RWOPolynomial:
                if(element in self):
                    element = self(element)
                else:
                    element=self(str(element))
                    
                if(element in self.base()):
                    return operator(self.base()(element))
                
                if(not element in self.__cache[operation]):
                    generators = self.gens()
                    if(element.is_monomial()):
                        c = element.coefficients()[0]
                        m = element.monomials()[0]
                        v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                        v = [self(str(el)) for el in v]

                        result = operator(c)
                        for i in range(len(v)):
                            for g in generators:
                                if g.contains(v[i]):
                                    index = list(g.index(v[i])); index[operation] += 1
                                    result *= g[tuple(index)]**d[i]
                                    break
                        
                        self.__cache[element] = result
                    else:
                        c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                        self.__cache[operation][element] = sum(operator(c[i])*__extended_homomorphism(m[i]) for i in range(len(m)))
                        
                return self.__cache[operation][element]
            func = __extended_homomorphism
        elif ttype == "derivation":
            def __extended_derivation(element : RWOPolynomial) -> RWOPolynomial:
                if(element in self):
                    element = self(element)
                else:
                    element=self(str(element))
                    
                if(element in self.base()):
                    return operator(self.base()(element))
                
                if(not element in self.__cache[operation]):
                    generators = self.gens()
                    if(element.is_monomial()):
                        c = element.coefficients()[0]
                        m = element.monomials()[0]
                        v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                        v = [self(str(el)) for el in v]
                        base = c*prod([v[i]**(d[i]-1) for i in range(len(v))], self.one())

                        first_term = operator(c)*self(str(m))
                        second_term = self.zero()
                        for i in range(len(v)):
                            to_add = d[i]*prod([v[j] for j in range(len(v)) if j != i], self.one())
                            for g in generators:
                                if(g.contains(v[i])):
                                    index = list(g.index(v[i])); index[operation] += 1
                                    to_add *= g[tuple(index)] # we create the next generator for this operation
                                    break
                            second_term += to_add
                        self.__cache[operation][element] = first_term + base*second_term
                    else:
                        c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                        self.__cache[operation][element] = sum(operator(c[i])*m[i] + c[i]*__extended_derivation(m[i]) for i in range(len(m)))
                        
                return self.__cache[operation][element]
            func = __extended_derivation
        elif ttype == "skew":
            raise NotImplementedError("The 'skew' case is not yet implemented")
            # func = None
        else:
            raise ValueError(f"The type {ttype} is not recognized as a valid operator.")

        return AdditiveMap(self, func) 
    
    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return f"Ring of operator polynomials in ({', '.join(self._names)}) over {self._base}"

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"

def is_RWOPolynomialRing(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, RWOPolynomialRing_dense)

class RWOPolyRingFunctor (ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`RWOPolynomialRing_dense`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential 
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DifferentialPolynomialRing_dense`)
    '''
    def __init__(self, variables):
        self.__variables = variables
        super().__init__(_RingsWithOperators,_RingsWithOperators)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _apply_functor(self, x):
        return RWOPolynomialRing(x,self.variables())
        
    def _repr_(self):
        return f"RWOPolynomialRing((*),{self.variables()})"
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.variables() == self.variables())

    def merge(self, other):
        pass # TODO

    def variables(self):
        return self.__variables

class RWOPolySimpleMorphism (Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`DifferentialPolynomialRing_dense` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        if(p.degree() == 0):
            return self.codomain()(p.coefficients()[0])

        return self.codomain()(str(p))

__all__ = ["RWOPolynomialRing", "DifferentialPolynomialRing", "DifferencePolynomialRing",
            "is_RWOPolynomialRing"]