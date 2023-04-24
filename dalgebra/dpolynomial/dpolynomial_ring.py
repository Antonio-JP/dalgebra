r"""
File for the ring structure of Differential polynomials

This file contains all the parent structures for Differential polynomials
and all the coercion associated classes. Mainly, this module provides the 
class :class:`DifferentialPolynomialRing_dense`, which is the main parent class defining
a ring of differential polynomials.

EXAMPLES::

    sage: from dalgebra import *
    sage: R.<y> = DifferentialPolynomialRing(QQ['x']) 
    sage: x = R.base().gens()[0] 
    sage: p = x^2*y[1]^2 - y[2]*y[1]; p
    -y_2*y_1 + x^2*y_1^2
    sage: R
    Ring of operator polynomials in (y) over Differential Ring [[Univariate Polynomial Ring 
    in x over Rational Field], (d/dx,)]
    sage: p.derivative()
    -y_3*y_1 - y_2^2 + 2*x^2*y_2*y_1 + 2*x*y_1^2

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

import logging

from itertools import product
from functools import reduce

from sage.all import cached_method, ZZ, latex, diff, prod, CommutativeRing, random, Parent, parent, matrix, vector
from sage.categories.all import Morphism, Category, CommutativeAlgebras, Sets
from sage.categories.morphism import SetMorphism # pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring_base import is_MPolynomialRing #pylint: disable=no-name-in-module
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.rings.ring import Ring #pylint: disable=no-name-in-module
from sage.structure.element import Element, Matrix #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from typing import Collection

from .dpolynomial_element import DPolynomial, DPolynomialGen, IndexBijection
from ..dring import DRings, AdditiveMap, DifferentialRing, DifferenceRing, DRing_Wrapper

logger = logging.getLogger(__name__)
_DRings = DRings.__classcall__(DRings)
_Sets = Sets.__classcall__(Sets)

## Factories for all structures
class DPolynomialRingFactory(UniqueFactory):
    r'''
        Factory to create a ring of polynomials over a ring with operators.

        This allows to cache the same rings created from different objects. See
        :class:`DPolynomialRing_dense` for further information on this structure.
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
        names = tuple(sorted(names))

        # We check now whether the base ring is valid or not
        if not base in _DRings:
            raise TypeError("The base ring must have operators attached")

        # Now the names are appropriate and the base is correct
        return (base, names)

    def create_object(self, _, key):
        base, names = key

        return DPolynomialRing_dense(base, names)

DPolynomialRing = DPolynomialRingFactory("dalgebra.dpolynomial.dpolynomial_ring.DPolynomialRing")
RWOPolynomialRing = DPolynomialRing #: alias for DPolynomialRing (used for backward compatility)
def DifferentialPolynomialRing(base, *names : str, **kwds):
    if not base in _DRings:
        base = DifferentialRing(base, diff)
    if not base.is_differential():
        raise TypeError("The base ring must be a differential ring")
    return DPolynomialRing(base, *names, **kwds)
def DifferencePolynomialRing(base, *names : str, **kwds):
    if not base in _DRings:
        base = DifferenceRing(base, base.Hom(base).one())
    if not base.is_difference():
        raise TypeError("The base ring must be a difference ring")
    return DPolynomialRing(base, *names, **kwds)

class DPolynomialRing_dense (InfinitePolynomialRing_dense):
    r'''
        Class for a ring of polynomials over a :class:`~dalgebra.dring.DRing`.

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
        all be ''homomorphism'', ''derivation'' or ''skew''). See documentation of :mod:`dalgebra.dring`
        for further information.

        EXAMPLES::

            sage: from dalgebra import *
            sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]; R
            Ring of operator polynomials in (y) over Differential Ring [[Univariate Polynomial Ring in x over Rational Field], (d/dx,)]
            sage: S.<a,b> = DifferentialPolynomialRing(ZZ); S
            Ring of operator polynomials in (a, b) over Differential Ring [[Integer Ring], (0,)]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: diff(y[1])
            y_2
            sage: diff(a[1]*b[0]) #Leibniz Rule
            a_2*b_0 + a_1*b_1

        Although the use of diff can work in these rings, it is not fully recommended because we may require more 
        information for the ``diff`` method to work properly. We recommend the use of the ``derivative`` methods 
        of the elements or the method ``derivative`` of the Rings (as indicated in the category 
        :class:`dalgebra.dring.DRings`)::

            sage: R.derivative(y[0])
            y_1
            sage: R.derivative(x)
            1
            sage: R.derivative(x*y[10])
            x*y_11 + y_10
            sage: R.derivative(x^2*y[1]^2 - y[2]*y[1])
            -y_3*y_1 - y_2^2 + 2*x^2*y_2*y_1 + 2*x*y_1^2
            sage: (x*y[10]).derivative()
            x*y_11 + y_10

        This derivation also works naturally with several infinite variables::

            sage: S.derivative(a[1] + b[0]*a[0])
            a_1*b_0 + a_0*b_1 + a_2
            sage: (a[3]*a[1]*b[0] - b[2]).derivative()
            a_4*a_1*b_0 + a_3*a_2*b_0 + a_3*a_1*b_1 - b_3

        At the same time, these rings also work with difference operators. This can be easily built
        using the method :func:`DifferencePolynomialRing` using a shift operator as the main 
        operator to extend the ring::

            sage: R.<y> = DifferencePolynomialRing(QQ['x']); x = R.base().gens()[0]; R
            Ring of operator polynomials in (y) over Difference Ring [[Univariate Polynomial Ring in x over Rational Field], (Id,)]
            sage: S.<a,b> = DifferencePolynomialRing(ZZ); S
            Ring of operator polynomials in (a, b) over Difference Ring [[Integer Ring], (Id,)]

        And after this code we can start creating polynomials using the generators ``y``, ``a`` and ``b`` and, then 
        compute their ``shift`` or ``difference`` as we did with the derivation::

            sage: y[1]
            y_1
            sage: y[1].difference()
            y_2
            sage: R.difference(x)
            x
            sage: R.difference(x*y[10])
            x*y_11
            sage: R.difference(x^2*y[1]^2 - y[2]*y[1])
            -y_3*y_2 + x^2*y_2^2

        This difference also works naturally with several infinite variables::

            sage: (a[1]*b[0]).difference() 
            a_2*b_1
            sage: S.difference(a[1] + b[0]*a[0])
            a_1*b_1 + a_2

        We can see other type of shifts or differences operators::

            sage: X = QQ[x]('x'); shift = QQ[x].Hom(QQ[x])(X+1)
            sage: T.<z> = DifferencePolynomialRing(DifferenceRing(QQ[x], shift)); x = T.base().gens()[0]
            sage: T.difference(z[0])
            z_1
            sage: T.difference(x)
            x + 1
            sage: T.difference(x^2*z[1]^2 - z[2]*z[1])
            -z_3*z_2 + (x^2 + 2*x + 1)*z_2^2

        One of the main features of the category :class:`dalgebra.dring.DRings` is that
        several operators can be included in the ring. This class of operator rings also have such feature, 
        extending all operators at once. 

        In this case, the variables are display with a tuple as a sub-index, indicating how many times each
        operators has been applied to each of the infinite variables of the ring::

            sage: R.<x,y> = QQ[] # base ring
            sage: dx, dy = R.derivation_module().gens() # creating derivations
            sage: s = R.Hom(R)([x+1,y-1]) # creating the shift operator
            sage: dsR = DifferenceRing(DifferentialRing(R, dx, dy), s); dsR
            Ring [[Multivariate Polynomial Ring in x, y over Rational Field], (d/dx, d/dy, Hom({x: x + 1, y: y - 1}))]

        We can see that these three operators all commute::

            sage: dsR.all_operators_commute()
            True

        Hence, we can create the ring of operator polynomials with as many variables as we want::

            sage: OR.<u,v> = DPolynomialRing(dsR); OR
            Ring of operator polynomials in (u, v) over Ring [[Multivariate Polynomial Ring in 
            x, y over Rational Field], (d/dx, d/dy, Hom({x: x + 1, y: y - 1}))]
            
        When we have several operators, we can create elements on the variables in two ways:

        * Using an index (as usual): then the corresponding variable will be created but following the order
          that is given by :class:`dalgebra.dpolynomial.dpolynomial_element.IndexBijection`.
        * Using a tuple: have the standard meaning that each of the operators has been applied that amount of times.

        We can see these two approaches in place::

            sage: u[5]
            u_0_1_1
            sage: v[0,3,2]
            v_0_3_2
            sage: u[5].derivative(0)
            u_1_1_1
            sage: u[5].derivative(1, times=3)
            u_0_4_1
            sage: u[5].derivative(1, times=3).derivative(0, times=2).difference(times=1)
            u_2_4_2
            sage: (u[5]*v[0,1,0]).derivative(1)
            u_0_2_1*v_0_1_0 + u_0_1_1*v_0_2_0
            sage: (u[5]*v[0,1,0]).derivative(1) - u[0,1,0].shift()*v[0,2,0]
            u_0_2_1*v_0_1_0
    '''
    Element = DPolynomial

    def _base_category(self) -> Category: return _DRings

    def _set_categories(self, base : Parent) -> list[Category]: return [_DRings, CommutativeAlgebras(base)]

    def __init__(self, base : Parent, names : Collection[str]):
        if not base in _DRings:
            raise TypeError("The base must be a ring with operators")
        if not base.all_operators_commute():
            raise TypeError("Detected operators that do NOT commute. Impossible to build the DPolynomialRing")

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
        morph = DPolynomialSimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DPolynomialSimpleMorphism(self, current)
            current.register_conversion(morph)
        
        try: # Trying to add conversion for the ring of linear operators
            operator_ring = self.linear_operator_ring()
            morph = DPolynomialToLinOperator(self)
            operator_ring.register_conversion(morph)
        except NotImplementedError:
            pass

        self.__operators : tuple[AdditiveMap] = tuple([
            self._create_operator(operation, ttype) 
            for operation, ttype in enumerate(self.base().operator_types())
        ])
        self.__cache : list[dict[DPolynomial, DPolynomial]] = [dict() for _ in range(len(self.__operators))]

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S: Parent) -> bool:
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, x) -> DPolynomial:
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into the corresponding type for ``self``.
        '''
        try:
            p = super()._element_constructor_(x)
            return self.element_class(self, p)
        except (ValueError, NameError) as error: # if it is not a normal element, we try as linear operators
            try: # trying to get the ring of linear operators
                operator_ring = self.linear_operator_ring()
                if x in operator_ring:
                    x = operator_ring(x).polynomial()
                    y = self.gens()[0]
                    if self.noperators() == 1: # x is a univariate polynomial
                        return sum(self.base()(x.monomial_coefficient(m))*y[m.degree()] for m in x.monomials())
                    else:
                        return sum(self.base()(c)*y[tuple(m.degrees())] for (c,m) in zip(x.coefficients(), x.monomials()))
            except NotImplementedError:
                raise NotImplementedError(f"Ring of linear operator rings not implemented. Moreover: {error}")

    def _pushout_(self, other):
        scons, sbase = self.construction()
        if isinstance(other, DPolynomialRing_dense):
            ocons, obase = other.construction()
            cons = scons.merge(ocons)
            try:
                base = pushout(sbase, obase)
            except TypeError:
                base = pushout(obase, sbase)
            return cons(base)
        return None
    
    @cached_method
    def gen(self, i: int | str = None) -> DPolynomialGen:
        r'''
            Override method to create the `i^{th}` generator (see method 
            :func:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse.gen`).

            For a :class:`DPolynomialRing_dense`, the generator type is 
            :class:`~dalgebra.diff_polynomial.diff_polynomial_element.DPolynomialGen`
            which provides extra features to know if an object can be generated by that generator.
            See tis documentation for further details.

            INPUT:

            * ``i``: index or name of the required generator.

            OUTPUT:

            A :class:`~dalgebra.diff_polynomial.diff_polynomial_element.DPolynomialGen`
            representing the `i^{th}` generator of ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: from dalgebra.dpolynomial.dpolynomial_element import DPolynomialGen
                sage: R.<y> = DPolynomialRing(DifferentialRing(QQ['x'], diff))
                sage: R.gen(0)
                y_*
                sage: R.gen(0) is y
                True
                sage: isinstance(R.gen(0), DPolynomialGen)
                True
                sage: S = DPolynomialRing(DifferentialRing(ZZ, lambda z : 0), ('a', 'b'))
                sage: S
                Ring of operator polynomials in (a, b) over Differential Ring [[Integer Ring], (0,)]
                sage: S.gen(0)
                a_*
                sage: S.gen(1)
                b_*

            This method also allow the name of the generator as input::

                sage: S.gen('a')
                a_*
                sage: S.gen('b')
                b_*
                sage: S.gen('t')
                Traceback (most recent call last):
                ...
                ValueError: tuple.index(x): x not in tuple
        '''
        if isinstance(i, str):
            i = self._names.index(i)
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return DPolynomialGen(self, self._names[i])
                
    def construction(self) -> DPolyRingFunctor:
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DPolynomialRing_dense`, the associated functor class is :class:`DPolyRingFunctor`.
            See its documentation for further information.
        '''
        return DPolyRingFunctor(self._names), self.base()
    
    def flatten(self, polynomial : DPolynomial) -> Element:
        r'''
            Method to compute the flatten version of a polynomial.

            This method allows to compute a basic object where all variables appearing in the given ``polynomial``
            and all its base parents are at the same level. This is similar to the method :func:`flattening_morphism`
            from multivariate polynomials, but adapted to the case of infinite variable polynomials.

            Moreover, we need to take care of possible wrapping problems in the DRing category. 

            INPUT:

            * ``polynomial``: an element in ``self`` to be flatten.

            OUTPUT:

            A multivariate polynomial with all the variables appearing in ``polynomial`` and all bases rings of ``self``
            at the same level.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: R.flatten(f1)
                u_2*x^2 + u_0*x + v_0*x - v_0
                sage: R.flatten(f1).parent()
                Multivariate Polynomial Ring in u_2, u_1, u_0, v_2, v_1, v_0, x over Rational Field

            This method works with more complicated ring with operators. It is interesting to remark that the subindex of the 
            infinite variables (when having several operators) collapse to one number following the rules as in 
            :class:`IndexBijection`::

                sage: B.<x,ex,l,m,e> = QQ[]
                sage: dx,dex,dl,dm,de = B.derivation_module().gens()
                sage: shift = B.Hom(B)([x+1, e*ex, l, m, e])
                sage: DSB = DifferenceRing(DifferentialRing(B, dx + ex*dex), shift); x,ex,l,m,e = DSB.gens()
                sage: R.<u,v> = DPolynomialRing(DSB)
                sage: f1 = u[1,0]*ex + (l-1)*v[0,1]*x - m; f1
                ex*u_1_0 + (x*l - x)*v_0_1 - m
                sage: f1.polynomial()
                ex*u_2 + (x*l - x)*v_1 - m
                sage: f1.derivative()
                ex*u_2_0 + ex*u_1_0 + (x*l - x)*v_1_1 + (l - 1)*v_0_1
                sage: f1.derivative().polynomial()
                ex*u_5 + ex*u_2 + (x*l - x)*v_4 + (l - 1)*v_1
                sage: R.flatten(f1.derivative())
                v_4*x*l - v_4*x + u_5*ex + u_2*ex + v_1*l - v_1
                sage: R.flatten(f1.derivative()).parent()
                Multivariate Polynomial Ring in u_5, u_4, u_3, u_2, u_1, u_0, v_5, v_4, v_3, v_2, v_1, v_0, x, ex, l, m, e over Rational Field

            We remark that we can reconstruct the original polynomial from the flattened version::

                sage: R(R.flatten(f1.derivative())) == f1.derivative()
                True
                sage: R(R.flatten(f1)) == f1
                True
        '''
        # we check that the input is in ``self``
        polynomial = self(polynomial)

        # we compute the destination ring for the polynomial
        variables = [*polynomial.polynomial().parent().gens()]
        current = self.base()
        while (
            isinstance(current, DRing_Wrapper) or 
            is_PolynomialRing(current) or 
            is_MPolynomialRing(current) or 
            isinstance(current, InfinitePolynomialRing_dense) or 
            isinstance(current, InfinitePolynomialRing_sparse)
        ):
            if is_PolynomialRing(current) or is_MPolynomialRing(current):
                variables.extend(current.gens())
            elif isinstance(current, InfinitePolynomialRing_dense) or isinstance(current, InfinitePolynomialRing_sparse):
                variables.extend(reduce(lambda p, q : pushout(p,q), [c.polynomial().parent() for c in polynomial.polynomial().coefficients()]).gens())
            
            if isinstance(current, DRing_Wrapper):
                current = current.wrapped
            else:
                current = current.base()

        # at this state we have a "current" that can not be extracted further and a list of variables
        destiny_ring = PolynomialRing(current, variables)
        return destiny_ring(str(polynomial.polynomial()))

    def change_ring(self, R):
        r'''
            Return the operator polynomial ring changing the base ring to `R`.

            We will keep the name of the variables of ``self`` but now will take coefficients
            over `R` and the operations will be those on `R`.

            INPUT:

            * ``R``: a Ring with Operators.

            OUTPUT:

            A :class:`DPolynomialRing_dense` over ``R`` with the same variables as ``self``.
        '''
        return DPolynomialRing(R, self.variable_names())

    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds) -> DPolynomial:
        res = super().__call__(*args, **kwds)
        if not isinstance(res, self.element_class):
            res = self.element_class(self, res)
        return res

    ## Other magic methods   
    def __repr__(self):
        return f"Ring of operator polynomials in ({', '.join(self._names)}) over {self._base}"

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self) -> DPolynomial:
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DPolynomialRing(DifferentialRing(QQ['x'], diff))
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self) -> DPolynomial:
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DPolynomialRing(DifferentialRing(QQ['x'], diff))
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
     
    def eval(self, element, *args, dic: dict[DPolynomialGen,DPolynomial] = None, **kwds):
        r'''
            Method to evaluate elements in the ring of differential polynomials.

            Since the infinite polynomials have an intrinsic meaning (namely, the 
            variables are related by the operator), evaluating a polynomial
            is a straight-forward computation once the objects for the ``*_0`` term is given.

            This method evaluates elements in ``self`` following that rule.

            REMARK: **this method can be used to compose operator polynomials**. In the case 
            where we have an operator polynomial `p(u) \in R\{u\}` (for `R` a ring with operators) 
            we can interpret the polynomial `p(u)` as an operator over any extension of `R` that acts
            by substituting `u` by the element the operator acts on.

            In the case of linear operators, we can define a non-commutative product over these operators
            and this method eval can be used to compute such multiplication (see examples below).

            INPUT:

            * ``element``: element (that must be in ``self``) to be evaluated
            * ``args``: list of arguments that will be linearly related with the generators
              of ``self`` (like they are given by ``self.gens()``)
            * ``dic``: dictionary mapping generators to polynomials. This alllows an input equivalent to 
              the argument in ``kwds`` but where the keys of the dictionary are :class:`DPOlynomialGen`.
            * ``kwds``: dictionary for providing values to the generators of ``self``. The 
              name of the keys must be the names of the generators (as they can be got using 
              the attribute ``_name``).

            We allow a mixed used of ``args`` and ``kwds`` but an error will be raised if

            * There are too many arguments in ``args``,
            * An input in ``kwds`` is not a valid name of a generator,
            * There are duplicate entries for a generator.

            OUTPUT:

            The resulting element after evaluating the variable `\alpha_{(i_1,...,i_n)} = (d_1^{i_1} \circ ... \circ d_n^{i_n})(\alpha)`,
            where `\alpha` is the name of the generator.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: R.eval(y[1], 0)
                0
                sage: R.eval(y[0] + y[1], x)
                x + 1
                sage: R.eval(y[0] + y[1], y=x)
                x + 1

            This method always commutes with the use of :func:`operation`::

                sage: R.eval(R.derivative(x^2*y[1]^2 - y[2]*y[1]), y=x) == R.derivative(R.eval(x^2*y[1]^2 - y[2]*y[1], y=x))
                True

            This evaluation also works naturally with several infinite variables::

                sage: S = DifferentialPolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.eval(a[1] + y[0]*a[0], a=x, y=x^2)
                x^3 + 1
                sage: in_eval = S.eval(a[1] + y[0]*a[0], y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of operator polynomials in (a) over Differential Ring [[Univariate Polynomial Ring in x over Rational Field], (d/dx,)]

            As explained earlier, we can use this method to compute the product as operator of two linear operators::

                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: p1 = y[2] - (x^2 - 1)*y[1] + y[0]; op1 = p1.as_linear_operator()
                sage: p2 = x*y[1] - 3*y[0]; op2 = p2.as_linear_operator()
                sage: p1(y=p2) == R(op1*op2)
                True

            As expected, similar behavior occurs when having several operators in the ring::

                sage: T.<u> = DPolynomialRing(DifferenceRing(DifferentialRing(QQ[x],diff), QQ[x].Hom(QQ[x])(QQ[x](x)+1))); x = T.base()(x)
                sage: p3 = 2*u[0,0] + (x^3 - 3*x)*u[1,0] + x*u[1,1] - u[2,2]; op3 = p3.as_linear_operator()
                sage: p4 = u[0,1] - u[0,0]; op4 = p4.as_linear_operator()
                sage: p3(u=p4) == T(op3*op4)
                True
                sage: p3(u=p4) - p4(u=p3) == T(op3*op4 - op4*op3) # computing the commutator of the two operators
                True

            This can also work when having several infinite variables (in contrast with the method :func:`as_linear_operator`)::

                sage: U.<a,b> = DifferentialPolynomialRing(QQ[x]); x = U.base()(x)
                sage: p5 = a[0] + b[1]*(b[0]^2 - x^2)*a[1]; p5.is_linear(a)
                True
                sage: p6 = x*a[1] - b[0]*a[0]; p6.is_linear(a)
                True
                sage: p5(a=p6) - p6(a=p5) # commutator of p5 and p6 viewed as operators w.r.t. a
                -a_0*b_1^2*b_0^2 + (-x)*a_1*b_2*b_0^2 + (-2*x)*a_1*b_1^2*b_0 + a_1*b_1*b_0^2 + x^2*a_0*b_1^2 + x^3*a_1*b_2 + x^2*a_1*b_1
        '''
        ### Combining the arguments from dic and kwds
        if dic != None:
            for k,v in dic.items():
                if isinstance(k, DPolynomialGen):
                    kwds[k.variable_name()] = v
                else:
                    kwds[str(k)] = v

        ### Checking the element is in self
        if(not element in self):
            raise TypeError("Impossible to evaluate %s as an element of %s" %(element, self))
        element = self(element) # making sure the structure is the appropriate

        ### Checking the input that needs to be evaluated
        gens : tuple[DPolynomialGen] = self.gens()
        names : list[str] = [el._name for el in gens]
        if(len(args) > self.ngens()):
            raise ValueError(f"Too many argument for evaluation: given {len(args)}, expected (at most) {self.ngens()}")

        final_input : dict[DPolynomialGen, Element] = {gens[i] : args[i] for i in range(len(args))}
        for key in kwds:
            if(not key in names):
                raise TypeError(f"Invalid name for argument {key}")
            gen = gens[names.index(key)]
            if(gen in final_input):
                raise TypeError(f"Duplicated value for generator {gen}")
            final_input[gen] = kwds[key]

        ### Deciding final parent
        rem_names = [name for (name,gen) in zip(names,gens) if gen not in final_input]
        R = DPolynomialRing(self.base(), rem_names) if len(rem_names) > 0 else self.base()
        for value in final_input.values():
            R = pushout(R, parent(value))
        
        final_input = {key : R(value) for key,value in final_input.items()} # updating input to the output ring

        ### Building the elements to be used in evaluation
        evaluation_dict = {}
        for variable in element.variables():
            for gen in gens:
                if variable in gen: # we found the generator of this variable
                    operations = gen.index(variable)
                    if gen in final_input:
                        if self.noperators() == 1:
                            value = final_input[gen].operation(times=operations)
                        else:
                            value = final_input[gen]
                            for (i, times) in enumerate(operations):
                                value = value.operation(operation=i, times=times)
                        evaluation_dict[str(variable)] = R(value)
                    else:
                        evaluation_dict[str(variable)] = R(gen[operations])
                    break
        # extending the dictionary to all variables in element.polynomial().
        for variable in element.polynomial().parent().gens():
            if not variable in element.variables(): # only those that do not appear
                evaluation_dict[str(variable)] = R.zero() # we can add anything here, since they do not show up

        return R(element.polynomial()(**evaluation_dict))
        
    #################################################
    ### Method from DRing category
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
            def __extended_homomorphism(element : DPolynomial) -> DPolynomial:
                if(element in self):
                    element = self(element)
                else:
                    element=self(str(element))
                    
                if(element in self.base()):
                    return self(operator(self.base()(element)))
                
                if(not element in self.__cache[operation]):
                    generators = self.gens()
                    if(element.is_monomial()):
                        c = element.coefficients()[0]
                        v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                        v = [self(str(el)) for el in v]

                        result = operator(c)
                        for i in range(len(v)):
                            for g in generators:
                                if g.contains(v[i]):
                                    result *= g.next(v[i], operation)**d[i]
                                    break
                        
                        self.__cache[operation][element] = result
                    else:
                        c = element.coefficients(); m = element.monomials()
                        self.__cache[operation][element] = sum(operator(c[i])*__extended_homomorphism(m[i]) for i in range(len(m)))
                        
                return self.__cache[operation][element]
            func = __extended_homomorphism
        elif ttype == "derivation":
            def __extended_derivation(element : DPolynomial) -> DPolynomial:
                if(element in self):
                    element = self(element)
                else:
                    element=self(str(element))
                    
                if(element in self.base()):
                    return self(operator(self.base()(element)))
                
                if(not element in self.__cache[operation]):
                    generators = self.gens()
                    if(element.is_monomial()):
                        c = element.coefficients()[0]
                        m = element.monomials()[0]
                        v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                        v = [self(str(el)) for el in v]
                        base = c*prod([v[i]**(d[i]-1) for i in range(len(v))], self.one())

                        first_term = operator(c)*m
                        second_term = self.zero()
                        for i in range(len(v)):
                            to_add = d[i]*prod([v[j] for j in range(len(v)) if j != i], self.one())
                            for g in generators:
                                if(g.contains(v[i])):
                                    to_add *= g.next(v[i], operation) # we create the next generator for this operation
                                    break
                            second_term += to_add
                        self.__cache[operation][element] = first_term + base*second_term
                    else:
                        self.__cache[operation][element] = sum(
                            operator(c)*m + c*__extended_derivation(m) 
                            for (c,m) in zip(
                                element.coefficients(), 
                                element.monomials()
                            )
                        )
                        
                return self.__cache[operation][element]
            func = __extended_derivation
        elif ttype == "skew":
            raise NotImplementedError("The 'skew' case is not yet implemented")
            # func = None
        else:
            raise ValueError(f"The type {ttype} is not recognized as a valid operator.")

        return AdditiveMap(self, func) 
    
    def linear_operator_ring(self) -> Ring:
        r'''
            Overridden method from :func:`~DRings.ParentMethods.linear_operator_ring`.

            This method builds the ring of linear operators on the base ring. It only works when the 
            ring of operator polynomials only have one variable.
        '''
        if self.ngens() > 1:
            raise NotImplementedError(f"Impossible to generate ring of linear operators with {self.ngens()} variables")
        
        return self.base().linear_operator_ring()

    def inverse_operation(self, element: DPolynomial, operation: int = 0) -> DPolynomial:
        if not element in self:
            raise TypeError(f"[inverse_operation] Impossible to apply operation to {element}")
        element = self(element)

        if self.operator_types()[operation] == "homomorphism":
            return self.__inverse_homomorphism(element, operation)
        elif self.operator_types()[operation] == "derivation":
            return self.__inverse_derivation(element, operation)
        elif self.operator_types()[operation] == "skew":
            return self.__inverse_skew(element, operation)
        else:
            raise NotImplementedError("[inverse_operation] Inverse for unknown operation not implemented")
    
    def __inverse_homomorphism(self, element: DPolynomial, operation: int):
        solution = self.zero()
        for coeff, monomial in zip(element.coefficients(), element.monomials()):
            coeff = coeff.inverse_operation(operation) if not coeff.is_constant() else coeff
            variables = monomial.variables()
            new_mon = self.one()
            for v in variables:
                for g in element.infinite_variables():
                    if v in g:
                        ind = list(g.index(v, True))
                        if ind[operation] == 0:
                            raise ValueError(f"[inverse_homomorphism] Found an element impossible to invert: {monomial}")
                        ind[operation] -= 1
                        new_mon *= g[tuple(ind) if len(ind) > 1 else ind[0]]
            solution += coeff*new_mon
        return solution
    
    def __inverse_derivation(self, element: DPolynomial, operation: int):
        logger.debug(f"[inverse_derivation] Called with {element}")
        if element == 0:
            logger.debug(f"[inverse_derivation] Found a zero --> Easy")
            solution = self.zero()
        elif element.degree() == 1:
            logger.debug(f"[inverse_derivation] Found linear element --> Easy to do")
            solution = self.zero()
            for coeff, monomial in zip(element.coefficients(), element.monomials()):
                if monomial == 1:
                    raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {monomial}")
                coeff = coeff.inverse_operation(operation) if not coeff.is_constant() else coeff
                var = monomial.variables()[0] # we know there is only 1
                for g in element.infinite_variables():
                    if var in g:
                        ind = list(g.index(var, True))
                        if ind[operation] == 0:
                            raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {monomial}")
                        ind[operation] -= 1
                        new_mon = g[tuple(ind) if len(ind) > 1 else ind[0]]
                        break
                solution += coeff*new_mon
        else:
            logger.debug(f"[inverse_derivation] Element is not linear")
            monomials = element.monomials()
            if 1 in monomials:
                raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {element}")
            monomials_with_points = []
            for mon in monomials:
                bv = max(self.gens().index(v) for v in mon.infinite_variables())
                bo = mon.order(self.gens()[bv], operation)
                monomials_with_points.append((bv, bo))

            aux = max(el[1] for el in monomials_with_points)
            V, O = max(monomials_with_points, key = lambda p: p[0]*aux + p[1])
            V = self.gens()[V]
            logger.debug(f"[inverse_derivation] Maximal variable: {V[O]}")
            
            if element.degree(V[O]) > 1:
                raise ValueError(f"[inverse_derivation] Found an element impossible to invert: {element}")
            else:
                highest_part = element.coefficient(V[O]); deg_order_1 = highest_part.degree(V[O-1])
                cs = [highest_part.coefficient(V[O-1]**i) for i in range(deg_order_1+1)]
                order_1_part = sum(cs[i]*V[O-1]**i for i in range(deg_order_1+1))
                q1 = highest_part - order_1_part # order q1 < d-1
                
                ## we compute remaining polynomial
                partial_integral = sum(cs[i]*(1/ZZ(i+1)) * V[O-1]**(i+1) for i in range(deg_order_1+1)) + V[O-1]*q1

            logger.debug(f"[inverse_derivation] Partial integral: {partial_integral}")
            rem = element - partial_integral.operation(operation)
            logger.debug(f"[inverse_derivation] Remaining to integrate: {rem}")
            solution = partial_integral + self.inverse_operation(rem, operation)
            
        logger.debug(f"[inverse_derivation] Result: {solution}")
        return solution
   
    def __inverse_skew(self, element: DPolynomial, operation: int):
        raise NotImplementedError("[inverse_skew] Skew-derivation operation not yet implemented")
            
    #################################################
    ### Sylvester methods
    #################################################
    def sylvester_resultant(self, P: DPolynomial, Q: DPolynomial, gen: DPolynomialGen = None) -> DPolynomial:
        r'''
            Method to compute the Sylvester resultant of two operator polynomials.

            **REMARK**: this method only works when ``self`` have with 1 operator and both `P` and `Q` are linear on the given generator.

            If we have two linear operator polynomials `P(u), Q(u) \in R\{u\}` where `(R, \sigma)` is a ring with 1 operator `\sigma`, 
            then we can consider the extended system 

            .. MATH::

                \{P, \sigma(P), \ldots, \sigma^{m-1}(P), Q, \sigma(Q), \ldots, \sigma^{n-1}(Q)\},

            where `n` is the order of `P` and `m` is the order of `Q`. Then, it is clear that the only appearances of the infinite variable 
            `u_*` is within `[u_0,\ldots,u_{n+m-1}]`. Hence we can build a Sylvester-type matrix using these polynomials and compute its
            determinant obtaining an expression in `R`. 

            This determinant is called the Sylvester resultant of `P` and `Q` and it is equivalent to the Sylvester resultant on the algebraic case.

            This method computes the Sylvester resultant of two linear operator polynomials given the appropriate variable. If only one infinite variable 
            is present, the it is not necessary to provide this value.

            INPUT:

            * ``P``: an operator polynomial (has to be linear) to be used as `P`.
            * ``Q``: an operator polynomial (has to be linear) to be used as `Q`.
            * ``gen``: an infinite variable that will be eliminated from `P` and `Q`. Can be ``None`` only if one infinite variable is in ``self``.

            OUTPUT:

            A :class:`~.dpolynomial_element.DPolynomial` with the Sylvester resultant of `P` and `Q`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_resultant(Q)
                x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19

            If several variables are available, we need to explicitly provide the variable we are considering::

                sage: R.<u,v> = DPolynomialRing(B)
                sage: P = (3*x -1)*u[0]*v[0] + x^2*v[1]*u[0] + u[2]
                sage: Q = 7*x*v[0] + x^2*v[0]*u[1]
                sage: P.sylvester_resultant(Q)
                Traceback (most recent call last):
                ...
                ValueError: [sylvester_checking] No infinite variable provided but several available.
                sage: P.sylvester_resultant(Q, u)
                x^6*v_1*v_0^2 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, v)
                x^2*u_1 + 7*x

            The infinite variable can also be given as an index::

                sage: P.sylvester_resultant(Q, 0)
                x^6*v_1*v_0^2 + (3*x^5 - x^4)*v_0^3
                sage: P.sylvester_resultant(Q, 1)
                x^2*u_1 + 7*x
                sage: P.sylvester_resultant(Q, 2)
                Traceback (most recent call last):
                ...
                IndexError: [sylvester_checking] Requested generator 2 but only 2 exist.
                sage: P.sylvester_resultant(Q, -1)
                Traceback (most recent call last):
                ...
                IndexError: [sylvester_checking] Requested generator -1 but only 2 exist.
        '''
        return self.sylvester_matrix(P,Q,gen).determinant()

    @cached_method
    def sylvester_subresultant(self, P: DPolynomial, Q: DPolynomial, gen: DPolynomialGen = None, k: int = 0, i: int = 0):
        r'''
            Method to compute the `(k,i)`-th Sylvester subresultant of two operator polynomials.

            From :func:`sylvester_matrix`, we obtain the matrix `S_k(P,Q)` which has `k` more columns than rows. In 
            order to obtain a square matrix, we can remove `k` columns. In particular, removing the `k` out of the `k+1`
            first columns (which are related to the coefficients of `(1,\ldots,\partial^k)`). 

            The corresponding `(k,i)`-th subresultant of `P` and `Q` is the determinant of this matrix.

            In particular, when `k=0` and `i=0`, then the subresultant is exactly the Sylvester resultant of `P` and `Q`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant(P, Q, k=1, i=0)
                -3*x^3 - 3*x^2 + 3*x + 2
                sage: S.sylvester_subresultant(P, Q, k=1, i=1)
                8*x^2 + 7*x

            We can see that the case with `k=0` and `i=0`coincides with the method :func:`sylvester_resultant`::
            
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant(P, Q, k=0, i=0) == P.sylvester_resultant(Q)
                True
        '''
        ## Checking the argument `i`
        if not i in ZZ:
            raise TypeError(f"[sylvester_subresultant] The argument {i = } must be an integer")
        elif i < 0 or i > k:
            raise ValueError(f"[sylvester_subresultant] The index {i = } is out of proper bounds [0,...,{k}]")

        S_k = self.sylvester_matrix(P,Q,gen,k)
        S_ki = S_k.matrix_from_columns([i]+list(range(k+1,S_k.ncols())))
        return S_ki.determinant()
        
    @cached_method
    def sylvester_matrix(self, P: DPolynomial, Q: DPolynomial, gen: DPolynomialGen = None, k: int = 0) -> Matrix:
        r'''
            Method to obtain the `k`-Sylvester matrix for two operator polynomials.

            **REMARK**: this method only works when ``self`` have with 1 operator and both `P` and `Q` are linear on the given generator.

            If we have two linear operator polynomials `P(u), Q(u) \in R\{u\}` where `(R, \sigma)` is a ring with 1 operator `\sigma`, 
            then we can consider the extended system 

            .. MATH::

                \Xi_k(P,Q) = \{P, \sigma(P), \ldots, \sigma^{m-1-k}(P), Q, \sigma(Q), \ldots, \sigma^{n-1-k}(Q)\},

            where `n` is the order of `P` and `m` is the order of `Q` and `k \in\{0,\ldots,N\}` for `N \min(n,m)-1`. We can 
            build a Sylvester-type matrix using these polynomials.

            INPUT:

            * ``P``: an operator polynomial (has to be linear) to be used as `P`.
            * ``Q``: an operator polynomial (has to be linear) to be used as `Q`.
            * ``gen``: an infinite variable that will be eliminated from `P` and `Q`. Can be ``None`` only if one infinite variable is in ``self``.
            * ``k``: an integer in `\{0,\ldots,N\}` to get the corresponding `k`-Sylvester matrix. When `k = 0`, the matrix is square.

            OUTPUT:

            A Sylvester-type matrix for the corresponding operators.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_matrix(Q)
                [      x^2 - 1          -3*x             1             0             0]
                [            0     x^2 + 2*x      -3*x - 3             1             0]
                [            0             0 x^2 + 4*x + 3      -3*x - 6             1]
                [           -1             0             0             1             0]
                [            0            -1             0             0             1]
                sage: P.sylvester_matrix(Q, k=1)
                [      x^2 - 1          -3*x             1             0]
                [            0     x^2 + 2*x      -3*x - 3             1]
                [           -1             0             0             1]

            It is important to remark that this matrix depends directly on the operation defined on the ring::

                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: P.sylvester_matrix(Q)
                [x^2 - 1    -3*x       1       0       0]
                [    2*x x^2 - 4    -3*x       1       0]
                [      2     4*x x^2 - 7    -3*x       1]
                [     -1       0       0       1       0]
                [      0      -1       0       0       1]
                sage: P.sylvester_matrix(Q,k=1)
                [x^2 - 1    -3*x       1       0]
                [    2*x x^2 - 4    -3*x       1]
                [     -1       0       0       1]

            However, the Sylvester matrix is not well defined when the ring has several operations::

                sage: B = DifferentialRing(DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)), diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[0,2] - 3*x*z[0,1] + (x^2 - 1)*z[1,0]
                sage: Q = z[2,3] - z[1,0]
                sage: P.sylvester_matrix(Q)
                Traceback (most recent call last):
                ...
                NotImplementedError: [sylvester_checking] Sylvester resultant with 2 is not implemented
        '''
        ## Checking the polynomials and ring arguments
        P,Q,gen = self.__process_sylvester_arguments(P,Q,gen)
        
        ## Checking the k argument
        n = P.order(gen); m = Q.order(gen); N = min(n,m) - 1
        # Special case when one of the orders is -1 (i.e., the variable `gen` is not present)
        if n == -1:
            return matrix([[P]]) # P does not contain the variable `gen` to eliminate
        elif m == -1:
            return matrix([[Q]]) # Q does not contain the variable `u` to eliminate
        
        if not k in ZZ:
            raise TypeError(f"[sylvester_matrix] The index {k = } is not an integer.")
        elif N == -1 and k != 0:
            raise TypeError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0].")
        elif N >= 0 and (k < 0 or k > N):
            raise ValueError(f"[sylvester_matrix] The index {k = } is out of proper bounds [0,...,{N}]")
        
        # Building the extension
        extended_P: list[DPolynomial] = [P.operation(times=i) for i in range(m-k)]
        extended_Q: list[DPolynomial] = [Q.operation(times=i) for i in range(n-k)]

        # Building the Sylvester matrix (n+m-1-k) , (n+m-1-k)
        fR = self.polynomial_ring() # guaranteed common parent for all polynomials
        cols = [fR(gen[pos].polynomial()) for pos in range(n+m-k)]
        equations = [fR(equation.polynomial()) for equation in extended_P + extended_Q]

        # Returning the matrix
        return matrix([[self(equation.coefficient(m)) for m in cols] for equation in equations])

    def sylvester_subresultant_sequence(self, P: DPolynomial, Q: DPolynomial, gen: DPolynomialGen = None) -> tuple[DPolynomial]:
        r'''
            Method that gets the subresultant sequence in form of a linear d-polynmomial.

            As described in :func:`sylvester_subresultant`, when we build the `k`-Sylvester matrix of two linear 
            d-polynomials, we obtain a non-square matrix and, in order to compute a determinant, we need to remove `k`
            columns. The subresultants are built by removing `k` out of the first `k+1` columns.

            Hence, we have remaining one columns corresponding to one operator `\sigma^i`. We can then consider the 
            following linear operator:

            .. MATH::

                \mathcal{S}_k(P,Q) = \sum_{i=0}^k S_{k,i}(P,Q)\sigma^i

            When iterating w.r.t. `k`, we obtain a sequence of linear operators. This is called the subresultant 
            sequence of the d-polynomials `P` and `Q`.

            This sequence is important because it describes the common factor (as operator) of the two d-polynomials. More
            precisely, if the first element is zero (i.e., the Sylvester resultant is zero), then `P` and `Q` 
            has a common right factor as linear operators. 

            Moreover, the first non-zero element in the sequence provides a formula for the greatest right common factor.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B = DifferenceRing(QQ[x], QQ[x].Hom(QQ[x])(x+1)); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant_sequence(P, Q)
                ((x^6 + 6*x^5 + 10*x^4 - 18*x^3 - 65*x^2 - 42*x - 2)*z_0, (8*x^2 + 7*x)*z_1 + (-3*x^3 - 3*x^2 + 3*x + 2)*z_0)
                sage: B = DifferentialRing(QQ[x], diff); x = B(x)
                sage: S.<z> = DPolynomialRing(B)
                sage: P = z[2] - 3*x*z[1] + (x^2 - 1)*z[0]
                sage: Q = z[3] - z[0]
                sage: S.sylvester_subresultant_sequence(P, Q)
                ((x^6 + 6*x^4 - 18*x^3 + 9*x^2 - 30*x - 19)*z_0, (8*x^2 + 4)*z_1 + (-3*x^3 + x - 1)*z_0)
        '''
        ## Checking the polynomials and ring arguments
        P,Q,gen = self.__process_sylvester_arguments(P,Q,gen)
        return tuple(
            sum(self.sylvester_subresultant(P,Q,gen,k,i) * gen[i] for i in range(k+1))
            for k in range(min(P.order(gen),Q.order(gen)))
        )

    def __process_sylvester_arguments(self, P: DPolynomial, Q: DPolynomial, gen: DPolynomialGen):
        r'''Check the ring, the generator and the polynomials are correct'''
        ## Checking the ring is appropriate
        if self.noperators() > 1:
            raise NotImplementedError(f"[sylvester_checking] Sylvester resultant with {self.noperators()} is not implemented")

        ## Checking the gen is correctly given
        if self.ngens() > 1 and gen is None:
            raise ValueError("[sylvester_checking] No infinite variable provided but several available.")
        elif self.ngens() > 1 and gen in ZZ:
            if gen < 0 or gen >= self.ngens():
                raise IndexError(f"[sylvester_checking] Requested generator {gen} but only {self.ngens()} exist.")
            gen = self.gens()[gen]
        elif isinstance(gen, DPolynomialGen) and not gen in self.gens():
            raise ValueError(f"[sylvester_checking] The variable {repr(gen)} do not belong to {self}")
        elif self.ngens() == 1 and gen is None:
            gen = self.gens()[0]

        ## Checking the operator polynomials are correct
        P = self(P); Q = self(Q)
        if not P.is_linear(gen):
            raise TypeError(f"[sylvester_checking] The polynomial {P} is not linear w.r.t. {gen}")
        if not Q.is_linear(gen):
            raise TypeError(f"[sylvester_checking] The polynomial {Q} is not linear w.r.t. {gen}")

        return P,Q,gen

    #################################################
    ### Weighting methods
    #################################################
    def weight_func(self, weight_vars, weight_oper):
        r'''
            TODO: add documentation to this method
        '''
        return WeightFunction(self, weight_vars, weight_oper)

    #################################################
    ### Other computation methods
    #################################################
    def as_linear_operator(self, element: DPolynomial) -> Element:
        r'''
            Method that tries to convert an operator polynomial into a linear operator.

            This method tries to create a linear operator coming from a :class:`DPolynomial`.
            In the case where we have an :class:`DPolynomial` `p(u) \in R\{u\}` (for `R` a ring with operators) 
            we can interpret the polynomial `p(u)` as an operator over any extension of `R` that acts
            by substituting `u` by the element the operator acts on. If `p` is linear, then it represents
            what it is called a linear operator.

            These linear operators may be represented more efficiently in other structures (see :func:`linear_operator_ring`
            for further information). This method transforms the elements of ``self`` that can be seen as linear
            operators to this ring structure.

            Conversely, a :class:`DPolynomialRing_dense` can transform elements from its ring of linear operators
            (i.e., the output of :func:`linear_operator_ring`) to linear :class:`DPolynomial`.

            This method checks that ``self`` has the appropriate structure (i.e., it has only one infinite variable)
            and also the ``element`` has the appropriate shape: it is linear without a constant term.

            REMARK: **this method is equivalent to the method :func:`~.dpolynomial_ring_element.DPolynomial.as_linear_operator`
            since it calls this method directly**

            INPUT:

            * ``element``: a :class:`DPolynomial` in ``self`` to be casted to a linear operator.
            
            OUTPUT:

            An element in ``self.linear_operator_ring()`` if this ring can be built.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<y> = DifferentialPolynomialRing(QQ[x]); x = R.base()(x)
                sage: p1 = y[2] - (x^2 - 1)*y[1] - y[0] # linear operator of order 2
                sage: p1.as_linear_operator()
                D^2 + (-x^2 + 1)*D - 1
                sage: R(p1.as_linear_operator()) == p1
                True
                
            If the operator polynomial is not linear or has a constant term, this method raises a :class:`TypeError`::

                sage: p2 = x*y[2]*y[0] - (x^3 + 3)*y[1]^2 # non-linear operator
                sage: p2.as_linear_operator()
                Traceback (most recent call last):
                ...
                TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.
                sage: p3 = y[2] - (x^2 - 1)*y[1] - y[0] + x^3 # linear operator but inhomogeneous
                sage: p3.as_linear_operator()
                Traceback (most recent call last):
                ...
                TypeError: Linear operator can only be built from an homogeneous linear operator polynomial.

            This also work when having several operators in the same ring::

                sage: S.<u> = DPolynomialRing(DifferenceRing(DifferentialRing(QQ[x], diff), QQ[x].Hom(QQ[x])(QQ[x](x)+1))); x = S.base()(x)
                sage: p4 = 2*u[0,0] + (x^3 - 3*x)*u[1,0] + x*u[1,1] - u[2,2] 
                sage: p4.as_linear_operator()
                -D^2*S^2 + x*D*S + (x^3 - 3*x)*D + 2
                sage: S(p4.as_linear_operator()) == p4
                True

            However, when having several infinite variables this method can not work even when the operator is clearly linear::

                sage: T.<a,b> = DifferentialPolynomialRing(QQ[x]); x = T.base()(x)
                sage: p5 = a[0] - b[1]
                sage: p5.as_linear_operator()
                Traceback (most recent call last):
                ...
                NotImplementedError: Impossible to generate ring of linear operators with 2 variables

        '''
        linear_operator_ring = self.linear_operator_ring() # it ensures the structure is alright for building this
        element = self(element) # making sure the element is in ``self``

        if not element.is_linear() or 1 in element.polynomial().monomials():
            raise TypeError("Linear operator can only be built from an homogeneous linear operator polynomial.")

        coeffs = element.coefficients(); monoms = element.monomials(); y = self.gens()[0]
        base_ring = linear_operator_ring.base(); gens = linear_operator_ring.gens()

        return sum(base_ring(c)*prod(g**i for (g,i) in zip(gens, y.index(m,as_tuple=True))) for (c,m) in zip(coeffs, monoms))

def is_DPolynomialRing(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, DPolynomialRing_dense)
is_RWOPolynomialRing = is_DPolynomialRing #: alias for is_DPolynomialRing (used for backward compatibility)

class DPolyRingFunctor (ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DPolynomialRing_dense`.

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
        super().__init__(_DRings,_DRings)
        self.rank = 11 # just above PolynomialRing and DRingFunctor
        
    ### Methods to implement        
    def _apply_functor(self, x):
        return DPolynomialRing(x,self.variables())
        
    def _repr_(self):
        return f"DPolynomialRing((*),{self.variables()})"
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.variables() == self.variables())

    def merge(self, other):
        if isinstance(other, DPolyRingFunctor):
            self_names = self.__variables
            other_names = other.__variables
            global_names = tuple(set(list(self_names)+list(other_names)))
            return DPolyRingFunctor(global_names)
        return None

    def variables(self):
        return self.__variables

class DPolynomialToLinOperator (Morphism):
    r'''
        Class representing a map to a ring of linear operators

        This map allows the coercion system to detect that some elements in a 
        :class:`DifferentialPolynomialRing_dense` are included in its ring of linear operators.
    '''
    def __init__(self, dpoly_ring : DPolynomialRing_dense):
        linear_operator_ring = dpoly_ring.linear_operator_ring()
        super().__init__(dpoly_ring, linear_operator_ring)

    def _call_(self, p):
        return self.codomain()(self.domain().as_linear_operator(p))

class DPolynomialSimpleMorphism (Morphism):
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

class WeightFunction(SetMorphism):
    r'''
        Class to represent a weight function for a ring of d-polynomials.

        Let `\mathcal{R} = (R,\Delta)\{a_1,\ldots,a_m\}` be a ring of d-polynomials and let `\mathcal{T}`
        be the monoid of monomials of `\mathcal{R}`. We say that a function `w: \mathcal{T} \rightarrow \mathbb{N}`
        if a weight function if it is a monoid homomorphism, i.e., `w(st) = w(s) + w(t)`.

        With this definition, it is clear that we can split `\mathcal{R}` into a `R`-direct sum where we keep in each 
        summand the monomials of a fixed weight:

        .. MATH::

            \mathcal{R} = \bigoplus_{i \in \mathbb{N}} \mathcal{R}_i,

        where `\mathcal{R}_i = R[t\ :\ t\in T\text{ with }w(t) = i]`. We call each layer `\mathcal{R}_i` the set of 
        `i`-homogeneous polynomials w.r.t. the weight function `w(\cdot)`.

        In order to define a weight function, we only need to define for each of the generators of `\mathcal{T}`. It 
        is interesting to remark that, for a ring of d-polynomials, we have an infinite amount of generators. In order to simplify 
        the implementation, we require two information:

        * A list of base weights `(w_1,\ldots,w_m)` such that `w(a_i) = w_i`.
        * A list of extending weights `(W_1,\ldots,W_n)` such that for 
        
        .. MATH::
        
            w(\sigma_j^k(a_i)) = \left\{\begin{array}{ll}
                w_i + kW_j & \text{if w_i \neq 0},\\
                0 & \text{otherwise}.
            \end{array}\right.

        INPUT:

        * ``dpoly_ring``: a :class:`DPolynomialRing` over which we will base the weight function.
        * ``base_weights``: a list, tuple or dictionary indicating the base weights. If a variable is not provided, we consider it with weight 0.
        * ``oper_weights``: a list or tuple indicating how each operation extends the weights (i.e., a list with the `W_i`).

        TODO:

        * Add reference to weight functions in differential setting.
        * Add reference to weight functions in difference setting.
    '''
    def __init__(self, dpoly_ring: DPolynomialRing_dense, base_weights: list[int] | tuple[int] | dict[str|DPolynomialGen, int], oper_weigths: list[int] |tuple[int]):
        if isinstance(base_weights, (list,tuple)): # we got a list of weights
            if not len(base_weights) == dpoly_ring.ngens():
                raise TypeError(f"[WeightFunction] A weight must be define for all generators (got {len(base_weights)}, expected {dpoly_ring.ngens()})")
            if any(el < 0 for el in base_weights):
                raise ValueError(f"[WeightFunction] Weights must be always non-negative.")
        elif isinstance(base_weights, dict):
            base_weights = [int(base_weights.get(v, base_weights.get(v.variable_name, base_weights.get(str(v), 0)))) for v in dpoly_ring.gens()]
            if any(el < 0 for el in base_weights):
                raise ValueError(f"[WeightFunction] Weights must be always non-negative.")
        else:
            raise TypeError("[WeightFunction] Weights must be given as lists or dictionaries.")
        self.__base_weights = base_weights

        if not isinstance(oper_weigths, (list,tuple)): # we got a list of weights
            raise TypeError("[WeightFunction] Extension of weights must be given as lists.")
        if not len(oper_weigths) == dpoly_ring.noperators():
            raise TypeError(f"[WeightFunction] A weight must be define for all operations (got {len(oper_weigths)}, expected {dpoly_ring.noperators()})")
        if any(el <= 0 for el in oper_weigths):
            raise ValueError(f"[WeightFunction] Weights must be always positive.")
        self.__oper_weights = oper_weigths

        super().__init__(dpoly_ring.Hom(ZZ, _Sets), self.weight)

    def parent(self) -> DPolynomialRing_dense:
        r'''
            Return the base ring of d-polynomials
        '''
        return self.domain()

    def weight(self, element: DPolynomial) -> int:
        r'''
            Method to weight an element of the parent

            This method compute the actual weight of a d-polynomial. If the element is a monomial, we return the corresponding weight
            for the monoid as defined by its base weights. Otherwise, we return the maximal weight of the monomials appearing in ``self``.

            INPUT:

            * ``element``: a :class:`DPolynomial` in the base ring of the weight function.

            OUTPUT:

            The weight of the element following the usual definitions.

            TODO: 

            * Add examples
        '''
        monomials = element.monomials()
        if len(monomials) == 0:
            return ZZ(0)
        elif len(monomials) > 1:
            return max(self(m) for m in monomials)
        else:
            m = monomials[0] # we treat the monomial by itself
            if m == 1:
                return ZZ(0)
            return sum(
                (self.__base_weights[i] + sum(j*w for (j,w) in zip(gen.index(variable, as_tuple=True), self.__oper_weights)))*m.degree(variable)
                for variable in m.variables() 
                for (i,gen) in enumerate(self.parent().gens()) if variable in gen
            )
    
    @cached_method
    def weighted_variables(self, weight: int) -> set[DPolynomial]:
        r'''
            Method that generates the variables with a given weight.

            INPUT:

            * ``weight``: the value of the weight we want to generate

            OUTPUT:

            A set of :class:`DPolynomial` with variables of the given weight.

            EXAMPLES::

                sage: from dalgebra import *
                sage: B.<c,x> = QQ[]
                sage: R.<a,b> = DPolynomialRing(DifferenceRing(DifferentialRing(B, lambda p : diff(p,x)), B.Hom(B)([c,x+1])))
                sage: w = R.weight_func([1,2],[2,1])
                sage: w.weighted_variables(0)
                set()
                sage: w.weighted_variables(1)
                {a_0_0}
                sage: w.weighted_variables(2)
                {b_0_0, a_0_1}
                sage: w.weighted_variables(3)
                {b_0_1, a_1_0, a_0_2}
                sage: w.weighted_variables(4)
                {b_1_0, b_0_2, a_1_1, a_0_3}
                sage: w.weighted_variables(5)
                {b_1_1, b_0_3, a_2_0, a_1_2, a_0_4}
                sage: w.weighted_variables(6)
                {b_2_0, b_1_2, b_0_4, a_2_1, a_1_3, a_0_5}
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
                sage: w = R.weight_func([1,3],[1,1])
                sage: [len(w.weighted_variables(i)) for i in range(20)]
                [0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36]
        '''
        if weight <= 0: return set()
        ## recursive part
        recursive = set()
        for i in range(self.parent().noperators()):
            recursive = recursive.union([v.operation(i) for v in self.weighted_variables(weight - self.__oper_weights[i])])
        
        ## adding the special case if needed
        return recursive.union(set([v[0] for (v,i) in zip(self.parent().gens(), self.__base_weights) if i == weight]))

    @cached_method
    def homogeneous_monomials(self, weight: int) -> set[DPolynomial]:
        r'''
            Method that generates the homogeneous monomials of weight ``weight``.

            This uses a recursive approach using the basic formulas on how to compute the 
            weights of monomials.

            INPUT:

            * ``weight``: the value of the weight we want to generate.

            OUTPUT:

            A set of :class:`DPolynomial` with monomials of the given weight.

            REMARK: 

            If a generator has weight zero, it won't appear in the set generated wince we could have infinitely many monomials, and we 
            are looking for finite sets.

            TODO: add examples
        '''
        if weight < 0:
            return set()
        elif weight == 0:
            return set([self.parent().one()])
        else:
            ## operation part
            result = set()
            for (operator, ttype, op_weight) in zip(self.parent().operators(), self.parent().operator_types(), self.__oper_weights):
                if ttype == "derivation":
                    logger.debug(f"Adding derivations of monomilas of weights {weight-1}")
                    to_add = sum([operator(mon).monomials() for mon in self.homogeneous_monomials(weight - op_weight)], [])
                elif ttype == "homomorphism":
                    cweight = weight - op_weight; i = 1
                    while cweight >= 0:
                        logger.debug(f"Adding shifts of monomilas of weights {cweight} with degree {i}")
                        to_add = sum([operator(mon).monomials() for mon in self.homogeneous_monomials(cweight) if mon.degree() == i], [])
                        i += 1; cweight -= op_weight
                else:
                    cweight = weight - 1
                    while cweight >= 0:
                        logger.debug(f"Adding operation of monomilas of weights {cweight} that has weight {weight}")
                        to_add = sum([[m for m in operator(mon).monomials() if self(m) == weight] for mon in self.homogeneous_monomials(cweight)], [])
                        cweight -= 1
                logger.debug(f"Adding {len(to_add)} elements")
                result.update(to_add)
                        
            ## multiplication part
            for i in range(1,weight//2 + 1):
                logger.debug(f"Adding product of monomilas of weights {i} and {weight-i}")
                to_add = [tl*th for (tl,th) in product(self.homogeneous_monomials(i), self.homogeneous_monomials(weight-i))]
                logger.debug(f"Adding {len(to_add)} elements")
                result.update(to_add)

            ## special cases for the variables
            to_add = [v[0] for i,v in enumerate(self.parent().gens()) if self.__base_weights[i] == weight]
            logger.debug(f"Special cases added: {len(to_add)}")
            result.update(to_add)

            return result

    def is_homogeneous(self, element: DPolynomial) -> bool:
        r'''
            Method that check if a polynomial is homogeneous w.r.t. this weight or not.
        '''
        if element == 0:
            return True
        mons = self.parent()(element).monomials()
        w = self(mons[0])
        return all(self(m) == w for m in mons[1:])
    
    def as_vector(self, element: DPolynomial) -> Element:
        element = self.parent()(element)
        if not self.is_homogeneous(element):
            raise ValueError("[WeightFunction] Vector representation only valid for homogeneous d-polynomials")
        
        w = self(element)
        mons = self.homogeneous_monomials(w)
        return vector([element.coefficient(m) for m in mons])
    
    def operation_from_vector(self, vector: Element, weight: int, operation: int):
        r'''
            Method that applies an operation to a vector.

            This method takes a vector, interpret it as an homogenoeus element (hence the need to specifying the weight)
            and applies the corresponding operation to it. When the result is again homogeneous, we return the new vector.

            INPUT:

            * ``vector``: a vector with a parent that can be casted into ``self.parent()``.
            * ``weight``: the weight assigned to the vector. We need the dimension to be appropriate.
            * ``operation``: the operation to be applied. We will check the result is homogeneous again.

            OUTPUT:

            A new vector with the result of applying the given operation to the vector when interpret as a homogeneous d-polynomial.

            TODO: add examples
        '''
        mons = self.homogeneous_monomials(weight)
        if len(vector) != len(mons):
            raise TypeError(f"[WeightFunction] The given vector is not of appropriate dimension (got {len(vector)}, expected {len(mons)})")
        
        element = sum(c*m for (c,m) in zip(vector, mons))
        element = element.operation(operation)
        if not self.is_homogeneous(element):
            raise ValueError("[WeightFunction] After operation, the result is not homogeneous")

        return self.as_vector(element)

__all__ = [
    "DPolynomialRing", "DifferentialPolynomialRing", "DifferencePolynomialRing", "is_DPolynomialRing", # names imported
    "RWOPolynomialRing", "is_RWOPolynomialRing" # deprecated names (backward compatibilities) 
]