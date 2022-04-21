r"""
File for the ring structure of Differential polynomials

This file contains all the parent structures for Differential polynomials
and all the coercion associated classes. Mainly, this module provides the 
class :class:`DiffPolynomialRing_dense`, which is the main parent class defining
a ring of differential polynomials.

EXAMPLES::

    sage: from dalgebra import DiffPolynomialRing
    sage: R.<y> = DiffPolynomialRing(QQ['x']) 
    sage: x = R.base().gens()[0] 
    sage: p = x^2*y[1]^2 - y[2]*y[1]; p
    -y_2*y_1 + x^2*y_1^2
    sage: R
    Ring of differential polynomials in (y) over [Univariate Polynomial Ring in x over Rational Field, d/dx]

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

from sage.all import cached_method, ZZ, latex, diff, prod, parent, CommutativeRing

from sage.categories.all import Morphism, Rings, CommutativeAlgebras
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

from .differential_polynomial_element import DiffPolynomial, DiffPolynomialGen
from ..ring_w_operator.differential_ring import DifferentialRing, DifferentialRings 

_Rings = Rings.__classcall__(Rings)

class DiffPolynomialRingFactory(UniqueFactory):
    r'''
        Factory to create rings of differential polynomials.ss

        This allows to cache the same rings of differential polynomials created from different
        objects. 

        EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x']); R
                Ring of differential polynomials in (y) over [Univariate Polynomial Ring in x over Rational Field, d/dx]
                sage: S = DiffPolynomialRing(QQ['x'], 'y')
                sage: R is DiffPolynomialRing(QQ['x'], 'y')
                True
                sage: R is DiffPolynomialRing(QQ['x'], ['y'])
                True
                sage: R is DiffPolynomialRing(QQ['x'], ('y'))
                True
                sage: R is DiffPolynomialRing(InfinitePolynomialRing(QQ['x'], 'y'))
                True
                sage: R is DiffPolynomialRing(R)
                True

            We can also see the unique generation even with several variables::

                sage: S = DiffPolynomialRing(QQ['x'], ('y','a')); S
                Ring of differential polynomials in (a, y) over [Univariate Polynomial Ring in x over Rational Field, d/dx]
                sage: S is DiffPolynomialRing(QQ['x'], ['y','a'])
                True
                sage: S is DiffPolynomialRing(QQ['x'], ('y','a'))
                True
                sage: S is DiffPolynomialRing(QQ['x'], names = ('y','a'))
                True
                sage: S is DiffPolynomialRing(R, 'a')
                True
                sage: S is DiffPolynomialRing(R, ['a'])
                True

            Remark that, in order to have real uniqueness, the variable names are sorted. The use of 
            the Sage notation ``<·,·>`` is then discouraged::

                sage: S.<y,a> = DiffPolynomialRing(QQ['x'])
                sage: y
                a_*
                sage: a
                y_*
    '''
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        ## Extracting the input from args and kwds
        if(len(args) == 0):
            base = kwds["base"]; names = kwds["names"]; derivation=kwds.get("derivation", diff)
        elif(len(args) == 1):
            base = args[0]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            names = kwds.get("names", [])
            derivation=kwds.get("derivation", diff)
        elif(len(args) == 2):
            base = args[0]; names = args[1]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            if("names" in kwds):
                raise TypeError("Duplicated value for the generators")
            derivation=kwds.get("derivation", diff)
        elif(len(args) == 2):
            base = args[0]; names = args[1]; derivation=args[2]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            if("names" in kwds):
                raise TypeError("Duplicated value for the generators")
            if("derivation" in kwds):
                raise TypeError("Duplicated value for the derivation")

        ## Processing the input
        if not type(names) in (list, tuple):
            names = tuple([str(names)])

        if(isinstance(base, InfinitePolynomial_dense) or isinstance(base, InfinitePolynomialRing_sparse)):
            names = tuple(list(base._names)+list(names))
            base = base.base()

        if(len(names) == 0):
            raise ValueError("No variables given: impossible to create a ring")

        ## Sorting the variables
        names = list(names); names.sort(); names = tuple(names) # pylint: disable=no-member

        ## Managing the derivation
        try:
            der_module = base.derivation_module()
            if (not callable(derivation) and not derivation in der_module):
                raise ValueError(f"The element {derivation} is not a derivation in {der_module}")
            elif (not derivation in der_module):
                if(der_module.dimension() == 0):
                    if(any(derivation(el) != 0 for el in [base.one(), base.zero()] + list(base.gens()))):
                        raise ValueError(f"The element {derivation} is not the zero derivation")
                    derivation = der_module.zero()
                else:
                    derivation = sum(derivation(base.gens()[i])*der_module.basis()[i] for i in range(base.ngens()))
            else:
                derivation = der_module(derivation)
        except NotImplementedError:
            ## The ring has no derivation module, we keep the derivation given
            pass

        return (base, names, derivation)

    def create_object(self, _, key):
        base, names, derivation = key
        result = DiffPolynomialRing_dense(base, names, derivation)
        ## Checking the overlaping between previous variables and the new generators
        for v in base.gens():
            for g in result.gens():
                if(g.contains(v)):
                    raise TypeError("There ir an overlapping in variables: %s inside %s" %(v, g))
        
        return result

DiffPolynomialRing = DiffPolynomialRingFactory("dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing")

class DiffPolynomialRing_dense (InfinitePolynomialRing_dense):
    r'''
        Class for a Ring of differential polynomials.

        Given a differential ring `R`, we can define the ring of differential polynomials
        on `y` over `R` as the *infinite polynomial ring* 

        .. MATH::

            R[y_0, y_1,\ldots]

        where the derivation `\partial` has been uniquely extended such that, for all `n \in \mathbb{N}`:

        .. MATH::

            \partial(y_n) = y_{n+1}.

        The ring of differential polynomials on `y` over `R` is denoted by `R\{y\}`. We can iterate the 
        process to define th ring of differential polynomials in several variables:

        .. MATH::

            R\{y,z\} \simeq R\{y\}\{z\} \simeq R\{z\}\{y\}

        This class represents exactly the ring of differential polynomial over the given ring ``base`` 
        with variables given in ``names``.

        This class inherits from :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`,
        which is the Sage structure to manipulate polynomial rings over infinitely many variables.

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R`.
        * ``names``: set of names for the variables of the new ring.

        EXAMPLES::

            sage: from dalgebra import DiffPolynomialRing
            sage: R.<y> = DiffPolynomialRing(QQ['x']); R
            Ring of differential polynomials in (y) over [Univariate Polynomial Ring in x over Rational Field, d/dx]
            sage: S.<a,b> = DiffPolynomialRing(ZZ); S
            Ring of differential polynomials in (a, b) over [Integer Ring, 0]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: diff(y[1])
            y_2
            sage: diff(a[1]*b[0]) #Leibniz Rule
            a_2*b_0 + a_1*b_1
    '''
    Element = DiffPolynomial

    def __init__(self, base, names, derivation=diff):
        # checking derivation
        if not base in DifferentialRings:
            base = DifferentialRing(base, derivation)
        self.__inner_derivation = base.derivation

        ## Line to set the appropriate parent class
        CommutativeRing.__init__(self, base, category=[DifferentialRings(), CommutativeAlgebras(base)])
        ## Initializing the ring of infinitely many variables
        super().__init__(base, names, 'deglex')
        ## Resetting the category to be the appropriate
        CommutativeRing.__init__(self, base, category=[DifferentialRings(), CommutativeAlgebras(base)])
        

        # cache variables
        self.__cache_derivatives = {}

        # registering conversion to simpler structures
        current = self.base()
        morph = DiffPolySimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = DiffPolySimpleMorphism(self, current)
            current.register_conversion(morph)

    #################################################
    ### Methods from DifferentialRings
    #################################################
    def derivation(self, element):
        r'''
            Computes the derivation of an element.

            This method catchs the essence of a :class:`DiffPolynomialRing`: the extension
            of the derivation on the base ring (retrieved by ``self.base()``) to the 
            infinite polynomial ring in such a way that the variables are linked linearly with the 
            derivation.

            For element in the base ring, this method relies on the Sage method :func:`diff`.

            INPUT:

            * ``element``: an object. Must be included in ``self``. 

            OUTPUT:

            An element in ``self`` that represents the derivative of ``element``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: R.derivation(y[0])
                y_1
                sage: R.derivation(x)
                1
                sage: R.derivation(x*y[10])
                x*y_11 + y_10
                sage: R.derivation(x^2*y[1]^2 - y[2]*y[1])
                -y_3*y_1 - y_2^2 + 2*x^2*y_2*y_1 + 2*x*y_1^2

            This derivation also works naturally with several infinite variables::

                sage: S = DiffPolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.derivation(a[1] + y[0]*a[0])
                a_1*y_0 + a_0*y_1 + a_2
        '''
        if(element in self):
            element = self(element)
        else:
            element=self(str(element))
            
        if(element in self.base()):
            return self.base()(self.__inner_derivation(self.base()(element)))
        
        if(not element in self.__cache_derivatives):
            generators = self.gens()
            if(element.is_monomial()):
                c = element.coefficients()[0]
                m = element.monomials()[0]
                v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                v = [self(str(el)) for el in v]
                base = c*prod([v[i]**(d[i]-1) for i in range(len(v))], self.one())

                first_term = self.derivation(c)*self(str(m))
                second_term = self.zero()
                for i in range(len(v)):
                    to_add = d[i]*prod([v[j] for j in range(len(v)) if j != i], self.one())
                    for g in generators:
                        if(g.contains(v[i])):
                            to_add *= g[g.index(v[i])+1]
                            break
                    second_term += to_add
                self.__cache_derivatives[element] = first_term + base*second_term
            else:
                c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                self.__cache_derivatives[element] = sum(self.derivation(c[i])*m[i] + c[i]*self.derivation(m[i]) for i in range(len(m)))
                
        return self.__cache_derivatives[element]

    def constants(self):
        return self.base().constants()

    #################################################
    ### Coercion methods
    #################################################
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))
        
    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into a :class:`~dalgebra.differential_polynomial.differential_polynomial_element.DiffPolynomial`.
        '''
        p = super()._element_constructor_(x)
        return self.element_class(self, p)

    @cached_method
    def gen(self, i=None):
        r'''
            Override method to create the `i^{th}` generator (see method 
            :func:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_sparse.gen`).

            For a :class:`DiffPolynomialRing_dense`, the generator type is 
            :class:`~dalgebra.differential_polynomial.differential_polynomial_element.DiffPolynomialGen`
            which provides extra features to know if an object can be generated by that generator.
            See tis documentation for further details.

            INPUT:

            * ``i``: index of the required generator.

            OUTPUT:

            A :class:`~dalgebra.differential_polynomial.differential_polynomial_element.DiffPolynomialGen`
            representing the `i^{th}` generator of ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: from dalgebra.differential_polynomial.differential_polynomial_element import DiffPolynomialGen
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.gen(0)
                y_*
                sage: R.gen(0) is y
                True
                sage: isinstance(R.gen(0), DiffPolynomialGen)
                True
                sage: S = DiffPolynomialRing(ZZ, ('a', 'b'))
                sage: S
                Ring of differential polynomials in (a, b) over [Integer Ring, 0]
                sage: S.gen(0)
                a_*
                sage: S.gen(1)
                b_*
        '''
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return DiffPolynomialGen(self, self._names[i])
                
    def construction(self):
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DiffPolynomialRing_dense`, the associated functor class is :class:`DPolyRingFunctor`.
            See its documentation for further information.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: from dalgebra.differential_polynomial.differential_polynomial_ring import DPolyRingFunctor
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: F, S = R.construction()
                sage: isinstance(F, DPolyRingFunctor)
                True
                sage: F
                DiffPolynomialRing(*,('y',))
                sage: S == QQ['x']
                True
        '''
        return DPolyRingFunctor(self._names), self._base
    
    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds):
        res = super().__call__(*args, **kwds)
        return self.element_class(self, res)

    ## Other magic methods   
    def __repr__(self):
        return "Ring of differential polynomials in (%s) over [%s, %s]" %(", ".join(self._names), self._base, self.__inner_derivation)

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.zero()
                0
        '''
        return self(0)
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a randome element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        p = super().random_element(*args,**kwds)
        return self(p)

    def eval(self, element, *args, **kwds):
        r'''
            Method to evaluate elements in the ring of differential polynomials.

            Since the differential polynomials have an intrinsic meaning (namely, the 
            variables are related by derivation), evaluating a differential polynomial
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

            The resulting element after evaluating the variable `\alpha_n = \partial^n(\alpha)`,
            where `\alpha` is the name of the generator.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x']); x = R.base().gens()[0]
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

                sage: S = DiffPolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.eval(a[1] + y[0]*a[0], a=x, y=x^2)
                x^3 + 1
                sage: in_eval = S.eval(a[1] + y[0]*a[0], y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of differential polynomials in (a) over [Univariate Polynomial Ring in x over Rational Field, d/dx]
        '''
        if(not element in self):
            raise TypeError("Impossible to evaluate %s as an element of %s" %(element, self))
        g = self.gens(); final_input = {}
        names = [el._name for el in g]
        if(len(args) > self.ngens()):
            raise ValueError("Too many argument for evaluation: given %d, expected (at most) %d" %(len(args), self.ngens()))
        for i in range(len(args)):
            final_input[g[i]] = args[i]
        for key in kwds:
            if(not key in names):
                raise TypeError("Invalid name for argument %s" %key)
            gen = g[names.index(key)]
            if(gen in final_input):
                raise TypeError("Duplicated value for generator %s" %gen)
            final_input[gen] = kwds[key]

        max_derivation = {gen: 0 for gen in final_input}
        for v in element.variables():
            for gen in max_derivation:
                if(gen.contains(v)):
                    max_derivation[gen] = max(max_derivation[gen], gen.index(v))
                    break
        
        to_evaluate = {}
        for gen in max_derivation:
            for i in range(max_derivation[gen]+1):
                to_evaluate[str(gen[i])] = diff(final_input[gen], i)

        ## Computing the final ring
        values = list(final_input.values())
        R = parent(values[0])
        for i in range(1, len(values)):
            R = pushout(R, parent(values[i]))

        poly = element.polynomial()
        ## Adding all the non-appearing variables on element
        if(len(final_input) == len(g)):
            for v in poly.parent().gens():
                if (v not in poly.variables()) and (not str(v) in to_evaluate):
                    to_evaluate[str(v)] = 0
        else:
            left_gens = [gen for gen in g if gen not in final_input]
            R = DiffPolynomialRing(R, [el._name for el in left_gens])
            for v in poly.parent().gens():
                if (not any(gen.contains(v) for gen in left_gens)) and (not str(v) in to_evaluate):
                    to_evaluate[str(v)] = 0

        return R(poly(**to_evaluate))

def is_DiffPolynomialRing(element):
    r'''
        Method to check whether an object is  rng of differential polynomial.
    '''
    return isinstance(element, DiffPolynomialRing_dense)

class DPolyRingFunctor (ConstructionFunctor):
    r'''
        Class representing Functor for creating :class:`DiffPolynomialRing_dense`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential 
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DiffPolynomialRing_dense`)

        EXAMPLES::

            sage: from dalgebra import DiffPolynomialRing
            sage: R.<y> = DiffPolynomialRing(QQ['x'])
            sage: F, S = R.construction()
            sage: F(S) is R
            True
            sage: R = DiffPolynomialRing(R, 'a')
            sage: F, T = R.construction()
            sage: F
            DiffPolynomialRing(*,('a', 'y'))
            sage: R is F(T)
            True
    '''
    def __init__(self, variables):
        self.__variables = variables
        super().__init__(_Rings,_Rings)
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _apply_functor(self, x):
        return DiffPolynomialRing(x,self.__variables)
        
    def _repr_(self):
        return "DiffPolynomialRing(*,%s)" %(str(self.__variables))
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.__variables == self.__variables)

    def merge(self, other):
        pass

    def variables(self):
        return self.__variables

class DiffPolySimpleMorphism (Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`DiffPolynomialRing_dense` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        if(p.degree() == 0):
            return self.codomain()(p.coefficients()[0])

        return self.codomain(str(p))
