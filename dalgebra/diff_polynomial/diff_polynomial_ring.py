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

from sage.all import cached_method, ZZ, latex, diff, prod, parent, CommutativeRing, Hom

from sage.categories.all import Morphism, Rings, CommutativeAlgebras
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialRing_dense, InfinitePolynomialRing_sparse
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module


from .diff_polynomial_element import RWOPolynomial, RWOPolynomialGen
from ..ring_w_operator.ring_w_operator import RingsWithOperator 
from ..ring_w_operator.differential_ring import DifferentialRing, DifferentialRings 
from ..ring_w_operator.difference_ring import DifferenceRing, DifferenceRings

_Rings = Rings.__classcall__(Rings)

## Factories for all structures
class RWOPolynomialRingFactory(UniqueFactory):
    r'''
        Factory to create a ring of polynomials over a ring with an operator.

        This allows to cache the same rings created from different objects. See
        :class:`RWOPolynomialRing_dense` for further information on this structure.

        Since the class :class:`RWOPolynomialRing_dense` is abstract, this class
        is only useful to unify the creation of other subclasses, so we do not provide 
        any example or test for this. See the tests for :class:`DifferentialPolynomialRingFactory`
        and :class:`DifferencePolynomialRingFactory` for more details.
    '''
    def _read_arguments(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        ## Extracting the input from args and kwds
        if(len(args) == 0):
            base = kwds["base"]; names = kwds["names"]; operation=kwds.get("derivation", lambda p : 0)
        elif(len(args) == 1):
            base = args[0]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            names = kwds.get("names", [])
            operation=kwds.get("operation", lambda p : 0)
        elif(len(args) == 2):
            base = args[0]; names = args[1]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            if("names" in kwds):
                raise TypeError("Duplicated value for the generators")
            operation=kwds.get("operation", lambda p : 0)
        elif(len(args) == 2):
            base = args[0]; names = args[1]; operation=args[2]
            if("base" in kwds):
                raise TypeError("Duplicated value for the base ring")
            if("names" in kwds):
                raise TypeError("Duplicated value for the generators")
            if("operation" in kwds):
                raise TypeError("Duplicated value for the operation")

        return base, names, operation

    def _adjust_names(self, base, names):
        if not type(names) in (list, tuple):
            names = tuple([str(names)])

        if(isinstance(base, InfinitePolynomial_dense) or isinstance(base, InfinitePolynomialRing_sparse)):
            names = tuple(list(base._names)+list(names))
            base = base.base()

        if(len(names) == 0):
            raise ValueError("No variables given: impossible to create a ring")

        ## Sorting the variables
        names = list(names); names.sort(); names = tuple(names) # pylint: disable=no-member

        return base, names

    def _adjust_operation(self, _, operation):
        return operation

    def _adjust_base(self, base, operation):
        if not base in RingsWithOperator:
            base = RingsWithOperator(base, operation)
        return base

    def create_key(self, *args, **kwds):
        ## Extracting and checking the arguments of the method
        base, names, operation = self._read_arguments(*args, **kwds)
        ## Computing the final names to be used
        base, names = self._adjust_names(base, names)
        ## Adapting the operation to the appropriate type
        operation = self._adjust_operation(base, operation)
        ## Making sure the base is of the required type and category
        base = self._adjust_base(base, operation)

        return (base, names)

    def _build_result(self, base, names):
        return RWOPolynomialRing_dense(base, names)

    def create_object(self, _, key):
        base, names = key

        result = self._build_result(base, names)

        ## Checking the overlaping between previous variables and the new generators
        for v in base.gens():
            for g in result.gens():
                if g.contains(v):
                    raise TypeError(f"There is an overlapping in variables: {v} inside {g}")
        
        ## Everything correct, we return
        return result

class DifferentialPolynomialRingFactory(RWOPolynomialRingFactory):
    r'''
        Factory to create rings of differential polynomials.

        This allows to cache the same rings of differential polynomials created from different
        objects. 

        EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing
                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); R
                Ring of differential polynomials in (y) over Differential Ring [Univariate 
                Polynomial Ring in x over Rational Field] with derivation [Map from 
                callable d/dx]
                sage: S = DifferentialPolynomialRing(QQ['x'], 'y')
                sage: R is DifferentialPolynomialRing(QQ['x'], 'y')
                True
                sage: R is DifferentialPolynomialRing(QQ['x'], ['y'])
                True
                sage: R is DifferentialPolynomialRing(QQ['x'], ('y'))
                True
                sage: R is DifferentialPolynomialRing(InfinitePolynomialRing(QQ['x'], 'y'))
                True
                sage: R is DifferentialPolynomialRing(R)
                True

            We can also see the unique generation even with several variables::

                sage: S = DifferentialPolynomialRing(QQ['x'], ('y','a')); S
                Ring of differential polynomials in (a, y) over Differential Ring [Univariate 
                Polynomial Ring in x over Rational Field] with derivation [Map from callable 
                d/dx]
                sage: S is DifferentialPolynomialRing(QQ['x'], ['y','a'])
                True
                sage: S is DifferentialPolynomialRing(QQ['x'], ('y','a'))
                True
                sage: S is DifferentialPolynomialRing(QQ['x'], names = ('y','a'))
                True
                sage: S is DifferentialPolynomialRing(R, 'a')
                True
                sage: S is DifferentialPolynomialRing(R, ['a'])
                True

            Remark that, in order to have real uniqueness, the variable names are sorted. The use of 
            the Sage notation ``<·,·>`` is then discouraged::

                sage: S.<y,a> = DifferentialPolynomialRing(QQ['x'])
                sage: y
                a_*
                sage: a
                y_*
    '''
    def _read_arguments(self, *args, **kwds):
        # we set the default value for operation from derivation:
        if (not "operation" in kwds):
            if ("derivation" in kwds):
                kwds["operation"] = kwds["derivation"]
            elif len(args) != 2:
                kwds["operation"] = diff # derivation from Sage
        return super()._read_arguments(*args, **kwds)
    
    def _adjust_operation(self, base, derivation):
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
        return derivation

    def _adjust_base(self, base, operation):
        if not base in DifferentialRings:
            base = DifferentialRing(base, operation)
        return base
        
    def _build_result(self, base, names):
        return DifferentialPolynomialRing_dense(base, names)

class DifferencePolynomialRingFactory(RWOPolynomialRingFactory):
    r'''
        Factory to create rings of difference polynomials.

        This allows to cache the same rings of difference polynomials created from different
        objects. 

        EXAMPLES::

                sage: from dalgebra import DifferencePolynomialRing
                sage: R.<y> = DifferencePolynomialRing(QQ['x']); R
                Ring of differential polynomials in (y) over Differential Ring [Univariate 
                Polynomial Ring in x over Rational Field] with derivation [Map from 
                callable d/dx]
                sage: S = DifferencePolynomialRing(QQ['x'], 'y')
                sage: R is DifferencePolynomialRing(QQ['x'], 'y')
                True
                sage: R is DifferencePolynomialRing(QQ['x'], ['y'])
                True
                sage: R is DifferencePolynomialRing(QQ['x'], ('y'))
                True
                sage: R is DifferencePolynomialRing(InfinitePolynomialRing(QQ['x'], 'y'))
                True
                sage: R is DifferencePolynomialRing(R)
                True

            We can also see the unique generation even with several variables::

                sage: S = DifferencePolynomialRing(QQ['x'], ('y','a')); S
                Ring of difference polynomials in (a, y) over Difference Ring [Univariate 
                Polynomial Ring in x over Rational Field] with derivation [Map from callable 
                d/dx]
                sage: S is DifferencePolynomialRing(QQ['x'], ['y','a'])
                True
                sage: S is DifferencePolynomialRing(QQ['x'], ('y','a'))
                True
                sage: S is DifferencePolynomialRing(QQ['x'], names = ('y','a'))
                True
                sage: S is DifferencePolynomialRing(R, 'a')
                True
                sage: S is DifferencePolynomialRing(R, ['a'])
                True

            Remark that, in order to have real uniqueness, the variable names are sorted. The use of 
            the Sage notation ``<·,·>`` is then discouraged::

                sage: S.<y,a> = DifferencePolynomialRing(QQ['x'])
                sage: y
                a_*
                sage: a
                y_*
    '''
    def _read_arguments(self, *args, **kwds):
        # we set the default value for operation from derivation:
        if (not "operation" in kwds):
            if ("difference" in kwds):
                kwds["operation"] = kwds["difference"]
            elif len(args) != 2:
                kwds["operation"] = lambda p : p #identity
        return super()._read_arguments(*args, **kwds)

    def _adjust_operation(self, base, difference):
        hom_module = Hom(base,base)
        if (not callable(difference) and not difference in hom_module):
            raise ValueError(f"The element {difference} is not an homomorphism in {hom_module}")
        elif (not difference in hom_module):
            try:
                difference = hom_module([difference(g) for g in base.gens()])
            except ValueError:
                raise ValueError(f"The difference {difference} is not a valid homomorphism of {hom_module}")
        else:
            difference = hom_module(difference)
        
        return difference

    def _adjust_base(self, base, operation):
        if not base in DifferenceRings:
            base = DifferenceRing(base, operation)
        return base
        
    def _build_result(self, base, names):
        return DifferencePolynomialRing_dense(base, names)

RWOPolynomialRing = RWOPolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.RWOPolynomialRing")
DifferentialPolynomialRing = DifferentialPolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.DifferentialPolynomialRing")
DifferencePolynomialRing = DifferencePolynomialRingFactory("dalgebra.diff_polynomial.diff_polynomial_ring.DifferencePolynomialRing")

class RWOPolynomialRing_dense (InfinitePolynomialRing_dense):
    r'''
        Class for a ring of polynomials over a :class:`~dalgebra.ring_w_operator.ring_w_operator.RingWithOperator`.

        Given a ring with an associated operator `(R, d)`, where `d : R \rightarrow R`, we can 
        always define the ring of polynomials on `y` as the *infinite polynomial ring*

        .. MATH::

            R[y_0,y_1,\ldots]

        where the operation acts naturally (preserving all its properties) over this ring and,
        in particular, `d(y_i) = y_{i+1}` for all `n \in \mathbb{N}`.

        This class represents exactly the ring of polynomial with this operator over the given ring ``base`` 
        with variables given in ``names``.

        This class inherits from :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`,
        which is the Sage structure to manipulate polynomial rings over infinitely many variables.

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R` (has to be in the 
          category :class:`RingsWithOperator`)
        * ``names``: set of names for the variables of the new ring.

        This class is abstract (since the properties of the operator are not known, so extending it to the whole
        ring is not obvious). See different subclasses to check its behavior.
    '''
    Element = RWOPolynomial

    def _base_category(self): return RingsWithOperator()

    def _set_categories(self, base): return [RingsWithOperator(), CommutativeAlgebras(base)]

    def __init__(self, base, names):
        if not base in self._base_category():
            raise TypeError("The base must be a differential ring")

        ## Line to set the appropriate parent class
        CommutativeRing.__init__(self, base, category=self._set_categories(base))
        ## Initializing the ring of infinitely many variables
        super().__init__(base, names, 'deglex')
        ## Resetting the category to be the appropriate
        CommutativeRing.__init__(self, base, category=self._set_categories(base))
        
        self.__inner_operation = base.operation

        # cache variables
        self.__cache = {}

        # registering conversion to simpler structures
        current = self.base()
        morph = RWOPolySimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = RWOPolySimpleMorphism(self, current)
            current.register_conversion(morph)

    @property
    def inner(self): return self.__inner_operation

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
            and then transforms the output into the corresponding type for ``self``.
        '''
        p = super()._element_constructor_(x)
        return self.element_class(self, p)

    @cached_method
    def gen(self, i=None):
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
                operator [Map from callable 0]
                sage: S.gen(0)
                a_*
                sage: S.gen(1)
                b_*
        '''
        if(not(i in ZZ) or (i < 0 or i > len(self._names))):
            raise ValueError("Invalid index for generator")
        
        return RWOPolynomialGen(self, self._names[i])
                
    def construction(self):
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`RWOPolynomialRing_dense`, the associated functor class is :class:`RWOPolyRingFunctor`.
            See its documentation for further information.
        '''
        return RWOPolyRingFunctor(self._names), self._base
    
    #################################################
    ### Magic python methods
    #################################################
    def __call__(self, *args, **kwds):
        res = super().__call__(*args, **kwds)
        return self.element_class(self, res)

    ## Other magic methods   
    def __repr__(self):
        return "Ring of infinite polynomials in (%s) over %s" %(", ".join(self._names), self._base)

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing
                sage: R.<y> = DifferentialPolynomialRing(QQ['x'])
                sage: R.one()
                1
        '''
        return self(1)
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing
                sage: R.<y> = DifferentialPolynomialRing(QQ['x'])
                sage: R.zero()
                0
        '''
        return self(0)
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a random element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        p = super().random_element(*args,**kwds)
        return self(p)

    def _apply_to_outside(self, element, times):
        return self.base().operation(element, times=times)
        
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

        max_application = {gen: 0 for gen in final_input}
        for v in element.variables():
            for gen in max_application:
                if(gen.contains(v)):
                    max_application[gen] = max(max_application[gen], gen.index(v))
                    break
        
        to_evaluate = {}
        for gen in max_application:
            for i in range(max_application[gen]+1):
                to_evaluate[str(gen[i])] = parent(final_input[gen])(self._apply_to_outside(final_input[gen], i))

        ## Computing the final ring
        values = list(final_input.values())
        R = self.base()
        for value in values:
            R = pushout(R, parent(value))

        poly = element.polynomial()
        ## Adding all the non-appearing variables on element
        if(len(final_input) == len(g)):
            for v in poly.parent().gens():
                if (v not in poly.variables()) and (not str(v) in to_evaluate):
                    to_evaluate[str(v)] = 0
        else:
            left_gens = [gen for gen in g if gen not in final_input]
            R = self.construction()[0].__class__([el._name for el in left_gens])(R)
            for v in poly.parent().gens():
                if (not any(gen.contains(v) for gen in left_gens)) and (not str(v) in to_evaluate):
                    to_evaluate[str(v)] = 0

        return R(poly(**to_evaluate))

class DifferentialPolynomialRing_dense (RWOPolynomialRing_dense):
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

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R`.
        * ``names``: set of names for the variables of the new ring.

        EXAMPLES::

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
    '''
    Element = RWOPolynomial

    def _base_category(self): return DifferentialRings()

    def _set_categories(self, base): return [DifferentialRings(), CommutativeAlgebras(base)]

    def __init__(self, base, names):
        super().__init__(base, names)

    #################################################
    ### Methods from DifferentialRings
    #################################################
    def derivation(self, element):
        r'''
            Computes the derivation of an element.

            This method catchs the essence of a :class:`DifferentialPolynomialRing`: the extension
            of the derivation on the base ring (retrieved by ``self.base()``) to the 
            infinite polynomial ring in such a way that the variables are linked linearly with the 
            derivation.

            For element in the base ring, this method relies on the Sage method :func:`diff`.

            INPUT:

            * ``element``: an object. Must be included in ``self``. 

            OUTPUT:

            An element in ``self`` that represents the derivative of ``element``.

            EXAMPLES::

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
        '''
        if(element in self):
            element = self(element)
        else:
            element=self(str(element))
            
        if(element in self.base()):
            return self.base()(self.inner(self.base()(element)))
        
        if(not element in self._RWOPolynomialRing_dense__cache):
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
                self._RWOPolynomialRing_dense__cache[element] = first_term + base*second_term
            else:
                c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                self._RWOPolynomialRing_dense__cache[element] = sum(self.derivation(c[i])*m[i] + c[i]*self.derivation(m[i]) for i in range(len(m)))
                
        return self._RWOPolynomialRing_dense__cache[element]

    def constants(self):
        return self.base().constants()

    #################################################
    ### Coercion methods
    #################################################  
    def construction(self):
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DifferentialPolynomialRing_dense`, the associated functor class is :class:`DifferentialPolyRingFunctor`.
            See its documentation for further information.

            EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing
                sage: from dalgebra.diff_polynomial.diff_polynomial_ring import DifferentialPolyRingFunctor
                sage: R.<y> = DifferentialPolynomialRing(QQ['x'])
                sage: F, S = R.construction()
                sage: isinstance(F, DifferentialPolyRingFunctor)
                True
                sage: F
                DifferentialPolynomialRing(*,('y',))
                sage: S
                Differential Ring [Univariate Polynomial Ring in x over Rational Field] with derivation [Map from callable d/dx]
        '''
        return DifferentialPolyRingFunctor(self._names), self._base
    
    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return "Ring of differential polynomials in (%s) over %s" %(", ".join(self._names), self._base)

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"
            
    #################################################
    ### Element generation methods
    #################################################
    def _apply_to_outside(self, element, times):
        try:
            return super()._apply_to_outside(self, element, times)
        except:
            return diff(element, times)

class DifferencePolynomialRing_dense (RWOPolynomialRing_dense):
    r'''
        Class for a Ring of difference polynomials.

        Given a difference ring `R`, we can define the ring of difference polynomials
        on `y` over `R` as the *infinite polynomial ring* 

        .. MATH::

            R[y_0, y_1,\ldots]

        where the difference `\sigma` has been uniquely extended such that, for all `n \in \mathbb{N}`:

        .. MATH::

            \sigma(y_n) = y_{n+1}.

        The ring of difference polynomials on `y` over `R` is denoted by `R\{y\}`. We can iterate the 
        process to define th ring of difference polynomials in several variables:

        .. MATH::

            R\{y,z\} \simeq R\{y\}\{z\} \simeq R\{z\}\{y\}

        This class represents exactly the ring of difference polynomial over the given ring ``base`` 
        with variables given in ``names``.

        INPUT:

        * ``base``: ring structure that represent the base ring of coefficients `R`.
        * ``names``: set of names for the variables of the new ring.

        EXAMPLES::

            sage: from dalgebra import DifferencePolynomialRing
            sage: R.<y> = DifferencePolynomialRing(QQ['x']); R
            Ring of differential polynomials in (y) over Difference Ring 
            [Univariate Polynomial Ring in x over Rational Field] with difference 
            [Map from callable x --> x]
            sage: S.<a,b> = DifferentialPolynomialRing(ZZ); S
            Ring of differential polynomials in (a, b) over Differential Ring [Integer Ring] 
            with derivation [Map from callable Identity map]

        We can now create objects in those rings using the generators ``y``, ``a`` and ``b``::

            sage: y[1]
            y_1
            sage: y[1].difference()
            y_2
            sage: (a[1]*b[0]).difference() #Homomorphism rule
            a_2*b_1
    '''
    Element = RWOPolynomial

    def _base_category(self): return DifferenceRings()

    def _set_categories(self, base): return [DifferenceRings(), CommutativeAlgebras(base)]

    def __init__(self, base, names):
        super().__init__(base, names)

    #################################################
    ### Methods from DifferentialRings
    #################################################
    def difference(self, element):
        r'''
            Computes the difference of an element.

            This method catchs the essence of a :class:`DifferencePolynomialRing`: the extension
            of the difference on the base ring (retrieved by ``self.base()``) to the 
            infinite polynomial ring in such a way that the variables are linked linearly with the 
            derivation.

            INPUT:

            * ``element``: an object. Must be included in ``self``. 

            OUTPUT:

            An element in ``self`` that represents the difference of ``element``.

            EXAMPLES::

                sage: from dalgebra import DifferencePolynomialRing
                sage: R.<y> = DifferencePolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: R.difference(y[0])
                y_1
                sage: R.difference(x)
                x
                sage: R.difference(x*y[10])
                x*y_11
                sage: R.difference(x^2*y[1]^2 - y[2]*y[1])
                x^3*y[2]^2 - y[3]*y[2]

            This difference also works naturally with several infinite variables::

                sage: S = DifferencePolynomialRing(R, 'a'); a,y = S.gens()
                sage: S.difference(a[1] + y[0]*a[0])
                a_2+ a_1*y_1

            We can see other type of shifts or differences operators::

                sage: T.<z> = DifferencePolynomialRing(QQ[x], difference=lambda p : p(x=x+1))
                sage: T.difference(z[0])
                z[1]
                sage: T.difference(x)
                x + 1
                sage: T.difference(x^2*z[1]^2 - z[2]*z[1])
                (x + 1)^2*z[2]^2 - z[3]*z[2]
        '''
        if(element in self):
            element = self(element)
        else:
            element=self(str(element))
            
        if(element in self.base()):
            return self.base()(self.inner(self.base()(element)))
        
        if(not element in self._RWOPolynomialRing_dense__cache):
            generators = self.gens()
            if(element.is_monomial()):
                c = element.coefficients()[0]
                m = element.monomials()[0]
                v = element.variables(); d = [element.degree(v[i]) for i in range(len(v))]
                v = [self(str(el)) for el in v]

                result = self.difference(c)
                for i in range(len(v)):
                    for g in generators:
                        if g.contains(v[i]):
                            result *= g[g.index(v[i])+1]**d[i]
                            break
                
                self._RWOPolynomialRing_dense__cache[element] = result
            else:
                c = element.coefficients(); m = [self(str(el)) for el in element.monomials()]
                self._RWOPolynomialRing_dense__cache[element] = sum(self.difference(c[i])*self.difference(m[i]) for i in range(len(m)))
                
        return self._RWOPolynomialRing_dense__cache[element]

    def constants(self):
        return self.base().constants()

    #################################################
    ### Coercion methods
    #################################################  
    def construction(self):
        r'''
            Return the associated functor and input to create ``self``.

            The method construction returns a :class:`~sage.categories.pushout.ConstructionFunctor` and 
            a valid input for it that would create ``self`` again. This is a necessary method to
            implement all the coercion system properly.

            For a :class:`DifferencePolynomialRing_dense`, the associated functor class is :class:`DifferencePolyRingFunctor`.
            See its documentation for further information.

            EXAMPLES::

                sage: from dalgebra import DifferencePolynomialRing
                sage: from dalgebra.diff_polynomial.diff_polynomial_ring import DifferencePolyRingFunctor
                sage: R.<y> = DifferencePolynomialRing(QQ['x'])
                sage: F, S = R.construction()
                sage: isinstance(F, DifferencePolyRingFunctor)
                True
                sage: F
                DifferencePolynomialRing(*,('y',))
                sage: S
                Difference Ring [Univariate Polynomial Ring in x over Rational Field] with derivation [Map from callable d/dx]
        '''
        return DifferentialPolyRingFunctor(self._names), self._base
    
    #################################################
    ### Magic python methods
    #################################################
    def __repr__(self):
        return "Ring of difference polynomials in (%s) over %s" %(", ".join(self._names), self._base)

    def _latex_(self):
        return latex(self._base) + r"\{" + ", ".join(self._names) + r"\}"

def is_RWOPolynomialRing(element):
    r'''
        Method to check whether an object is a ring of infinite polynomial with an operator.
    '''
    return isinstance(element, RWOPolynomialRing_dense)

def is_DifferentialPolynomialRing(element):
    r'''
        Method to check whether an object is a ring of differential polynomials.
    '''
    return isinstance(element, DifferentialPolynomialRing_dense)

def is_DifferencePolynomialRing(element):
    r'''
        Method to check whether an object is a ring of difference polynomials.
    '''
    return isinstance(element, DifferencePolynomialRing_dense)

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
        super().__init__(_Rings,_Rings)
        
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
        pass

    def variables(self):
        return self.__variables

class DifferentialPolyRingFunctor (RWOPolyRingFunctor):
    r'''
        Class representing Functor for creating :class:`DifferentialPolynomialRing_dense`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of differential 
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DifferentialPolynomialRing_dense`)

        EXAMPLES::

            sage: from dalgebra import DifferentialPolynomialRing
            sage: R.<y> = DifferentialPolynomialRing(QQ['x'])
            sage: F, S = R.construction()
            sage: F(S) is R
            True
            sage: R = DifferentialPolynomialRing(R, 'a')
            sage: F, T = R.construction()
            sage: F
            DifferentialPolynomialRing(*,('a', 'y'))
            sage: R is F(T)
            True
    '''
    def __init__(self, variables):
        super().__init__(variables)
      
    def _apply_functor(self, x):
        return DifferentialPolynomialRing(x,self.variables())
        
    def _repr_(self):
        return "DifferentialPolynomialRing(*,%s)" %(str(self.__variables))

class DifferencePolyRingFunctor (RWOPolyRingFunctor):
    r'''
        Class representing Functor for creating :class:`DifferencePolynomialRing_dense`.

        This class represents the functor `F: R \mapsto R\{y^(1),\ldots,y^{(n)}\}`.
        The names of the variables must be given to the functor and, then
        this can take any ring and create the corresponding ring of difference 
        polynomials.

        INPUT:

        * ``variables``: names of the variables that the functor will add (see 
          the input ``names`` in :class:`DifferencePolynomialRing_dense`)

        EXAMPLES::

            sage: from dalgebra import DifferencePolynomialRing
            sage: R.<y> = DifferencePolynomialRing(QQ['x'])
            sage: F, S = R.construction()
            sage: F(S) is R
            True
            sage: R = DifferencePolynomialRing(R, 'a')
            sage: F, T = R.construction()
            sage: F
            DifferencePolynomialRing(*,('a', 'y'))
            sage: R is F(T)
            True
    '''
    def __init__(self, variables):
        super().__init__(variables)
      
    def _apply_functor(self, x):
        return DifferentialPolynomialRing(x,self.variables())
        
    def _repr_(self):
        return "DifferencePolynomialRing(*,%s)" %(str(self.__variables))
         

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
