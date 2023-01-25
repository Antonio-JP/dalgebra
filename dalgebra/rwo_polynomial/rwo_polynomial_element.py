r"""
File for the ring structure of Differential polynomials

This file contains all the element structures for Differential polynomials.

AUTHORS:

    - Antonio Jimenez-Pastor (2012-05-19): initial version

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

from sage.all import cartesian_product, binomial, Parent
from sage.categories.morphism import Morphism # pylint: disable=no-name-in-module
from sage.misc.cachefunc import cached_method #pylint: disable=no-name-in-module
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialGen
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense, InfinitePolynomial_sparse
from sage.rings.semirings.non_negative_integer_semiring import NN
from sage.structure.element import Element #pylint: disable=no-name-in-module

from typing import Collection


#######################################################################################
### AUXILIARY FUNCTIONS AND CLASSES
#######################################################################################
def is_InfinitePolynomial(element):
    r'''
        Method to decide whether or not an element is a polynomial with infinite variables.

        This is a call to ``isinstance`` with the two main element classes of Infinite Polynomial
        Rings.
    '''
    return (isinstance(element, InfinitePolynomial_dense) or isinstance(element, InfinitePolynomial_sparse))

__BIJECTIONS = {}
def IndexBijection(size : int):
    r'''
        Factory for the bijections of a given size.

        This method returns a unique bijection object that allow to map integers to tuples of 
        the given size in a specific order. This order tries to have the appearance of all
        tuples whose sum is fixed as soon as possible.

        For example, for size `3` the tuples generated would be as follows:

        .. MATH::

            (0,0,0) \rightarrow (0,0,1) \rightarrow (0,1,0) \rightarrow (1,0,0) \rightarrow (0,0,2) \rightarrow (0,1,1) 
            \rightarrow (0,2,0) \rightarrow (1,0,1) \rightarrow (1,1,0) \rightarrow (2,0,0) \rightarrow \ldots

        These bijections cache some of its results, hence the convenience of always returning the same 
        bijection object.

        INPUT:

        * ``size``: number of elements of the tuples generated by the bijection.

        OUTPUT:

        A :class:`IndexBijection_Object` with the given bijection.

        EXAMPLES::

            sage: from dalgebra.rwo_polynomial.rwo_polynomial_element import IndexBijection
            sage: size2 = IndexBijection(2)
            sage: size2(0)
            (0, 0)
            sage: size2(10)
            (0, 4)
            sage: size2(100)
            (9, 4)
            sage: size4 = IndexBijection(4)
            sage: [size4(i) for i in range(5)]
            [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0), (1, 0, 0, 0)]

        Since we have a bijection, we can also go back:

            sage: IndexBijection(10).inverse((1,2,3,4,5,6,7,8,9,10)) # around 2ms
            156289762326
    '''
    if not size in __BIJECTIONS:
        __BIJECTIONS[size] = IndexBijection_Object(size)    
    return __BIJECTIONS[size]
    
class IndexBijection_Object (Morphism):
    def __init__(self, size : int):
        Morphism.__init__(self, NN, cartesian_product(size*[NN]))
        self.dim = size

    @staticmethod
    def elements_summing(n: int, l: int) -> int:
        r'''Number of elements summing `n` in `l` elements'''
        return binomial(n+l-1, n)

    @staticmethod
    def tuple_summing(index: int, n: int, l: int) -> tuple[int]:
        r'''Tuple in position ``index`` summing `n` in `l` elements'''
        if index < 0 or index >= IndexBijection_Object.elements_summing(n,l):
            raise ValueError
        if l == 1:
            return tuple([n])
        elif n == 0:
            return tuple(l*[0])
        first = 0
        while index >= IndexBijection_Object.elements_summing(n-first, l-1):
            index -= IndexBijection_Object.elements_summing(n-first, l-1); first += 1
        return tuple([first] + list(IndexBijection_Object.tuple_summing(index, n-first, l-1)))

    @cached_method
    def _call_(self, index: int) -> Element:
        r'''Computes the image of a natural number'''
        if self.dim == 1:
            return index
        sum_of_elements = 0
        while index >= IndexBijection_Object.elements_summing(sum_of_elements, self.dim):
            index -= IndexBijection_Object.elements_summing(sum_of_elements, self.dim)
            sum_of_elements += 1
        return self.codomain()(IndexBijection_Object.tuple_summing(index, sum_of_elements, self.dim))

    @cached_method
    def inverse(self, image: Element) -> int:
        r'''Computes the preimage of a tuple of ``self.dim`` natural numbers'''
        if self.dim == 1:
            return image
        if not len(image) == self.dim:
            raise TypeError("Given element has innapropriate length")
        sum_of_elements = sum(image)
        result = IndexBijection_Object.elements_summing(sum_of_elements-1, self.dim+1) # elements summing less than "sum_of_elements"
        for i in range(len(image)-1):
            result += sum(IndexBijection_Object.elements_summing(sum_of_elements - j, self.dim - i-1) for j in range(image[i]))
            sum_of_elements -= image[i]
        return self.domain()(result)

    def iter(self, sum_bound : int):
        quantity = IndexBijection_Object.elements_summing(sum_bound, self.dim + 1)
        for i in range(quantity): yield self(i) 
#######################################################################################
###
### MAIN CLASS FOR THE GENERATORS
###
#######################################################################################
class RWOPolynomialGen (InfinitePolynomialGen):
    r'''
        Class for generators of :class:`.rwo_polynomial_ring.RWOPolynomialRing_dense`.

        A generator of a :class:`.rwo_polynomial_ring.RWOPolynomialRing_dense` is 
        an object that can create the infinitely many variables associated with a particular name. The variables it generates
        are of the form ``name_index`` where ``name`` is the string defining the variable and the index is the image 
        a :class:`IndexBijection_Object`.

        Let assume `R{y}` is a :class:`.rwo_polynomial_ring.RWOPolynomialRing_dense` with operators `\sigma` and `\delta`.
        Then the generator will be ``y_(i,j)`` representing the element `\sigma^i ( \delta^j (y))`.

        To allow more flexibility, this class provides methods to know if an object can be generated with this
        generator and to obtain the corresponding index.

        INPUT:

        * ``parent``: a :class:`.rwo_polynomial_ring.DifferentialPolynomialRing_dense` where ``self`` will generate its elements.
          This will indicate also the amount of indices allow to generate a variable.
        * ``name``: main part of the name for the generated variales.
    '''
    def __init__(self, parent: Parent, name: str):
        from .rwo_polynomial_ring import is_RWOPolynomialRing
        if(not is_RWOPolynomialRing(parent)):
            raise TypeError("The RWOPolynomialGen must have a ring of polynomial with an operator as parent")

        self.index_map = IndexBijection(parent.noperators())
        super().__init__(parent, name)

    def __getitem__(self, i : int | tuple[int]) -> RWOPolynomial:
        if self._parent.noperators() > 1 and isinstance(i, tuple) and len(i) == self._parent.noperators():
            return self._parent(super().__getitem__(self.index_map.inverse(i)))
        return self._parent(super().__getitem__(i))

    def contains(self, element: RWOPolynomial) -> bool:
        r'''
            Method to know if an object can be generated using ``self``.

            This method analyzes the string associated with ``element`` to determined
            if it is of the appropriate shape to be generated by ``self``.

            INPUT:

            * ``element``: the element to be checked.
            
            OUTPUT:

            ``True`` if the string of the element is of the shape ``X_Y`` where ``X`` is the 
            value of ``self._name``.
        '''
        try:
            element = self._parent(element)
        except:
            return False
        if not element.is_generator():
            return False

        name = str(element)
        spl = name.split("_")
        first = "_".join(spl[:-1])
        return first == self._name

    def __contains__(self, other) -> bool:
        return self.contains(other)

    def index(self, element: RWOPolynomial, as_tuple : bool = True) -> int:
        r'''
            Method to know the index to generate ``element`` using ``self``.

            This method analyzes the string associated with ``element`` to determined
            the appropriate index to generated ``element`` using ``self``.

            INPUT:

            * ``element``: the element to be checked.
            
            OUTPUT:

            Assumed the string form of ``X_Y`` from :func:`contains`, this method returns
            the numerical value of ``Y`` or an error if not possible.
        '''
        if(self.contains(element)):
            index = str(element).split("_")[-1]
            if self._parent.noperators() == 1:
                index = int(index)
            else:
                index = tuple(int(num) for num in index.replace("(","").replace(")","").split(",")) 
                
            if self._parent.noperators() == 1 and not as_tuple:
                index = self.index_map.inverse(index)
            return index

    def next(self, element: RWOPolynomial, operation : int) -> RWOPolynomial:
        r'''
            Method to get the next variable from ``element`` with the given operation
        '''
        if operation < 0 or operation >= self._parent.noperators():
            raise IndexError("The operation requested is out of range")
        index = self.index(element)
        if self._parent.noperators() == 1:
            index += 1
        else: # the index is a tuple and operation is important
            index = list(index); index[operation] += 1
            index = tuple(index)
        return self[index]


    def __hash__(self):
        return hash(self._name)

#######################################################################################
###
### MAIN CLASS FOR THE ELEMENTS
###
#######################################################################################
class RWOPolynomial (InfinitePolynomial_dense):
    r'''
        Class for representing infinite polynomials associated ring with operators.

        Given a ring `R` with several operators `d_1,\ldots,d_n`, we can define the ring of infinite polynomials with an operator
        on `y` over `R` as the *infinite polynomial ring* 

        .. MATH::

            R\{y\} := R[y_\sigma : \sigma \in \mathbb{N}^n]

        where the operations `d_i` has been uniquely extended such that, for all `\sigma \in \mathbb{N}^n`:

        .. MATH::

            d_i(y_\sigma) = y_{\sigma+e_i},

        where `e_i` is the `i`-th canonical vector of length `n`, i.e., a vector of length `n` with all zeros except
        the `i`-th entry, which is a one.

        We can iterate the process to define thr ring of operator polynomials in several variables:

        .. MATH::

            R\{y,z\} \simeq R\{y\}\{z\} \simeq R\{z\}\{y\}

        Objects of this class represents the polynomials of within one of these a ring. They 
        are a natural extension of the class :class:`~sage.rings.polynomial.infinite_polynomial_element.InfinitePolynomial_dense`
        including some extra functionality more specific of these polynomials (such as the the operation, evaluation and orders).

        INPUT:

        * ``parent``: a :class:`.rwo_polynomial_ring.RWOPolynomialRing_dense` where the new element will be contained.
        * ``polynomial``: a valid polynomial to be casted into an element of ``parent``.

        We recommend not to use this constructor, but instead build the polynomials using the generators of the 
        corresponding :class:`.rwo_polynomial_ring.RWOPolynomialRing_dense`.
    '''
    def __init__(self, parent : Parent, polynomial : Element):
        if(is_InfinitePolynomial(polynomial)):
            polynomial = polynomial.polynomial()
        super().__init__(parent, polynomial)

    ###################################################################################
    ### Method for computing special values
    #######################################################################################
    @cached_method
    def orders(self, operation: int = -1) -> tuple[int]:
        r'''
            Method that gets the order of a polynomial in all its variables.

            This method computes the order of a concrete polynomial in all the 
            variables that appear in its parent. This method relies on the method 
            :func:`~dalgebra.rwo_polynomial.rwo_polynomial_ring.RWOPolynomialRing_dense.gens`
            and the method :func:`~RWOPolynomialGen.index`.

            INPUT:

            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            A tuple of integers where the index `i` is the order of ``self`` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates that variable does not show up in the polynomial.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.orders()
                (2, 0)
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.orders()
                (1, 2)
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.orders()
                (-1, 10)
                sage: R.one().orders()
                (-1, -1)
        '''
        var = self.variables() # we get all variables
        gens = self.parent().gens() # we get the generators of the parent

        indices = [[g.index(el) for el in var if el in g] for g in gens]

        if self.parent().noperators() > 1:
            if operation == -1: # we need to add up each tuple
                indices = [[sum(index) for index in lst] for lst in indices]
            else:
                indices = [[index[operation] for index in lst] for lst in indices]
        
        return tuple([max(lst, default = -1) for lst in indices])

    @cached_method
    def order(self, gen : RWOPolynomialGen = None, operation : int = -1) -> int:
        r'''
            Method to obtain the order of a polynomial w.r.t. a variable

            This method computes the order of a polynomial with respect to 
            a particular variable. Such variable has to be provided as a generator of 
            the ring of polynomials (see :class:`RWOPolynomialGen`).

            This method uses the method :func:`orders` as a basic definition of these orders.

            In the case the polynomial only has one differential variable, the input ``gen``
            can be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`RWOPolynomialGen` in the parent ring.
            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            An integer representing the order of ``self`` with respect with the differential variable ``gen``

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.order(u)
                2
                sage: f1.order(v)
                0
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.order(u)
                1
                sage: f2.order(v)
                2
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.order(u)
                -1
                sage: f3.order(v)
                10
                sage: R.one().order(u)
                -1
                sage: R.one().order(v)
                -1
        '''
        gens = self.parent().gens()
        if(gen is None and len(gens) == 1):
            index = 0
        elif(gen is None):
            raise TypeError("The variable has to be provided")
        else:
            index = gens.index(gen)

        return self.orders(operation)[index]

    @cached_method
    def lorders(self, operation: int = -1) -> tuple[int]:
        r'''
            Method that gets the order of a polynomial in all its variables.

            This method computes the lowest appearing order of a concrete polynomial in all the 
            variables that appear in its parent. This method relies on the method 
            :func:`~dalgebra.rwo_polynomial.rwo_polynomial_ring.RWOPolynomialRing_dense.gens`
            and the method :func:`~RWOPolynomialGen.index`.

            INPUT:

            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            A tuple of integers where the index `i` is the lowest order of ``self`` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates that variable does not show up in the polynomial..

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.lorders()
                (0, 0)
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.lorders()
                (1, 1)
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.lorders()
                (-1, 0)
                sage: R.one().lorders()
                (-1, -1)
        '''
        var = self.variables() # we get all variables
        gens = self.parent().gens() # we get the generators of the parent

        indices = [[g.index(el) for el in var if el in g] for g in gens]

        if self.parent().noperators() > 1:
            if operation == -1: # we need to add up each tuple
                indices = [[sum(index) for index in lst] for lst in indices]
            else:
                indices = [[index[operation] for index in lst] for lst in indices]

        return tuple([min(lst, default = -1) for lst in indices])

    @cached_method
    def lorder(self, gen : RWOPolynomialGen = None, operation: int = -1) -> int:
        r'''
            Method to obtain the minimal order of a polynomial w.r.t. a variable

            This method computes the minimal order of a polynomial with respect to 
            a particular variable. Such variable has to be provided as a generator of 
            the ring of polynomials (see :class:`RWOPolynomialGen`).

            This method uses the method :func:`lorders` as a basic definition of these orders.

            In the case the polynomial only has one variable, the input ``gen``
            may be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`RWOPolynomialGen` in the parent ring.
            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            OUTPUT:

            An integer representing the minimal order appearing in ``self`` with respect with the variable ``gen``
            or `-1` if the variable does not appear.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x =  R.base().gens()[0]
                sage: f1 = x*u[0] + x^2*u[2] - (1-x)*v[0]
                sage: f1.lorder(u)
                0
                sage: f1.lorder(v)
                0
                sage: f2 = v[1] - v[2] + u[1]
                sage: f2.lorder(u)
                1
                sage: f2.lorder(v)
                1
                sage: f3 = (x^3-x^2+1)*v[0] - (x^2 + 1)*v[10]
                sage: f3.lorder(u)
                -1
                sage: f3.lorder(v)
                0
                sage: R.one().lorder(u)
                -1
                sage: R.one().lorder(v)
                -1
        '''
        gens = self.parent().gens()
        if(gen is None and len(gens) == 1):
            index = 0
        elif(gen is None):
            raise TypeError("A differential variable has to be provided")
        else:
            index = gens.index(gen)

        return self.lorders(operation)[index]

    @cached_method
    def initial(self, gen : RWOPolynomialGen = None, operation: int = -1) -> RWOPolynomial:
        r'''
            Computes the leading polynomial of an infinite polynomial.

            This method computes the leading term of the infinite polynomial
            when the generator given in ``gen`` is consider the *most important* 
            variable of the polynomial and then it is ordered by its order.

            INPUT:

            * ``gen``: the generator we want to focus. May be omitted when there is only one generator.
            * ``operation``: index of the operator we want to check. If `-1` is given, then the combined
              order of all operators is returned (only useful when having several operators).

            TODO add tests
        '''
        parent = self.parent()

        if parent.ngens() == 1 or gen is None: gen = parent.gens()[0]

        if (not isinstance(gen, RWOPolynomialGen)) or (not gen in parent.gens()):
            raise TypeError(f"The generator must be a valid generator from {parent}")
        
        o = self.order(gen, operation)
        monomials = [parent()(mon) for mon in self.monomials()]
        coefficients = self.coefficients()

        return parent(sum(coeff*mon for (mon, coeff) in zip(monomials, coefficients) if mon.order(gen,operation) == o))

    lc = initial #: alias for initial (also called "leading coefficient")

    #######################################################################################
    ### Properties methods (is_...)
    #######################################################################################
    def is_linear(self, variables : RWOPolynomialGen | Collection[RWOPolynomialGen]=None) -> bool:
        r'''
            Method that checks whether a infinite polynomial is linear (in terms of degree).

            This method checks whether an infinite polynomial is lienar or not w.r.t. the provided
            variables. If ``None`` is given, then we will consider all variables.

            INPUT:

            * ``variables``: (``None`` by default) variable or list of variables (see :class:`RWOPolynomialGen`)
              for which we will consider if the polynomial is linear or not.

            OUTPUT:

            ``True`` if all the appearances of the variables in ``variables`` are linear.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<a,b> = DifferentialPolynomialRing(QQ[x]); x = R('x')
                sage: p = x^2*a[1]*b[0] - a[0]*b[1]^2
                sage: p.is_linear()
                False
                sage: p.is_linear(a)
                True
                sage: p.is_linear(b)
                False
                sage: p.is_linear([a])
                True

            If we provide several variables, then they have to be linear all together::

                sage: S.<u,v,w> = DifferencePolynomialRing(QQ['n']); n = S('n')
                sage: p = n*(n+1)*u[1]*w[0] - 3*n*v[1]*w[1] + 6*n^3*u[0]*w[2] - v[0]
                sage: p.is_linear()
                False
                sage: p.is_linear(u)
                True
                sage: p.is_linear(v)
                True
                sage: p.is_linear(w)
                True
                sage: p.is_linear([u,v])
                True
                sage: p.is_linear([u,w])
                False
                sage: p.is_linear([v,w])
                False
        '''    
        if variables is None:
            variables = self.parent().gens()
        elif (not isinstance(variables, (list,tuple))):
            variables = [variables]

        if any(not el in self.parent().gens() for el in variables):
            raise TypeError(f"The variables must be generators of {self.parent()}")
        elif len(variables) == self.parent().ngens() or len(variables) == 0:
            return self.degree() <= 1
        
        ## This is the generic case when some variable appears in ``variables``
        return all(
            sum(
                t.degree(v) 
                for v in t.variables() 
                if any(v in var for var in variables)
            ) <= 1 
        for t in self.monomials())

    # Magic methods
    def __call__(self, *args, **kwargs) -> RWOPolynomial:
        r'''
            Override of the __call__ method. 

            Evaluating an operator polynomial has a different meaning than evaluating a polynomial
            with infinitely many variables (see method :func:`~dalgebra.rwo_polynomial.rwo_polynomial_ring.RWOPolynomialRing_dense.eval`
            for further information)

            INPUT:

            * ``args`` and ``kwargs`` with the same format as in 
              :func:`~dalgebra.rwo_polynomial.rwo_polynomial_ring.RWOPolynomialRing_dense.eval`

            OUTPUT:

            The evaluated object as in :func:`~dalgebra.rwo_polynomial.rwo_polynomial_ring.RWOPolynomialRing_dense.eval`.

            EXAMPLES::

                sage: from dalgebra import DifferentialPolynomialRing 
                sage: R.<y> = DifferentialPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: y[1](0)
                0
                sage: (y[0] + y[1])(x)
                x + 1
                sage: (y[0] + y[1])(y=x)
                x + 1

            In the case of a differential polynomial, this method commutes with the use of :func:`derivative`::

                sage: (x^2*y[1]^2 - y[2]*y[1]).derivative()(y=x) == (x^2*y[1]^2 - y[2]*y[1])(y=x).derivative()
                True

            This evaluation also works naturally with several infinite variables::

                sage: S = DifferentialPolynomialRing(R, 'a'); a,y = S.gens()
                sage: (a[1] + y[0]*a[0])(a=x, y=x^2)
                x^3 + 1
                sage: in_eval = (a[1] + y[0]*a[0])(y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of differential polynomials in (a) over Differential Ring [Univariate Polynomial Ring 
                in x over Rational Field] with derivation [Map from callable d/dx]
        '''
        return self.parent().eval(self, *args, **kwargs)

    def divides(self, other : RWOPolynomial) -> bool:
        r'''
            Method that checks whether a polynomial divides ``other``.

            This method relies on the base polynomial structure behind the infinite polynomial ring.
        '''
        other = self.parent()(other)
        return self.polynomial().divides(other.polynomial())

    ###################################################################################
    ### Arithmetic methods
    ###################################################################################
    def _add_(self, x):
        return self.parent().element_class(self.parent(), super()._add_(x))
    def _sub_(self, x):
        return self.parent().element_class(self.parent(), super()._sub_(x))
    def _mul_(self, x):
        return self.parent().element_class(self.parent(), super()._mul_(x))
    def _rmul_(self, x):
        return self.parent().element_class(self.parent(), super()._rmul_(x))
    def _lmul_(self, x):
        return self.parent().element_class(self.parent(), super()._lmul_(x))
    def _mod_(self, x):
        return self.parent().element_class(self.parent(), self.polynomial() % x.polynomial())
    def _truediv_(self, x):
        return self.parent().element_class(self.parent(), self.polynomial() // x.polynomial())
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), super().__pow__(n))

    ###################################################################################
    ### Other magic methods
    ###################################################################################
    def __repr__(self) -> str:
        original = super().__repr__()
        if self.parent().noperators() > 1:
            import re
            sub_match = lambda match : "_" + str(IndexBijection(self.parent().noperators())(int(match.groups()[0]))) + match.groups()[1]
            original = re.sub(r"_(\d+)( |\^|\*|$)", sub_match, original)
        return original
    
    def _latex_(self) -> str:
        original = super()._latex_()
        if self.parent().noperators() > 1:
            import re
            sub_match = lambda match : "_{" + str(IndexBijection(self.parent().noperators())(int(match.groups()[0]))) + "}"
            original = re.sub(r"_{(\d+)}", sub_match, original)
        return original

__all__ = ["IndexBijection"]