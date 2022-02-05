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

from sage.misc.cachefunc import cached_method
from sage.rings.polynomial.infinite_polynomial_ring import InfinitePolynomialGen
from sage.rings.polynomial.infinite_polynomial_element import InfinitePolynomial_dense, InfinitePolynomial_sparse

def is_InfinitePolynomial(element):
    r'''
        Method to decide whether or not an element is a polynomial with infinite variables.

        This is a call to ``isinstance`` with the two main element classes of Infinite Polynomial
        Rings.
    '''
    return (isinstance(element, InfinitePolynomial_dense) or isinstance(element, InfinitePolynomial_sparse))

class DiffPolynomialGen (InfinitePolynomialGen):
    r'''
        Class for generators of :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense`.

        A generator of a :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense` is 
        an object that can create the infinitely many variables associated with a particular name. The variables it generates
        are of the form ``name_x`` where ``x`` is the index.

        In the case of a ring of differential polynomials, ``name_x`` represents the x-th derivative of the variable with 
        given name. 

        To allow more flexibility, this class provides methods to know if an object can be generated with this
        generator and to obtain the corresponding index.

        INPUT:

        * ``parent``: a :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense` 
          where ``self`` will generate its elements.
        * ``name``: main part of the name for the generated variales.
    '''
    def __init__(self, parent, name):
        from .differential_polynomial_ring import is_DiffPolynomialRing
        if(not is_DiffPolynomialRing(parent)):
            raise TypeError("The DiffPolynomialGen must have a ring of differential polynomial as parent")
        super().__init__(parent, name)

    def __getitem__(self, i):
        return self._parent(super().__getitem__(i))

    def contains(self, element):
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
        name = str(element)
        spl = name.split("_")
        first = "_".join(spl[:-1])
        return first == self._name

    def __contains__(self, other):
        return self.contains(other)

    def index(self, element):
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
            el = int(str(element).split("_")[-1])
            if(el < 0):
                raise ValueError("negative index is not valid")
            return el

    def __hash__(self):
        return hash(self._name)

class DiffPolynomial (InfinitePolynomial_dense):
    r'''
        Class for representing differential polynomials.

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

        This object of this class represents the polynomials of a ring of differential polynomials. They 
        are a natural extension of the class :class:`~sage.rings.polynomial.infinite_polynomial_element.InfinitePolynomial_dense`
        including some extra functionality more specific of differential polynomials (such as the derivation and the evaluation).

        INPUT:

        * ``parent``: a :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense` 
          where the new element will be contained.
        * ``polynomial``: a valid polynomial to be casted into an element of ``parent``.

        We recommend not to use this constructor, but instead build the polynomials using the generators of the 
        corresponding :class:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense`.
    '''
    def __init__(self, parent, polynomial):
        if(is_InfinitePolynomial(polynomial)):
            polynomial = polynomial.polynomial()
        super().__init__(parent, polynomial)
        
    # Properties methods
    @cached_method
    def orders(self):
        r'''
            Method that gets the order of a differential polynomial in all its variables.

            This method computes the order of a concrete differential polynomial in all the differential 
            variables that appear in its parent. This method relies on the method 
            :func:`~dalgebra.differential_polynomial.differential_polynomial_ring.DifferentialPolynomialRing_dense.gens`
            and the method :func:`~DiffPolynomialGen.index`.

            OUTPUT:

            A tuple of integers where the index `i` is the order of ``self` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates thatvariable does not show up in the polynomial.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x = R.base().gens()[0]
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

        return tuple([max([g.index(el) for el in var if el in g], default=-1) for g in gens])

    @cached_method
    def order(self, gen=None):
        r'''
            Method to obtain the order of a differential polynomial w.r.t. a variable

            This method computes the order of a differential polynomial with respect to 
            a particular variable. Such variables has to be provided as a generator of 
            the ring of differential polynomials (see :class:`DiffPolynomialGen`).

            This method uses the method :func:`orders` as a basic definition of these orders.

            In the case te differential polynomial only has one differential variable, the input ``gen``
            can be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`DiffPolynomialGen` in the parent ring.

            OUTPUT:

            An integer representing the order of ``self`` with respect with the differential variable ``gen``

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x =  R.base().gens()[0]
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
            raise TypeError("A differential variable has to be provided")
        else:
            index = gens.index(gen)

        return self.orders()[index]

    @cached_method
    def lorders(self):
        r'''
            Method that gets the order of a differential polynomial in all its variables.

            This method computes the order of a concrete differential polynomial in all the differential 
            variables that appear in its parent. This method relies on the method 
            :func:`~dalgebra.differential_polynomial.differential_polynomial_ring.DifferentialPolynomialRing_dense.gens`
            and the method :func:`~DiffPolynomialGen.index`.

            OUTPUT:

            A tuple of integers where the index `i` is the order of ``self` with respect to the `i`-th variable
            of ``self.parent()``. The value `-1` indicates thatvariable does not show up in the polynomial.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x =  R.base().gens()[0]
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

        return tuple([min([g.index(el) for el in var if el in g], default=-1) for g in gens])

    @cached_method
    def lorder(self, gen=None):
        r'''
            Method to obtain the minimal order of a differential polynomial w.r.t. a variable

            This method computes the minimal order of a differential polynomial with respect to 
            a particular variable. Such variables has to be provided as a generator of 
            the ring of differential polynomials (see :class:`DiffPolynomialGen`).

            This method uses the method :func:`lorders` as a basic definition of these orders.

            In the case te differential polynomial only has one differential variable, the input ``gen``
            can be not given and the only variable will be used instead.

            INPUT:

            * ``gen``: a :class:`DiffPolynomialGen` in the parent ring.

            OUTPUT:

            An integer representing the minimal order appearing in ``self`` with respect with the differential variable ``gen``
            or `-1` if the variable does not appear.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x =  R.base().gens()[0]
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

        return self.lorders()[index]

    # Magic methods
    def __call__(self, *args, **kwargs):
        r'''
            Override of the __call__ method. 

            Evaluating a differential polynomial has a different meaning than evaluating a polynomial
            with infinitely many variables (see method 
            :func:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense.eval`
            for further information)

            INPUT:

            * ``args`` and ``kwargs`` with the same format as in 
              :func:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense.eval`

            OUTPUT:

            The evaluate object as in :func:`~dalgebra.differential_polynomial.differential_polynomial_ring.DiffPolynomialRing_dense.eval`.

            EXAMPLES::

            sage: from dalgebra import DiffPolynomialRing 
                sage: R.<y> = DiffPolynomialRing(QQ['x']); x = R.base().gens()[0]
                sage: y[1](0)
                0
                sage: (y[0] + y[1])(x)
                x + 1
                sage: (y[0] + y[1])(y=x)
                x + 1

            This method commutes with the use of :func:`derivation`::

                sage: (x^2*y[1]^2 - y[2]*y[1]).derivative()(y=x) == (x^2*y[1]^2 - y[2]*y[1])(y=x).derivative()
                True

            This evaluation also works naturally with several infinite variables::

                sage: S = DiffPolynomialRing(R, 'a'); a,y = S.gens()
                sage: (a[1] + y[0]*a[0])(a=x, y=x^2)
                x^3 + 1
                sage: in_eval = (a[1] + y[0]*a[0])(y=x); in_eval
                a_1 + x*a_0
                sage: parent(in_eval)
                Ring of differential polynomials in (a) over [Univariate Polynomial Ring in x over Rational Field]
        '''
        return self.parent().eval(self, *args, **kwargs)

    def divides(self, other):
        r'''
            Method that checks whether a differential polynomial divides ``other``.

            This method relies on the base polynomial structure behind the infinite polynomial ring.
        '''
        other = self.parent()(other)
        return self.polynomial().divides(other.polynomial())

    # Arithmetic methods
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
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), super().__pow__(n))

    def _derivative(self, *_):
        r'''
            Overridden method to implement properly the derivation in Fraction Field

            This method simply calls the method :func:`derivative`. See its documentation
            for further information on the input, output and examples.
        '''
        return self.parent().derivation(self)
