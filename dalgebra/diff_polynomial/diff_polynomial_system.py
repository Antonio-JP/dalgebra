r"""
File for the structures concerning differential systems

This file contains the structures and main algorithms to manipulate
and study the solutions of differential systems expressed in terms of 
differential polynomials.

AUTHORS:

    - Antonio Jimenez-Pastor (2022-02-04): initial version

"""

# ****************************************************************************
#  Copyright (C) 2022 Antonio Jimenez-Pastor <jimenezpastor@lix.polytechnique.fr>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from functools import reduce

from sage.all import latex, ZZ, PolynomialRing, cartesian_product
from sage.categories.pushout import pushout
from sage.misc.cachefunc import cached_method #pylint: disable=no-name-in-module

from .diff_polynomial_ring import is_DifferencePolynomialRing, is_DifferentialPolynomialRing, is_RWOPolynomialRing

class RWOSystem:
    r'''
        Class for representing a system over a ring with an operator.

        This class allows the user to represent a system of equations 
        over a ring with an operator (see :class:`~dalgebra.ring_w_operator.ring_w_operator.RingsWithOperator`)
        as a list of infinite polynomials in one or several variables.

        This class will offer a set of methods and properties to extract the main
        information of the system and also the main algorithms and methods
        to study or manipulate these systems such as elimination procedures, etc.

        INPUT:

        * ``equations``: list or tuple of polynomials (see :class:`~dalgebra.diff_polynomial.diff_polynomial_element.RWOPolynomial`). 
          The system will be the one defined by `eq = 0` for all `eq` in the input ``equations``.
        * ``parent``: the common parent to transform the input. The final parent of all
          the elements will a common structure (if possible) that will be the 
          pushout of all the parents of ``elements`` and this structure.
        * ``variables``: list of names or infinite variables that will fix 
          the variables of the system. If it is not given, we will consider all the 
          differential variables as main variables.
    '''
    def __init__(self, equations, parent=None, variables=None):
        # Building the common parent
        parents = [el.parent() for el in equations]
        if(parent != None):
            parents.insert(0,parent)

        pushed = reduce(lambda p, q : pushout(p,q), parents)
        if(not is_RWOPolynomialRing(pushed)):
            raise TypeError("The common parent is nto a ring of differential polynomials. Not valid for a DifferentialSystem")

        self.__parent = pushed
        # Building the equations
        self.__equations = tuple([pushed(el) for el in equations])
        
        # Checking the argument `variables`
        if(variables != None):
            str_vars = [str(v) for v in variables]
            gens = [str(g) for g in self.parent().gens()]
            dvars = []
            for var in str_vars:
                if(not var in gens):
                    raise ValueError("The variable %s is not valid for a system in [%s]" %(var, self.parent()))
                dvars.append(self.parent().gens()[gens.index(var)])
        else:
            dvars = self.parent().gens()
        
        # setting up the differential variables
        self.__variables = tuple(dvars)
        self.__parameters = tuple([el for el in self.parent().gens() if (not el in dvars)])

        # cached variables
        self.__CACHED_SP1 = {}

    ## Getters for some properties
    @property
    def equations(self): return self.__equations
    @property
    def variables(self): return self.__variables
    @property
    def parameters(self): return self.__parameters

    def parent(self):
        return self.__parent

    def size(self):
        return len(self.equations)

    @cached_method
    def is_DifferentialSystem(self):
        return is_DifferentialPolynomialRing(self.parent())
    @cached_method
    def is_DifferenceSystem(self):
        return is_DifferencePolynomialRing(self.parent())

    ## magic methods
    def __getitem__(self, index):
        return self.__class__(self.equations[index], self.parent(), self.variables)

    def __repr__(self):
        return "System over [%s] with variables [%s]:\n{\n\t" %(self.parent(), self.variables) + "\n\t".join(["%s == 0" %el for el in self.equations]) + "\n}"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        result = r"\text{System over }" + latex(self.parent()) + r" \text{ with variables }" + ", ".join(latex(el) for el in self.variables) + ":\n\n"
        result += r"\left\{\begin{array}{ll}"
        result += "\n".join(latex(el) + r" & = 0 \\" for el in self.equations)
        result += "\n" + r"\end{array}\right."
        return result

    ## to algebraic methods
    @cached_method
    def algebraic_variables(self):
        r'''
            Method to retrieve the algebraic variables in the system.

            This method computes the number of algebraic variables that appear on the system. This means,
            gethering each appearance of the differential variables and filter them by the variables of the system.

            OUTPUT:

            A tuple containing the algebraic variables appearing in the system (as differential polynomials)

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u> = DifferentialPolynomialRing(QQ)
                sage: system = DifferentialSystem([u[1]-u[0]])
                sage: system.algebraic_variables()
                (u_0, u_1)
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]])
                sage: system.algebraic_variables()
                (v_0, v_1, v_2, u_0, u_1, u_2)
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]], variables = [u])
                sage: system.algebraic_variables()
                (u_0, u_1, u_2)
        '''
        all_vars = list(set(sum([[self.parent()(v) for v in equ.variables()] for equ in self.equations], [])))
        filtered = [el for el in all_vars if any(el in g for g in self.variables)]
        filtered.sort()
        return tuple(filtered)

    @cached_method
    def algebraic_equations(self):
        r'''
            Method to get the equivalent algebraic equations.

            Considering a differential polynomial algebraically means to sepparate semantically
            the relation of different derivatives of a differential variable. This is mainly useful 
            once all differential operations are completed.

            OUTPUT:

            A tuple of polynomials in a common parent that represent the equations of ``self`` 
            in a purely algebraic context.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u> = DifferentialPolynomialRing(QQ)
                sage: system = DifferentialSystem([u[1]-u[0]])
                sage: system.algebraic_equations()
                (-u_0 + u_1,)
                sage: system.extend_by_operation([1]).algebraic_equations()
                (-u_0 + u_1, -u_1 + u_2)
                
            We can check that the parent of all the equations is the same::

                sage: parents = [el.parent() for el in system.extend_by_operation([1]).algebraic_equations()]
                sage: all(el == parents[0] for el in parents[1:])
                True
                sage: parents[0]
                Multivariate Polynomial Ring in u_0, u_1, u_2 over Differential 
                Ring [Rational Field] with derivation [Map from callable 0]

            The same can be checked for a multivariate differential polynomial::

                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]])
                sage: system.algebraic_equations()
                ((x - 1)*v_0 + x*u_0 + x^2*u_2, v_1 - v_2 + u_1)
                sage: system.extend_by_operation([1,2]).algebraic_equations()
                ((x - 1)*v_0 + x*u_0 + x^2*u_2,
                v_0 + (x - 1)*v_1 + u_0 + x*u_1 + 2*x*u_2 + x^2*u_3,
                v_1 - v_2 + u_1,
                v_2 - v_3 + u_2,
                v_3 - v_4 + u_3)
                
            And the parents are again the same for all those equations::

                sage: parents = [el.parent() for el in system.extend_by_operation([1,2]).algebraic_equations()]
                sage: all(el == parents[0] for el in parents[1:])
                True
                sage: parents[0]
                Multivariate Polynomial Ring in v_0, v_1, v_2, v_3, v_4, u_0, u_1, u_2, u_3 over 
                Differential Ring [Univariate Polynomial Ring in x over Rational Field] with 
                derivation [Map from callable d/dx]

            The output of this method depends actively in the set of active variables that defines the system::

                sage: system_with_u = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]], variables=[u])
                sage: system_with_u.algebraic_equations()                                                                                                                                        
                (x*u_0 + x^2*u_2 + (x - 1)*v_0, u_1 + v_1 - v_2)
                sage: system_with_u.extend_by_operation([1,2]).algebraic_equations()
                (x*u_0 + x^2*u_2 + (x - 1)*v_0,
                u_0 + x*u_1 + 2*x*u_2 + x^2*u_3 + v_0 + (x - 1)*v_1,
                u_1 + v_1 - v_2,
                u_2 + v_2 - v_3,
                u_3 + v_3 - v_4)

            In this case, the parent prioritize the variables related with `u_*`::

                sage: system_with_u.algebraic_equations()[0].parent()
                Multivariate Polynomial Ring in u_0, u_1, u_2 over Multivariate Polynomial 
                Ring in v_0, v_1, v_2 over Differential Ring [Univariate Polynomial Ring 
                in x over Rational Field] with derivation [Map from callable d/dx]
                sage: parents = [el.parent() for el in system_with_u.extend_by_operation([1,2]).algebraic_equations()]
                sage: all(el == parents[0] for el in parents[1:])
                True
                sage: parents[0]
                Multivariate Polynomial Ring in u_0, u_1, u_2, u_3 over Multivariate Polynomial 
                Ring in v_0, v_1, v_2, v_3, v_4 over Differential Ring [Univariate Polynomial 
                Ring in x over Rational Field] with derivation [Map from callable d/dx]

        '''
        equations = [el.polynomial() for el in self.equations]
        ## Usual pushout leads to a CoercionException due to management of variables
        ## We do the pushout by ourselves by looking into the generators and creating the best 
        ## possible polynomial ring with the maximal possible derivatives
        max_orders = reduce(lambda p, q : [max(p[i],q[i]) for i in range(len(p))], [equ.orders() for equ in self.equations])
        base_ring = self.parent().base()
        gens = self.parent().gens()
        variables = []
        parameters = []
        subs_dict = {}
        for i in range(len(gens)):
            if(gens[i] in self.variables):
                for j in range(max_orders[i]+1):
                    variables.append(gens[i][j])
                    subs_dict[str(gens[i][j])] = gens[i][j]
            else:
                for j in range(max_orders[i]+1):
                    parameters.append(gens[i][j])
                    subs_dict[str(gens[i][j])] = gens[i][j]
        variables.sort(); parameters.sort()
        

        inner_ring = base_ring if len(parameters) == 0 else PolynomialRing(base_ring, parameters)
        
        final_parent = PolynomialRing(inner_ring, variables)
        try:
            return tuple([final_parent(el(**subs_dict)) for el in equations])
        except TypeError:
            return tuple([final_parent(str(el)) for el in equations])

    ## SP properties
    def extend_by_operation(self, Ls):
        r'''
            Method that build an extended system that satisfies SP1.

            The condition SP1 is defined in the paper :doi:`10.1016/j.laa.2013.01.016` (Section 3) in regard with a 
            system of differential polynomial: let `\mathcal{P} = \{f_1,\ldots,f_m\}`. We say that an extended set of 
            differential polynomials `SP \subset \partial(\mathcal{P})` is SP1 for some `L_1,\ldots,L_m \in \mathbb{N}` if it can be written as:

            .. MATH::

                PS = \left\{\partial^{k}(f_i) \mid k \in \{0,\ldots,L_i\}, i=1,\ldots,m\right\}

            This method provides a way to build an extended system from ``self`` using the operator of the base ring 
            that satisfies condition SP1 for a fixed set of values of `L_1,\ldots,L_m`.

            INPUT:

            * `Ls`: list or tuple of non-negative integers of length ``self.size()``.

            OUTPUT:

            Another :class:`RWOSystem` extending ``self`` with the operation in the base ring that satisfies 
            SP1 for the given list of `L_i`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u> = DifferentialPolynomialRing(QQ)
                sage: system = DifferentialSystem([u[1]-u[0]])
                sage: system.extend_by_operation([0]).equations
                (u_1 - u_0,)
                sage: system.extend_by_operation([1]).equations
                (u_1 - u_0, u_2 - u_1)
                sage: system.extend_by_operation([5]).equations
                (u_1 - u_0, u_2 - u_1, u_3 - u_2, u_4 - u_3, u_5 - u_4, u_6 - u_5)
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]], variables = [u])
                sage: system.extend_by_operation([0,0]).equations
                (x^2*u_2 + x*u_0 + (x - 1)*v_0, u_1 - v_2 + v_1)
                sage: system.extend_by_operation([1,0]).equations
                (x^2*u_2 + x*u_0 + (x - 1)*v_0,
                x^2*u_3 + 2*x*u_2 + x*u_1 + u_0 + (x - 1)*v_1 + v_0,
                u_1 - v_2 + v_1)
                sage: system.extend_by_operation([1,1]).equations
                (x^2*u_2 + x*u_0 + (x - 1)*v_0,
                x^2*u_3 + 2*x*u_2 + x*u_1 + u_0 + (x - 1)*v_1 + v_0,
                u_1 - v_2 + v_1,
                u_2 - v_3 + v_2)
        '''
        # Checking the input of L
        if(not isinstance(Ls, (list, tuple))):
            raise TypeError("The argument must be a list or tuple")
        if(any(not el in ZZ or el < 0 for el in Ls)):
            raise ValueError("The argument must be a list or tuple of non-negative integers")
        
        Ls = tuple(Ls)
        if(not Ls in self.__CACHED_SP1):
            new_equations = sum([[self.equations[i].operation(times=k) for k in range(Ls[i]+1)] for i in range(self.size())], [])
            self.__CACHED_SP1[Ls] = self.__class__(new_equations, self.parent(), self.variables)

        return self.__CACHED_SP1[Ls]

    build_sp1 = extend_by_operation #: alias for method :func:`extend_by_operation`
    
    @cached_method
    def is_homogeneous(self):
        r'''
            This method checks whether the system is homogeneous in the indicated variables.

            This method relies on the method :func:`algebraic_equations` and the method :func:`is_homogeneous`
            from the polynomial class in Sage.
        '''
        return all(equ.is_homogeneous() for equ in self.algebraic_equations())

    def is_sp2(self):
        r'''
            Method that checks the condition SP2.

            The condition SP2 is defined in the paper :doi:`10.1016/j.laa.2013.01.016` (Section 3) in regard with a 
            system of differential polynomial: let `\mathcal{P} = \{f_1,\ldots,f_m\}` be a system of differentially algebraic equations
            in the differential variables `\mathcal{U} = \{u_1,\ldots, u_n}`. We say that the system satisfies the condition SP2
            if and only if the number of variables is valid to compute a resultant algebraically.

            This quantity changing depending on whether the equations are homogeneous (same number of variables and equations)
            or not (one more equations than variables).

            It is interesting to remark that the algebraic variables of a differential polynomial are the total amount of
            variables that appears in it before the differential relation. Namely, the result of method 
            :func:`~dalgebra.diff_polynomial.diff_polynomial_element.RWOPolynomial.variables`
            provides the algebraic variables for a differential polynomial.

            OUTPUT:

            ``True`` if the system satisfies the condition SP2, ``False`` otherwise.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u,v> = DifferentialPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]], variables = [u])
                sage: system.is_sp2()
                False
                sage: system.extend_by_operation([1,2]).is_sp2()
                True

            WARNING: for this method it is crucial to know that the result depends directly on the set variables for 
            the system. Namely, having different set of active variables change the output of this method for *the same* 
            differential system::

                sage: same_system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]])
                sage: system.is_sp2()
                False
                sage: system.extend_by_operation([1,2]).is_sp2()
                True
        '''
        if(self.is_homogeneous()):
            return len(self.algebraic_variables()) == self.size()
        return len(self.algebraic_variables()) == self.size() - 1

    ## resultant methods
    def diff_resultant(self, bound_L = 10, alg_res = "dixon"):
        r'''
            Method to compute the operator resultant of this system.

            TODO: add explanation of resultant.

            INPUT:

            * ``bound_L``: bound for the values of ``Ls`` for method :func:`extend_by_operation`.
            * ``alg_res``: method to compute the algebraic resultant once we extended a 
              system to a valid system (see :func:`is_sp2`). The valid values are, currently,
              ``"dixon"`` and ``"macaulay"``.

            OUTPUT:

            The resultant for this system.

            TODO: add examples
        '''
        ## Checking arguments
        if(not bound_L in ZZ or bound_L < 0):
            raise ValueError("The bound for the L argument must be a non-negative integer")
        if(not alg_res in ("dixon", "macaulay")):
            raise ValueError("The algorithm for the algebraic resultant must be 'dixon' or 'macaulay'")

        ## Extending the system
        L = None
        for _aux_L in cartesian_product(len(self.equations)*[range(bound_L+1)]):
            if(self.extend_by_operation(tuple(_aux_L)).is_sp2()):
                L = tuple(_aux_L)
                break
        
        if(L is None):
            raise TypeError("The system was not nicely extended with bound %d" %bound_L)

        ## Computing the resultant
        if(alg_res == "dixon"):
            raise NotImplementedError("Dixon's resultant not yet implemented")
        elif(alg_res == "macaulay"):
            equs = [el.homogenize() for el in self.extend_by_operation(L).algebraic_equations()]
            ring = equs[0].parent()
            return ring.macaulay_resultant(equs)

class DifferentialSystem (RWOSystem):
    r'''
        Class representing a differential system.

        This class allows the user to represent a system of differential equations 
        as a list of differential polynomials in one or several variables.

        This class will offer a set of methods and properties to extract the main
        information of the differential system and also the main algorithms and methods
        to study or manipulate these systems.

        INPUT:

        * ``equations``: list or tuple of differential polynomials. The system will
          be the one defined by `eq = 0` for all `eq` in the input ``equations``.
        * ``parent``: the common parent to transform the input. The final parent of all
          the elements will a common structure (if possible) that will be the 
          pushout of all the parents of ``elements`` and this structure.
        * ``variables``: list of names or differential variables that will fix 
          the variables of the system. If it is not given, we will consider all the 
          differential variables as main variables.
    '''
    def __init__(self, equations, parent=None, variables=None):
        super().__init__(equations, parent, variables)

        if not is_DifferentialPolynomialRing(self.parent()):
            raise TypeError("The common parent is nto a ring of differential polynomials. Not valid for a DifferentialSystem")

    extend_by_derivation = RWOSystem.extend_by_operation #: new alias for :func:`extend_by_operation`

class DifferenceSystem (RWOSystem):
    r'''
        Class representing a difference system.

        This class allows the user to represent a system of difference equations 
        as a list of difference polynomials in one or several variables.

        This class will offer a set of methods and properties to extract the main
        information of the difference system and also the main algorithms and methods
        to study or manipulate these systems.

        INPUT:

        * ``equations``: list or tuple of difference polynomials. The system will
          be the one defined by `eq = 0` for all `eq` in the input ``equations``.
        * ``parent``: the common parent to transform the input. The final parent of all
          the elements will a common structure (if possible) that will be the 
          pushout of all the parents of ``elements`` and this structure.
        * ``variables``: list of names or difference variables that will fix 
          the variables of the system. If it is not given, we will consider all the 
          difference variables as main variables.
    '''
    def __init__(self, equations, parent=None, variables=None):
        super().__init__(equations, parent, variables)

        if not is_DifferencePolynomialRing(self.parent()):
            raise TypeError("The common parent is nto a ring of difference polynomials. Not valid for a DifferenceSystem")

    extend_by_difference = RWOSystem.extend_by_operation #: new alias for :func:`extend_by_operation`

__all__ = ["DifferentialSystem", "DifferenceSystem"]