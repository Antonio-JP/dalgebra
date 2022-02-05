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

from sage.all import latex, ZZ
from sage.categories.pushout import pushout
from sage.misc.cachefunc import cached_method

from .differential_polynomial_ring import is_DiffPolynomialRing

class DifferentialSystem:
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
        # Building the common parent
        parents = [el.parent() for el in equations]
        if(parent != None):
            parents.insert(0,parent)

        pushed = reduce(lambda p, q : pushout(p,q), parents)
        if(not is_DiffPolynomialRing(pushed)):
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
        
        # caching variables
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

    ## magic methods
    def __getitem__(self, index):
        return DifferentialSystem(self.equations[index], self.parent(), self.variables)

    def __repr__(self):
        return "Differential system over [%s] with variables [%s]:\n{\n\t" %(self.parent(), self.variables) + "\n\t".join(["%s == 0" %el for el in self.equations]) + "\n}"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        result = r"\text{Differential system over }" + latex(self.parent()) + r" \text{ with variables }" + ", ".join(latex(el) for el in self.variables) + ":\n\n"
        result += r"\left\{\begin{array}{ll}"
        result += "\n".join(latex(el) + r" & = 0 \\" for el in self.equations)
        result += "\n" + r"\end{array}\right."
        return result

    ## SP properties
    def build_sp1(self, Ls):
        r'''
            Method that build an extended system that satisfies SP1.

            The condition SP1 is defined in the paper :doi:`10.1016/j.laa.2013.01.016` (Section 3) in regard with a 
            system of differential polynomial: let `\mathcal{P} = \{f_1,\ldots,f_m\}`. We say that an extended set of 
            differential polynomials `SP \subset \partial(\mathcal{P})` is SP1 for some `L_1,\ldots,L_m \in \mathbb{N}` if it can be written as:

            .. MATH::

                PS = \left\{\partial^{k}(f_i) \mid k \in \{0,\ldots,L_i\}, i=1,\ldots,m\right\}

            This method provides a way to build an extended differential system from ``self`` that satisfies condition SP1 for 
            a fixed set of values of `L_1,\ldots,L_m`.

            INPUT:

            * `Ls`: list or tuple of non-negative integers of length ``self.size()``.

            OUTPUT:

            Another differential system extending ``self`` by derivation that satisfies SP1 for the given list of `L_i`.

            EXAMPLES::

                sage: from dalgebra import *
                sage: R.<u> = DiffPolynomialRing(QQ)
                sage: system = DifferentialSystem([u[1]-u[0]])
                sage: system.build_sp1([0]).equations
                (u_1 - u_0,)
                sage: system.build_sp1([1]).equations
                (u_1 - u_0, u_2 - u_1)
                sage: system.build_sp1([5]).equations
                (u_1 - u_0, u_2 - u_1, u_3 - u_2, u_4 - u_3, u_5 - u_4, u_6 - u_5)
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x = R.base().gens()[0]
                sage: system = DifferentialSystem([x*u[0] + x^2*u[2] - (1-x)*v[0], v[1] - v[2] + u[1]], variables = [u])
                sage: system.build_sp1([0,0]).equations
                (x^2*u_2 + x*u_0 + (x - 1)*v_0, u_1 - v_2 + v_1)
                sage: system.build_sp1([1,0]).equations
                (x^2*u_2 + x*u_0 + (x - 1)*v_0,
                x^2*u_3 + 2*x*u_2 + x*u_1 + u_0 + (x - 1)*v_1 + v_0,
                u_1 - v_2 + v_1)
                sage: system.build_sp1([1,1]).equations
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
            new_equations = sum([[self.equations[i].derivative(times=k) for k in range(Ls[i]+1)] for i in range(self.size())], [])
            self.__CACHED_SP1[Ls] = DifferentialSystem(new_equations, self.parent(), self.variables)

        return self.__CACHED_SP1[Ls]

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
                sage: R.<u> = DiffPolynomialRing(QQ)
                sage: system = DifferentialSystem([u[1]-u[0]])
                sage: system.algebraic_variables()
                (u_0, u_1)
                sage: R.<u,v> = DiffPolynomialRing(QQ[x]); x = R.base().gens()[0]
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


    def is_sp2(self):
        r'''
            Method that checks the condition SP2.

            The condition SP2 is defined in the paper :doi:`10.1016/j.laa.2013.01.016` (Section 3) in regard with a 
            system of differential polynomial: let `\mathcal{P} = \{f_1,\ldots,f_m\}` be a system of differentially algebraic equations
            in the differential variables `\mathcal{U} = \{u_1,\ldots, u_n}`. We say that the system satisfies the condition SP2
            if and only if the number of *algebraic* variables in the polynomials is exactly the number of polynomials minus 1.

            It is interesting to remark that the algebraic variables of a differential polynomial are the total amount of
            variables that appears in it before the differential relation. Namely, the result of method 
            :func:`~dalgebra.differentialpolynomial.differential_polynomial_element.DiffPolynomial.variables`
            provides the algebraic variables for a differential polynomial.
        '''
        return len(self.algebraic_variables()) == self.size() - 1





