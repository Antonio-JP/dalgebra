r'''
    Analysis of algebraic ideals.

    This module contains some additional functionality to study the algebraic ideals generated in the computations
    of the module :mod:`dalgebra.commutators`.

    This software has been used in the presentation in ISSAC'23 "Computing almost-commuting basis of Ordinary Differential
    Operators", by A. Jiménez-Pastor, S.L. Rueda and M.A. Zurro in Tromsø, Norway.

    **Things remaining TODO**
    -----------------------------------------

    1. CHECK CHANGES FROM NEW DPOLYNOMIAL FRAMEWORK
    2. Extend this documentation

    **Elements provided by the module**
    -----------------------------------------
'''
# ****************************************************************************
#  Copyright (C) 2025 Antonio Jimenez-Pastor <antonio.jimenezp@upm.es>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

from __future__ import annotations

import logging

logger = logging.getLogger(__name__)

from functools import reduce

from sage.categories.pushout import pushout
from sage.combinat.combination import Combinations
from sage.functions.other import binomial
from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.modules.free_module_element import free_module_element as vector
from sage.parallel.multiprocessing_sage import Pool
from sage.rings.fraction_field import FractionField_generic
from sage.rings.integer_ring import ZZ
from sage.rings.ideal import Ideal_generic as Ideal, Ideal as ideal
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.structure.element import parent

from typing import Any

from ..dring import DifferentialRing, DRings
from ..dpolynomial.dpolynomial import DPolynomial, DPolynomialRing, is_DPolynomialRing
from ..logging.logging import count_calls, cut_string, loglevel


_DRings = DRings.__classcall__(DRings)


#################################################################################################
###
### AUXILIARY STRUCTURES AND CODE TO RUN IN PARALLEL
###
#################################################################################################
__ProcessesPool = None


def LoopInParallel(func, iterable, chunksize=1):
    r'''
        Method that tries to loop a function application in parallel. If no Pool is created, then we simply loop in the usual way.

        ::NO EXAMPLE::
    '''
    if __ProcessesPool is not None:
        logger.debug(f"[LoopInParallel] Starting parallel computation of {len(iterable)} processes in {__ProcessesPool._processes}")
        return __ProcessesPool.starmap(func, iterable, chunksize)
    else:
        return (func(*el) for el in iterable)


def StartPool(ncpus: int = None):
    r'''Method to universally starting the pool (::NO EXAMPLE::)'''
    global __ProcessesPool
    if __ProcessesPool is None and ncpus not in (None, 1):
        __ProcessesPool = Pool(ncpus)


#################################################################################################
###
### CLASS FOR STORING SOLUTIONS OF IDEALS
###
#################################################################################################
class SolutionBranch:
    r'''
        Class representing a branch of solutions for an algebraic problem.

        This class essentially works with an independent component of an algebraic variety together with some information about how we got to this component (decisions taken, partial solution, etc.). It is the main output of the method :func:`analyze_ideal` and it is used in the main method :func:`analyze_ideals` to store the different branches of solutions.

        It combines the classical analysis of an algebraic variety with some tweaks about how to properly analyze an ideal and reducing the number of variables as much as possible. It also provides some methods to combine branches, check whether a branch is a subsolution of another, etc.

        ::NO EXAMPLE::

        TODO: Add examples to this documentation.
    '''
    def __init__(self, I: list | Ideal, solution: dict[str,Any], decisions: list[tuple[str,str,Any] | tuple[str,Any]], base_parent=None):
        ##################################################################
        ## Deciding the parent
        ##################################################################
        if base_parent is not None:
            self.__parent = base_parent
        elif isinstance(I, Ideal):
            self.__parent = I.ring()
        elif isinstance(I, (tuple,list)) and len(I) > 0:
            self.__parent = reduce(lambda p,q: pushout(p,q), (parent(el) for el in I), QQ)
        elif isinstance(I, (tuple, list)):
            self.__parent = reduce(lambda p,q: pushout(p,q), (parent(el) for el in solution.values()), QQ)
        else:
            raise TypeError(f"The argument `I` must be an ideal or a list/tuple.")

        ##################################################################
        ## Creating the ideal for the branch
        ##################################################################
        self.__I = ideal(self.__parent, I)

        ##################################################################
        ## Storing the dictionary of partial solution
        ##################################################################
        self.__solution = {k : self.__parent(v) for k,v in solution.items()} # we store a copy with casted values
        self.__solution = SolutionBranch.__clean_solution(self.__solution, self.I, self.__parent)

        ##################################################################
        ## Storing the list of decisions taken
        ##################################################################
        self.__decisions = []
        for decision in decisions:
            if decision[0] in ("var", "arb"):
                _,var,value = decision
                if var not in self.__solution:
                    raise ValueError(f"Decided a variable that is not in the solution.")
                self.__decisions.append(("var", var, self.__parent(value)))
            elif decision[0] == "prim":
                self.__decisions.append(decision)
            elif decision[0] == "factor":
                self.__decisions.append(("factor", self.__parent(decision[1]), self.__parent(decision[2])))
            else:
                raise TypeError(f"Format of decision incorrect: {decision[0]}")

    @staticmethod
    def AllSolution(parent):
        r'''Static method to create a default solution: everything is a solution and there are no decisions taken. (::NO EXAMPLE::)'''
        return SolutionBranch([0], {}, [], base_parent=parent)

    ######################################################################################################
    ### PROPERTIES OF THE CLASS
    ######################################################################################################
    @property
    def I(self) -> Ideal: 
        r'''Property to get the ideal of the branch. (::NO EXAMPLE::)'''
        return self.__I
    @property
    def decisions(self) -> list: 
        r'''Property to get the list of decisions taken in the branch. (::NO EXAMPLE::)'''
        return self.__decisions

    def parent(self): 
        r'''Method to get the parent ring of the branch. (::NO EXAMPLE::)'''
        return self.__parent

    @cached_method
    def final_parent(self, field=False):
        r'''
            Method to compute the parent that will be used for the algebraic variety. It includes the information of algebraic components for which we can not work any further.

            This can be seen as creating the field of rational functions over the variety.

            ::NO EXAMPLE::

            TODO: Add more information about this method and maybe some examples.
        '''
        if field:
            return self.final_parent(False).fraction_field()

        ## First we create the algebraic extension
        B = self.parent().base()
        if self.I != ZZ(0):
            algebraic_variables = list(set(sum((list(poly.variables()) for poly in self.I.gens()), [])))
            BB = PolynomialRing(B, algebraic_variables)
            I = ideal(BB, self.I)
            try:
                B = reduce(lambda p, q : p.extension(q, names=str(q.variables()[0])), [QQ] + [poly.polynomial(poly.variables()[0]).change_ring(QQ) for poly in I.gens()])
            except Exception as e:
                logger.info(f"Found an error: {e}")
                B = BB.quotient(I, names=BB.variable_names())
        else:
            algebraic_variables = []

        ## We now add the remaining variables as polynomial variables
        rem_vars = [v for v in self.remaining_variables() if v not in algebraic_variables]
        if len(rem_vars) > 0:
            B = PolynomialRing(B, rem_vars)

        return B

    @cached_method
    def diff_parent(self, origin):
        r'''
            Recreate the differential structure over the :func:`final_parent` for this solution branch.
            
            As a main difference with :func:`final_parent`, which only creates an algebraic structure (using classes on Sage), this method
            creates the differential structure (following the concepts in :mod:`..dring`) so all the elements of the final parent have a derivative.

            ::NO EXAMPLE::

            TODO: Add a deeper information about this method and maybe some examples.
        '''
        if is_DPolynomialRing(origin):
            output = DPolynomialRing(self.diff_parent(origin.base()), origin.variable_names())
        elif isinstance(origin, FractionField_generic) and origin in _DRings:
            output = self.diff_parent(origin.base()).fraction_field()
        else:
            imgs_of_gens = {str(v): self.parent()(origin(str(v)).derivative()) if v in origin else 0 for v in self.final_parent().gens()}
            base = self.final_parent(origin.is_field())
            if any(imgs_of_gens[v] != 0 for v in (g for g in imgs_of_gens if g not in base.variable_names())):
                raise TypeError(f"Impossible to build the differential structure: something was not constant but was assigned in the solution branch")

            imgs_of_gens = {v : imgs_of_gens[v] for v in base.variable_names()}
            output = DifferentialRing(base, lambda p : imgs_of_gens[str(p)])
        return output

    def __getitem__(self, key):
        r'''Magic method to get the value of a variable from a string or polynomial. ::NO EXAMPLE::'''
        if not isinstance(key, str):
            if key not in self.parent().gens():
                raise KeyError(f"Only generators of {self.parent()} can be requested")
            key = str(key)
        return self.__solution.get(key, self.parent()(key)) # we get the value for the key or the key itself

    @cached_method
    def full_ideal(self, groebner: bool = True) -> Ideal:
        r'''
            Creates the full ideal that represents this Solution Branch. 
        
            It includes all the decided variables as part of the ideal (instead of evaluating the variables)
            ::NO EXAMPLE::
        '''
        polynomials = tuple(self.parent()(k) - v for (k,v) in self.__solution.items()) + tuple(self.I.gens())
        full_ideal = ideal(polynomials)

        if groebner:
            return ideal(full_ideal.groebner_basis())
        return full_ideal

    ######################################################################################################
    ### UTILITY METHODS
    ######################################################################################################
    def eval(self, element):
        r'''
            Evaluates an element of the polynomial ring within the solution branch.

            It basically transforms any polynomial into the corresponding value in the final parent field (see :func:`final_parent`) by evaluating the variables according to the solution branch.

            ::NO EXAMPLE::

            TODO: Add some examples of this method
        '''
        evaluating = (lambda p : p(**self.__solution)) if len(self.__solution) > 0 else (lambda p : p)
        if isinstance(element, DPolynomial): # case of differential polynomials
            # this should evaluate coefficients and monomials
            return evaluating(element)

        # case of coefficients
        if isinstance(element.parent(), FractionField_generic): # case of fractions
            numer = self.eval(element.numerator())
            denom = self.eval(element.denominator())
            return numer / denom
        else: # case of polynomials
            try:
                element = self.parent()(element)
            except Exception:
                element = self.parent().fraction_field()(element)
            try:
                return self.final_parent()(str(evaluating(element)))
            except Exception:
                return self.final_parent(True)(str(evaluating(element)))

    def remaining_variables(self):
        r'''List the variables that are not evaluated in the solution branch (including those linked algebraically) (::NO EXAMPLE::)'''
        return [v for v in self.parent().gens() if str(v) not in self.__solution]

    def subsolution(self, **kwds):
        r'''
            Creates a subsolution branch using extra information about the variables.

            It establish the value for new variables which are removed from the final parent accordingly to what is set on the current solution branch.
            NOTE: this method checks whether the given values were already set or not. It returns an error if we try to **change** a value.

            ::NO EXAMPLE::

            TODO: add examples of this method
        '''
        ## We check the input of new values
        new_values = dict()
        for (k,v) in kwds.items():
            v = self.parent()(v)

            if k in self.__solution and v != self.__solution[k]:
                raise ValueError(f"The variable {k} was already assigned")
            if any(g not in self.remaining_variables() for g in v.variables()):
                raise ValueError(f"The value for a variable must only contain remaining variables")
            new_values[k] = v

        ## We create the new ideal
        I = [el(**new_values) for el in self.I.gens()]

        ## We create the new dictionary
        solution = self.__solution.copy()
        solution.update(new_values)

        ## We create the new decisions
        decisions = self.decisions.copy()
        for (k,v) in new_values.items():
            decisions.append(("arb", k, v))

        return SolutionBranch(I, solution, decisions, self.parent())

    def is_subsolution(self, other: SolutionBranch) -> bool:
        r'''Checks whether ``other`` is a subsolution (i.e., its variety is a subset) of the current solution branch. (::NO EXAMPLE::)'''
        return all(self.full_ideal().reduce(g_other) == 0 for g_other in other.full_ideal(False).gens())

    def combine(self, other: SolutionBranch) -> list[SolutionBranch]:
        r'''Combine two solutions branches into one if they are compatible (::NO EXAMPLE::)'''
        sol = SolutionBranch._dir_combine(self, other)
        if sol == []:
            sol = SolutionBranch._dir_combine(other, self)
        return sol

    @staticmethod
    def _dir_combine(self, other):
        r'''See :func:`combine` (::NO EXAMPLE::)'''
        ## We first check the common solutions are equal
        ots_values = dict()
        sto_values = dict()

        if not (self.is_linear() and other.is_linear()):
            for v, val in other.__solution.items():
                if v in self.__solution:
                    if self.eval(val) != self.__solution[v]:
                        return [] # No solution
                else:
                    ots_values[v] = val
            for v, val in self.__solution.items():
                if v not in other.__solution:
                    sto_values[v] = val
            ## The other branch is compatible. We create the subsolution with these new values
            extended_self = self.subsolution(**ots_values) if len(ots_values) > 0 else self
            extended_other = other.subsolution(**sto_values) if len(sto_values) > 0 else other
            new_dict = extended_self.__solution
            I = extended_self.I.gens() + extended_other.I.gens()
        else:
            C = self.matrix_solution()
            D = other.matrix_solution()
            new_sol = C.right_kernel().intersection(D.right_kernel())
            if new_sol.dimension() == 0:
                # the zero is always a solution
                new_dict = {str(g): self.parent().zero() for g in self.parent().gens()}
                I = []
            else:
                ## Finding the generators
                generators = []
                for (i,column) in enumerate(new_sol.matrix().columns()):
                    if list(column).count(0) == len(column)-1 and list(column).count(1) == 1:
                        generators.append(self.parent().gens()[i])
                new_dict = {
                    str(g) : sum(column[i]*generators[i] for i in range(len(generators)))
                    for (g,column) in zip(self.parent().gens(), new_sol.matrix().columns())
                    if g not in generators
                }
                I = [el(**new_dict) for el in self.I.gens()+other.I.gens()]

        ## We now analyze the resulting ideal
        I = [el for el in I if el != 0]
        return analyze_ideal(I, new_dict, [])

    def matrix_solution(self):
        r'''
            ::NO EXAMPLE::
            TODO: Add documentation about this method
        '''
        if not self.is_linear():
            raise ValueError(f"Impossible to compute the matrix of solution with a non-linear solution branch.")
        coeff = lambda c,h : 0 if c == 0 else c.coefficient(h) if hasattr(c, "coefficient") else c.coefficients(True)[1]
        return Matrix([[
                    (coeff(self.__solution[str(g)],h) if str(g) in self.__solution else (0 if i != j else 1)) - (1 if i == j else 0)
                for j,h in enumerate(self.parent().gens())]
            for i,g in enumerate(self.parent().gens())], base_ring=self.parent().base())

    def is_avoiding(self, to_avoid: list[dict[str, int]]) -> bool:
        r'''Method to check whether a branch solution is avoiding some configurations (algebraic varieties) (::NO EXAMPLE::)'''
        return not _check_avoid(self.__solution, to_avoid)

    def is_linear(self) -> bool:
        r'''
            Method to know if the Branch has a similar known values.

            Checks whether the solution is of linear fashion, i.e., all elements appearing in
            the r.h.s. of ``self.__solution`` is linear in the variables.

            ::NO EXAMPLE::

            TODO: Add examples to this method
        '''
        return all(
            value == 0 or (value.degree() == 1 and (value.ct if hasattr(value, "ct") else value.constant_coefficient()) == 0)
            for value in self.__solution.values()
        )

    ######################################################################################################
    ### Equality methods
    ######################################################################################################
    def __eq__(self, other: SolutionBranch) -> bool:
        r'''Magic method to check equality (::NO EXAMPLE::)'''
        if not isinstance(other, SolutionBranch):
            return False
        return self.I == other.I and self.__solution == other.__solution

    def __ne__(self, other) -> bool:
        r'''Magic method to check non-equality (::NO EXAMPLE::)'''
        return not (self == other)

    def __hash__(self) -> int:
        r'''Magic method to compute the hash of a solution branch. (::NO EXAMPLE::)'''
        return hash((self.I, tuple(sorted(self.__solution.keys()))))

    def __repr__(self) -> str:
        r'''Magic method to represent the solution branch as a string. (::NO EXAMPLE::)'''
        parts = [f"Solution Branch"]
        if len(self.__solution) > 0:
            parts.append(f"[{','.join(f'{var}={val}' for (var, val) in self.__solution.items())}]")
        if self.__I.ngens() > 1 or self.__I.gens()[0] != 0:
            parts.append(f"with {self.__I.ngens()} relations {self.__I.gens()}")
        if len(self.__decisions) > 0:
            parts.append(f"with {len(self.__decisions)} decisions")
        if len(self.remaining_variables()) > 0:
            parts.append(f"and {','.join([str(v) for v in self.remaining_variables()])} as free variables")
        return f'{" ".join(parts)}.'

    def _latex_(self) -> str:
        r'''Magic method to represent the solution branch in LaTeX. (::NO EXAMPLE::)'''
        from sage.misc.latex import latex_variable_name
        parts = [r"\texttt{Solution}",
                 f"\\left[{','.join(latex_variable_name(str(latex(v))) for v in self.remaining_variables())}\\right]",
                 f"\\left({latex(self.I)}\\right)",
                 r"\left\{" + ",".join(f"{latex_variable_name(k)}={latex(v)}" for (k,v) in self.__solution.items()) + r"\right\}"
        ]

        return "".join(parts)

    ######################################################################################################
    ### STATIC METHODS OF THE CLASS
    ######################################################################################################
    @staticmethod
    def __clean_solution(solution: dict, ideal, parent):
        r'''Static method to remove iterated equalities throughout a dictionary with values for variables. (::NO EXAMPLE::)'''
        solution = {k: parent(v) for k,v in solution.items()}
        old_solution = None

        while solution != old_solution:
            old_solution = solution
            solution = {k: ideal.reduce(v(**old_solution)) for (k,v) in solution.items()}

        return solution


#################################################################################################
###
### MAIN ANALYSIS METHODS
###
#################################################################################################
@loglevel(logger)
def analyze_ideal(I, partial_solution: dict, to_avoid: list | dict , decisions: list = [], final_parent=None, groebner: bool = True, parallel: int = None) -> list[SolutionBranch]:
    r'''
        Method that applies simple steps for analyzing an ideal without human intervention

        This method studies a particular ideal (given some specific information and avoiding certain configurations) and 
        returns a list of solution branches that represent the different components of the algebraic variety defined by the ideal. 
        Instead of working directly with Gröbner basis (which would be the theoretical tool to study the variety of an ideal, 
        this method performs several simplifications, splitting the ideal into different simple components with the hope
        that the Gröbner basis we end up computing are simpler and, hence, faster to compute.

        The simplifications performed by this method are:
        * Finding simple elements: for example, finding linear polynomials of the type `v - c` for a given constant, or `c*v^e` for a given constant and exponent.
        * We split into factors. In particular, we consider `p(X) = p_1(X)p_2(X)...p_n(X)` and we change `p(X) = 0` into `p_i(X) = 0` for each factor.
        * We try to find expressions of the form `v = q(w)` for a polynomial `q`. This allows to remove a variable `v` and substitute it by a polynomial in the remaining variables.
        * We then compute a Gröbner basis.
        * If we already have a Gröbner basis, we do a primary decomposition.

        This method allows the use of Parallel computations to study subbranches.

        This method also performs a post-processing to remove subsolutions and solutions to avoid.

        ::NO EXAMPLE::
    '''
    if I == ideal(I.ring()):
        return (SolutionBranch.AllSolution(I.ring()),)

    StartPool(parallel) # starting (if needed) the processes pool

    ## We process the "to_avoid" argument
    if isinstance(to_avoid, dict):
        to_avoid = [to_avoid]

    logger.debug(f"[IDEAL] We start with a general overview.")
    branches = _analyze_ideal(I, partial_solution, to_avoid, decisions, final_parent, groebner=groebner)

    if not isinstance(I, (list, tuple)):
        I = I.gens()
    final_branches: set[SolutionBranch] = set()

    logger.debug(f"[IDEAL] Analyzing resulting branches ({len(branches)})...")
    while len(branches) > 0:
        logger.debug(f"[IDEAL] Analyzing one of the remaining branches...")
        branch = branches.pop()
        branch_GB = branch.full_ideal() # This should be efficient since the branches have passed through GB computations
        logger.debug(f"[IDEAL] We compute the original equations in the resulting branch.")
        equations = [branch_GB.reduce(equ) for equ in I]
        equations = [el for el in equations if el != 0] # cleaning zeros
        if len(equations) == 0:
            logger.debug(f"[IDEAL] All equations satisfied: we add this branch to final solution.")
            final_branches.add(branch)
        else:
            logger.debug(f"[IDEAL] New equations merged: analyzing more branches")
            new_branches = _analyze_ideal(equations, dict(), to_avoid, list(), final_parent, groebner=groebner)
            logger.debug(f"[IDEAL] Adding the new branches ({len(new_branches)})")
            for new_branch in new_branches:
                branches.append(
                    SolutionBranch(
                        new_branch.I,
                        branch._SolutionBranch__solution | new_branch._SolutionBranch__solution,
                        branch.decisions + new_branch.decisions,
                        branch.parent()
                    )
                )

    ## Filtering solutions with data to avoid
    logger.debug(f"[IDEAL] Removing solutions to avoid (starting with {len(final_branches)})")
    final_branches = [branch for branch in final_branches if branch.is_avoiding(to_avoid)]

    ## Filtering subsolutions
    logger.debug(f"[IDEAL] Removing subsolutions (starting with {len(final_branches)})")
    output: list[SolutionBranch] = list()
    for (i,branch) in enumerate(final_branches):
        logger.debug(f"[IDEAL] Starting with new {i}/{len(final_branches)}...")
        for other in output:
            if other.is_subsolution(branch):
                logger.debug(f"[IDEAL] Detected old branch as subsolution of new: removing old")
                output.remove(other)
            if branch.is_subsolution(other):
                logger.debug(f"[IDEAL] Detected new branch as subsolution of old: we do not add this branch")
                break
        else:
            logger.debug(f"[IDEAL] Nothing detected: we add a new branch")
            output.append(branch)
    logger.debug(f"[IDEAL] Remaining branches: {len(output)}")
    return output


@count_calls(logger)
def _analyze_ideal(I, partial_solution: dict, to_avoid: dict, decisions: list = [], final_parent=None, groebner: bool = True) -> list[SolutionBranch]:
    r'''See :func:`analyze_ideal` (::NO EXAMPLE::)'''
    ## First we prune the solution
    logger.debug(f"[ideal] +++ Starting new execution of _analyze_ideal")
    if _check_avoid(partial_solution, to_avoid):
        logger.debug(f"[ideal] ??? Pruning a branch where an undesired solution appear")
        return list()

    if not isinstance(I, (list, tuple)):
        I = I.gens()

    if len(I) == 0:
        logger.debug(f"[ideal] !!! No more polynomials to analyze. Returning this path")
        return [SolutionBranch(I, partial_solution, decisions, final_parent)]

    ## We copy the arguments to avoid possible collisions
    partial_solution = partial_solution.copy()
    decisions = decisions.copy()

    logger.debug(f"[ideal] +++ analyze_ideal ({len(I)} equations, {len(partial_solution)}/{I[0].parent().ngens()} variables)")

    if any(poly.degree() == 0 for poly in I): ## No solution case
        logger.debug(f"[ideal] Found a branch without a solution.")
        return []

    ###########################################################################################################
    ## First we try to find easy elements (that must be a constant)
    logger.debug(f"[ideal] ### Looking for polynomials with direct solution")
    to_eval = dict()
    for poly in I:
        if poly.degree() == 1 and len(poly.variables()) == 1: # polynomials of type (v - c)
            v = poly.variables()[0]
            c = poly.coefficient(v) if poly.parent().ngens() > 1 else poly.coefficients(False)[1]

            value = poly.parent()(v - poly/c)
            if str(v) in to_eval and to_eval[str(v)] != value:
                logger.debug(f"[ideal] Found incompatibility for ({poly}): {v} = {to_eval[str(v)]}")
                return [] # no solution for incompatibility of two equations
            elif str(v) not in to_eval:
                logger.debug(f"[ideal] ### Found simple polynomial ({poly}): adding solution {v} = {value}")
                to_eval[str(v)] = value
        elif len(poly.coefficients()) == 1 and len(poly.variables()) == 1: # case of type (c*v^d)
            v = poly.variables()[0]
            value = poly.parent().zero()
            if str(v) in to_eval and to_eval[str(v)] != value:
                logger.debug(f"[ideal] Found incompatibility for ({poly}): {v} = {to_eval[str(v)]}")
                return [] # no solution for incompatibility of two equations
            elif str(v) not in to_eval:
                logger.debug(f"[ideal] ### Found simple polynomial ({poly}): adding solution {v} = {value}")
                to_eval[str(v)] = value
        elif poly.degree() == 0 and poly != 0: # No solution in the ideal
            logger.debug(f"[ideal] Found no solution for an ideal")
            return []
    if len(to_eval):
        logger.debug(f"[ideal] ### Applying easy variables...")
        I = [el(**to_eval) for el in I]
        I = [el for el in I if el != 0] # removing zeros from the ideal
        logger.debug(f"[ideal] ### Applying recursively to the remaining polynomials ({len(I)})")
        partial_solution.update(to_eval)
        return _analyze_ideal(I, partial_solution, to_avoid, decisions, final_parent, groebner=groebner)

    ###########################################################################################################
    ## Third we try an easy type of splitting
    logger.debug(f"[ideal] $$$ Looking for monomials implying a splitting in solutions")
    for poly in I:
        if poly.is_monomial():
            logger.debug(f"[ideal] $$$ Found a splitting monomial: {poly}")
            args = []
            for v in poly.variables():
                path_sol = partial_solution.copy()
                path_sol[str(v)] = 0
                path_ideal = [el(**{str(v): 0}) for el in I]
                path_ideal = [el for el in path_ideal if el != 0]

                logger.debug(f"[ideal] $$$ SPLITTING WITH (({v} = 0))")
                args.append((path_ideal, path_sol, to_avoid, decisions + [("var", str(v), 0)], final_parent, groebner))

            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])

    ###########################################################################################################
    ## Four we try a different type of splitting
    logger.debug(f"[ideal] [[[ Looking for monomials implying a splitting in solutions")
    sorted_polynomials = sorted(I, key=lambda p : len(p.monomials()))
    for poly in sorted_polynomials:
        factors = poly.factor()
        if len(factors) > 1: # we can split
            logger.debug(f"[ideal] [[[ Found a splitting into {len(factors)} factors")
            for factor in factors:
                logger.debug(f"[ideal] [[[    {str(factor)[:20]}...")
            args = []
            for factor,_ in factors:
                path_ideal = [factor] + [p for p in I if p != poly]
                path_sol = partial_solution.copy()
                path_decisions = decisions + [("factor", factor, poly)]
                args.append((path_ideal, path_sol, to_avoid, path_decisions, final_parent, groebner))
            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])

    ###########################################################################################################
    ## Fifth we try to find elements where we can find v = p(w)
    logger.debug(f"[ideal] ??? Looking for polynomials with easy simplification")
    for poly in I:
        for v in reversed(poly.variables()):
            if poly.degree(v) == 1 and all(m == v or v not in m.variables() for m in poly.monomials()):
                variable = v
                break
        else:
            continue
        c = poly.coefficient(variable)
        value = poly.parent()(variable - poly/c)
        if str(variable) in to_eval:
            logger.debug(f"[ideal] ??? Found a repeated variable: {variable}")
        if any(str(w) in to_eval for w in value.variables()):
            logger.debug(f"[ideal] ??? Found a cyclic linear evaluation: discarding this simplification for now.")
        else:
            logger.debug(f"[ideal] ??? Found linear polynomial {poly}: adding solution {variable} = {value}")
            to_eval[str(variable)] = value
    if len(to_eval):
        logger.debug(f"[ideal] ??? Applying new reductions...")
        I = [el(**to_eval) for el in I]
        I = [el for el in I if el != 0] # removing zeros from the ideal
        logger.debug(f"[ideal] ??? Applying recursively to the remaining polynomials ({len(I)})")
        partial_solution.update(to_eval)
        return _analyze_ideal(I, partial_solution, to_avoid, decisions, final_parent, groebner=groebner)

    if groebner and len(I) > 1:
        ###########################################################################################################
        ## Sixth we try a Groebner basis
        logger.debug(f"[ideal] %%% Computing a GROEBNER BASIS of {len(I)} polynomials")
        for (i,poly_I) in enumerate(I):
            logger.debug(f"[ideal] %%% \t{i:4} -> {cut_string(poly_I, 50)}")

        I_gb = ideal(I).groebner_basis()

        if not all(poly in I_gb for poly in I): # we improved with a Gröbner basis
            logger.debug(f"[ideal] %%% The ideal was changed when computing a Groebner basis: we apply recursively to the GB")
            return _analyze_ideal(I_gb, partial_solution, to_avoid, decisions, final_parent, groebner=groebner)

        ###########################################################################################################
        ## Seventh we try a primary decomposition
        logger.debug(f"[ideal] +++ Computing a PRIMARY DECOMPOSITION of {len(I)} polynomials")
        logger.debug(f"[ideal] +++ First, we compute the radical")
        I = ideal(I).radical().gens() # Computing the radical of the original ideal
        logger.debug(f"[ideal] +++ Now, we compute the primary decomposition.")
        primary_decomp = ideal(I).primary_decomposition()
        if len(primary_decomp) != 1: # We are not done: several component found
            logger.debug(f"[ideal] +++ Found {len(primary_decomp)} components: splitting into decisions")
            args = []
            for primary in primary_decomp:
                logger.debug(f"[ideal] --- Computing radical ideal of primary component")
                primary = primary.radical()
                logger.debug(f"[ideal] --- Applying recursively to the radical ideal ({len(primary.gens())})")
                args.append((primary, partial_solution, to_avoid, decisions + [("prim", primary.gens())], final_parent, groebner))

            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])

    logger.debug(f"[ideal] !!! Reached ending point for analyzing an ideal. Returning this path")
    return [SolutionBranch(I, partial_solution, decisions, final_parent)]


def _check_avoid(partial_solution: dict, to_avoid: list):
    r'''
        Method to check whether a partial solution has an undesired configuration.

        The argument ``to_avoid`` is provided as a list of dictionaries. This can be translated into
        a logical formula:

        * A dictionary `D` can be translated into `\bigwedge_{(k,v)\in D} k = v`.
        * A list `L` can be translated into `\bigvee_{l \in L} l`.

        ::NO EXAMPLE::
    '''
    return any(all(partial_solution.get(v, None) == avoiding[v] for v in avoiding) for avoiding in to_avoid)


#################################################################################################
###
### PARTIAL ANALYSIS METHOD
###
#################################################################################################
@loglevel(logger)
def eliminate_linear_variables(I: Ideal, variables):
    r'''
        Method to eliminate the linear variables that are not relevant for the ideal.

        Assume that `I \subset R[x_1,\ldots,x_n,y_1,\ldots,y_n]`, that we are interested in the
        elimination ideal `I \cap R[x_1,\ldots, x_n]` and that the variables `y_1,\ldots,y_n`
        appear linearly in the generators of `I`.

        This method computes the elimination ideal by considering the induced linear system
        by the generators of `I` and using the rank condition on this linear system to
        obtain non-linear conditions on `x_1,\ldots,x_n`.

        Need to be done:
        * Check this is exactly the elimination ideal
        * Perform a fast computation
        * Compute GB while computing equations or not?

        ::NO EXAMPLE::
    '''
    logger.debug(f"[ELV] Eliminating linear variables {variables=} from ideal using minors")
    generators = I.gens()
    ring = I.parent().ring()

    variables = [ring(v) for v in variables] # we make sure the variables are in the correct ring
    if not all(v.is_generator() for v in variables):
        raise ValueError(f"[ELV] We can only remove linear variables if variables are provided (given {variables})")
    if not all(all(g.degree(v) <= 1 for v in variables) for g in generators):
        raise ValueError(f"[ELV] We can only remove linear variables if the generators are linear in these variables.")

    logger.debug(f"[ELV] Checking and filtering the input...")
    ring = ring.remove_var(*variables)
    variables = [v for v in variables if any(g.degree(v) > 0 for g in generators)] # removing unnecessary variables
    generators = [g for g in generators if g != 0] # removing zero generators

    logger.debug(f"[ELV] Building the matrix with n={len(generators)} rows and m={len(variables)} columns")
    A = Matrix([[ring(g.coefficient(v)) for v in variables] for g in generators]) # matrix of linear system
    logger.debug(f"[ELV] Computing the inhomogeneous vector...")
    b = vector([ring(g.coefficient({v: 0 for v in variables})) for g in generators]) # inhomogeneous term
    if b != 0:
        raise NotImplementedError(f"[ELV] Elimination of linear variables for inhomogeneous systems not yet implemented.")
    n = A.ncols()
    m = A.nrows()

    total = binomial(m,n) # this is how many minors we need to compute
    total_10 = total//10
    total_100 = total//100
    final_ideal = ideal(ring)

    C = [[i for i in range(A.nrows()) if A[i][j] != 0] for j in range(A.ncols())]

    logger.debug(f"[ELV] Rows for each column with non-zero elements:\n\t" + "\n\t".join(str(c) for c in C))
    print(f"[ELV] Rows for each column with non-zero elements:\n\t" + "\n\t".join(str(c) for c in C), flush=True)
    for i,c in enumerate(Combinations(range(m), n)):
        if total_10 == 0 or i == total-1 or i % total_10 == 0:
            logger.debug(f"[ELV] ++ Computing minor {i+1}/{total}... (Ideal with {final_ideal.ngens()} generators)")
            print(f"[ELV] ++ Computing minor {i+1}/{total}... (Ideal with {final_ideal.ngens()} generators)", end="\r", flush=True)

        A_ = A.matrix_from_rows(c)
        red_det = final_ideal.reduce(A_.determinant())

        if red_det != 0: # there is something to add
            final_ideal = ideal(ideal(final_ideal.gens() + (red_det,)).groebner_basis())
            if 1 in final_ideal:
                break
    print("\n[ELV] -- Finished the computation of minors")

    logger.debug(f"[ELV] -- Finished elimination of linear variables")
    return final_ideal


def find_nonzero_minor(A, size):
    r'''Method to find a non-zero minor of a given size in a matrix. (::NO EXAMPLE::)'''
    from itertools import product
    for rows in product(*[[i for i in range(A.nrows()) if A[i][c] != 0] for c in range(A.ncols())]):
        for cols in Combinations(range(A.ncols()), size):
            mrows = [rows[i] for i in cols]
            if A.matrix_from_rows_and_columns(mrows, cols).determinant() != 0:
                return (mrows, cols)


__all__ = ["analyze_ideal", "eliminate_linear_variables"]