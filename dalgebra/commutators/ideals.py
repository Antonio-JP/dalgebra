r'''    
    Analysis of algebraic ideals.

    This module contains some additional functionality to study the algebraic ideals generated in the computations
    of the module :mod:`dalgebra.commutators`.

    This software has been used in the presentation in ISSAC'23 "Computing almost-commuting basis of Ordinary Differential
    Operators", by A. Jiménez-Pastor, S.L. Rueda and M.A. Zurro in Tromsø, Norway.

    **Things remaining TODO**
    -----------------------------------------

    1. Extend this documentation
    
    **Elements provided by the module**
    -----------------------------------------
'''
from __future__ import annotations

import logging

logger = logging.getLogger(__name__)

from functools import reduce
from sage.all import cached_method, ideal, parent, QQ, ZZ
from sage.categories.pushout import pushout
from sage.parallel.multiprocessing_sage import Pool
from sage.rings.fraction_field import is_FractionField
from sage.rings.ideal import Ideal_generic as Ideal
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from typing import Any

from ..dring import DifferentialRing, DRings
from ..dpolynomial.dpolynomial_element import DPolynomial
from ..dpolynomial.dpolynomial_ring import DPolynomialRing, DPolynomialRing_dense
from ..logging.logging import loglevel, cut_string

_DRings = DRings.__classcall__(DRings)

#################################################################################################
###
### AUXILIAR STRUCTURES AND CODE TO RUN IN PARALLEL
###
#################################################################################################
__ProcessesPool = None
def LoopInParallel(func, iterable, chunksize=1):
    r'''
        Method that tries to loop a function application in parallel. If no Pool is created, then we simply loop in the usual way.
    '''
    if __ProcessesPool != None:
        logger.debug(f"[LoopInParallel] Starting parallel computation of {len(iterable)} processes in {__ProcessesPool._processes}")
        return __ProcessesPool.starmap(func, iterable, chunksize)
    else:
        return (func(*el) for el in iterable)
    
def StartPool(ncpus: int = None):
    global __ProcessesPool
    if __ProcessesPool == None and ncpus != None:
        __ProcessesPool = Pool(ncpus)

#################################################################################################
###
### CLASS FOR STORING SOLUTIONS OF IDEALS
###
#################################################################################################
class SolutionBranch:
    def __init__(self, I: list | Ideal, solution: dict[str,Any], decisions: list[tuple[str,str,Any] | tuple[str,Any]], base_parent = None):
        ##################################################################
        ## Deciding the parent
        ##################################################################
        if base_parent != None:
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
        self.__solution = SolutionBranch.__clean_solution(self.__solution, self.__parent)

        ##################################################################
        ## Storing the list of decisions taken
        ##################################################################
        self.__decisions = []
        for decision in decisions:
            if decision[0] in ("var", "arb"):
                _,var,value = decision
                if not var in self.__solution:
                    raise ValueError(f"Decided a variable that is not in the solution.")
                self.__decisions.append(("var", var, self.__parent(value)))
            elif decision[0] == "prim":
                self.__decisions.append(decision)
            elif decision[0] == "factor":
                self.__decisions.append(("factor", self.__parent(decision[1]), self.__parent(decision[2])))
            else:
                raise TypeError(f"Format of decision incorrect: {decision[0]}")
            
    ######################################################################################################
    ### PROPERTIES OF THE CLASS
    ######################################################################################################
    @property
    def I(self) -> Ideal: return self.__I
    @property
    def decisions(self) -> list: return self.__decisions
    
    def parent(self): return self.__parent

    @cached_method
    def final_parent(self, field=False):
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
                logger.error(f"Found an error: {e}")
                B = BB.quotient(I, names=BB.variable_names())
        else:
            algebraic_variables = []

        ## We now add the remaining variables as polynomial variables
        rem_vars = [v for v in self.remaining_variables() if not v in algebraic_variables]
        B = PolynomialRing(B, rem_vars)
        return B

    @cached_method
    def diff_parent(self, origin):
        r'''Recreate the differential structure over the :func:`final_parent` for this solution branch.'''
        if isinstance(origin, DPolynomialRing_dense):
            output = DPolynomialRing(self.diff_parent(origin.base()), origin.variable_names())
        elif is_FractionField(origin) and origin in _DRings:
            output = self.diff_parent(origin.base()).fraction_field()
        else: 
            imgs_of_gens = {str(v): self.parent()(origin(str(v)).derivative()) if v in origin else 0 for v in self.final_parent().gens()}
            base = self.final_parent().fraction_field() if origin.is_field() else self.final_parent()
            if any(imgs_of_gens[v] != 0 for v in (g for g in imgs_of_gens if g not in base.variable_names())):
                raise TypeError(f"Impossible to build the differential structure: something was not constant but was assigned in the solution branch")
            
            imgs_of_gens = {v : imgs_of_gens[v] for v in base.variable_names()}
            output = DifferentialRing(base, lambda p : imgs_of_gens[str(p)])
        return output

    def __getitem__(self, key):
        if not isinstance(key, str):
            if not key in self.parent().gens(): raise KeyError(f"Only generators of {self.parent()} can be requested")
            key = str(key)
        return self.__solution.get(key, self.parent()(key)) # we get the value for the key or the key itself
    
    ######################################################################################################
    ### UTILITY METHODS
    ######################################################################################################    
    def eval(self, element):
        if isinstance(element, DPolynomial): # case of differential polynomials
            dR = self.diff_parent(element.parent())
            return sum(
                c*m for (c,m) in zip(
                    (dR(self.eval(el)) for el in element.coefficients()),
                    (dR(str(el)) for el in element.monomials())
                )
            )
        
        # case of coefficients
        if is_FractionField(element.parent()): # case of fractions
            numer = self.eval(element.numerator())
            denom = self.eval(element.denominator())
            return numer / denom
        else: # case of polynomials
            try:
                element = self.parent()(element)
            except:
                element = self.parent().fraction_field()(element)
            try:
                return self.final_parent()(str(element(**self.__solution)))
            except:
                return self.final_parent(True)(str(element(**self.__solution)))
    
    def remaining_variables(self):
        return [v for v in self.parent().gens() if not str(v) in self.__solution]

    def subsolution(self, **kwds):
        ## We check the input of new values
        new_values = dict()
        for (k,v) in kwds.items():
            if k in self.__solution:
                raise ValueError(f"The variable {k} was already assigned")
            v = self.parent()(v)
            if any(g not in self.remaining_variables() for g in v.variables()):
                raise ValueError(f"The value for a variable must only contain remaining variables")
            new_values[k] = v

        ## We create the new ideal
        I = [el(**new_values) for el in self.I.gens()]
        ## We create the new dictionary
        solution = self.__solution.copy(); solution.update(new_values)
        ## We create the new decisions
        decisions = self.decisions.copy()
        for (k,v) in new_values.items():
            decisions.append(("arb", k, v))

        return SolutionBranch(I, solution, decisions, self.parent())
        
    def is_subsolution(self, other: SolutionBranch) -> bool:
        self_vars = self.remaining_variables(); other_vars = other.remaining_variables()
        if any(v not in other_vars for v in self_vars):
            return False
        
        to_subs = {str(v): self[str(v)] for v in other_vars if (not v in self_vars)}
        if len(to_subs) > 0:
            other = other.subsolution(**to_subs)
        return self == other

    ######################################################################################################
    ### Equality methods
    ######################################################################################################
    def __eq__(self, other: SolutionBranch) -> bool:
        if not isinstance(other, SolutionBranch): return False
        return self.I == other.I and self.__solution == other.__solution
    
    def __hash__(self) -> int: return hash((self.I, tuple(sorted(self.__solution.keys()))))

    ######################################################################################################
    ### STATIC METHODS OF THE CLASS
    ######################################################################################################
    @staticmethod
    def __clean_solution(solution: dict, parent):
        solution = {k: parent(v) for k,v in solution.items()}
        old_solution = None

        while(solution != old_solution):
            old_solution = solution
            solution = {k: v(**old_solution) for (k,v) in solution.items()}

        return solution
 
#################################################################################################
###
### MAIN ANALYSIS METHODS
###
################################################################################################# 
@loglevel(logger)
def analyze_ideal(I, partial_solution: dict, decisions: list=[], final_parent = None, groebner: bool = True, parallel: int = None) -> list[SolutionBranch]:
    r'''Method that applies simple steps for analyzing an ideal without human intervention'''

    StartPool(parallel) # starting (if needed) the processes pool

    logger.debug(f"[IDEAL] We start with a general overview.")
    branches = _analyze_ideal(I, partial_solution, decisions, final_parent, groebner=groebner)

    if not isinstance(I, (list, tuple)):
        I = I.gens()
    final_branches: set[SolutionBranch] = set()
    
    logger.info(f"[IDEAL] Analyzing resulting branches ({len(branches)})...")
    while len(branches) > 0:
        logger.debug(f"[IDEAL] Analyzing one of the remaining branches...")
        branch = branches.pop()
        branch_GB = branch.I.groebner_basis() # This should be efficient since the branches have passed through GB computations
        logger.debug(f"[IDEAL] We compute the original equations in the resulting branch.")
        equations = [equ(**branch._SolutionBranch__solution).reduce(branch_GB) for equ in I]
        equations = [el for el in equations if el != 0] # cleaning zeros
        if len(equations) == 0:
            logger.debug(f"[IDEAL] All equations satisfied: we add this branch to final solution.")
            final_branches.add(branch)
        else:
            logger.debug(f"[IDEAL] New equations merged: analyzing more branches")
            new_branches = _analyze_ideal(equations, dict(), list(), final_parent, groebner=groebner)
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
    ## Filtering subsolutions
    logger.info(f"[IDEAL] Removing subsolutions (starting with {len(final_branches)})")
    output: list[SolutionBranch] = list()
    for (i,branch) in enumerate(final_branches):
        (logger.info if i%100 == 0 else logger.debug)(f"[IDEAL] Starting with new {i}/{len(final_branches)}...")
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
    logger.info(f"[IDEAL] Remaining branches: {len(output)}")
    return output

def _analyze_ideal(I, partial_solution: dict, decisions: list=[], final_parent = None, groebner: bool = True) -> list[SolutionBranch]:
    r'''Method that applies simple steps for analyzing an ideal without human intervention'''
    if not isinstance(I, (list, tuple)):
        I = I.gens()

    if len(I) == 0:
        logger.info(f"[ideal] !!! No more polynomials to analyze. Returning this path")
        return [SolutionBranch(I, partial_solution, decisions, final_parent)]
    
    ## We copy the arguments to avoid possible collisions
    partial_solution = partial_solution.copy()
    decisions = decisions.copy()

    if any(poly.degree() == 0  for poly in I): ## No solution case
        logger.info(f"[ideal] Found a branch without a solution.")
        return []

    ########################################################################################################### 
    ## First we try to find easy elements (that must be a constant)
    logger.debug(f"[ideal] ### Looking for polynomials with direct solution")
    to_eval = dict()
    for poly in I:
        if poly.degree() == 1 and len(poly.variables()) == 1: # polynomials of type (v - c)
            v = poly.variables()[0]; c = poly.coefficient(v) if poly.parent().ngens() > 1 else poly.coefficients(False)[1]
            value = poly.parent()(v - poly/c)
            if str(v) in to_eval and to_eval[str(v)] != value:
                logger.debug(f"[ideal] Found incompatibility for ({poly}): {v} = {to_eval[str(v)]}")
                return [] # no solution for incompatibility of two equations
            elif not str(v) in to_eval:
                logger.debug(f"[ideal] ### Found simple polynomial ({poly}): adding solution {v} = {value}")
                to_eval[str(v)] = value
        elif len(poly.coefficients()) == 1 and len(poly.variables()) == 1: # case of type (c*v^d)
            v = poly.variables()[0]
            value = poly.parent().zero()
            if str(v) in to_eval and to_eval[str(v)] != value:
                logger.debug(f"[ideal] Found incompatibility for ({poly}): {v} = {to_eval[str(v)]}")
                return [] # no solution for incompatibility of two equations
            elif not str(v) in to_eval:
                logger.debug(f"[ideal] ### Found simple polynomial ({poly}): adding solution {v} = {value}")
                to_eval[str(v)] = value
        elif poly.degree() == 0 and poly != 0: # No solution in the ideal
            return []
    if len(to_eval):
        logger.debug(f"[ideal] ### Applying easy variables...")
        I = [el(**to_eval) for el in I]
        I = [el for el in I if el != 0] # removing zeros from the ideal
        logger.debug(f"[ideal] ### Applying recursively to the remaining polynomials ({len(I)})")
        partial_solution.update(to_eval)
        return _analyze_ideal(I, partial_solution, decisions, final_parent, groebner=groebner)
        
    ###########################################################################################################
    ## Third we try an easy type of splitting
    logger.debug(f"[ideal] $$$ Looking for monomials implying a splitting in solutions")
    for poly in I:
        if poly.is_monomial():
            logger.info(f"[ideal] $$$ Found a splitting monomial: {poly}")
            args = []
            for v in poly.variables():
                path_sol = partial_solution.copy()
                path_sol[str(v)] = 0
                path_ideal = [el(**{str(v): 0}) for el in I]; path_ideal = [el for el in path_ideal if el != 0]
                logger.debug(f"[ideal] $$$ SPLITTING WITH (({v} = 0))")
                args.append((path_ideal, path_sol, decisions + [("var", str(v), 0)], final_parent, groebner))
            
            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])
        
    ###########################################################################################################
    ## Four we try a different type of splitting
    logger.debug(f"[ideal] [[[ Looking for monomials implying a splitting in solutions")
    sorted_polynomials = sorted(I, key=lambda p : len(p.monomials()))
    for poly in sorted_polynomials:
        factors = poly.factor()
        if len(factors) > 1: # we can split
            logger.info(f"[ideal] [[[ Found a splitting into {len(factors)} factors")
            args = []
            for factor,_ in factors:
                path_ideal = [factor] + [p for p in I if p != poly]
                path_sol = partial_solution.copy()
                path_decisions = decisions + [("factor", factor, poly)]
                args.append((path_ideal, path_sol, path_decisions, final_parent, groebner))
            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])

    ###########################################################################################################
    ## Fifth we try to find elements where we can find v = p(w)
    logger.debug(f"[ideal] ??? Looking for polynomials with easy simplification")
    for poly in I:
        for v in reversed(poly.variables()):
            if poly.degree(v) == 1 and all(m == v or not v in m.variables() for m in poly.monomials()):
                variable = v
                break
        else:
            continue
        c = poly.coefficient(variable)
        value = poly.parent()(variable - poly/c)
        if str(variable) in to_eval:
            logger.debug(f"[ideal] ??? Found a repeated variable: {variable}")
        else:
            logger.debug(f"[ideal] ??? Found linear polynomial {poly}: adding solution {variable} = {value}")
            to_eval[str(variable)] = value
    if len(to_eval):
        logger.debug(f"[ideal] ??? Applying new reductions...")
        I = [el(**to_eval) for el in I]
        I = [el for el in I if el != 0] # removing zeros from the ideal
        logger.debug(f"[ideal] ??? Applying recursively to the remaining polynomials ({len(I)})")
        partial_solution.update(to_eval)
        return _analyze_ideal(I, partial_solution, decisions, final_parent, groebner=groebner)

    if groebner:
        ###########################################################################################################
        ## Sixth we try a Groebner basis
        logger.info(f"[ideal] %%% Computing a GROEBNER BASIS of {len(I)} polynomials")
        for (i,poly_I) in enumerate(I): logger.debug(f"[ideal] %%% \t{i:4} -> {cut_string(poly_I, 50)}")
        I_gb = ideal(I).groebner_basis()
        if not all(poly in I_gb for poly in I): # we improved with a Gröbner basis
            logger.debug(f"[ideal] %%% The ideal was changed when computing a Groebner basis: we apply recursively to the GB")
            return _analyze_ideal(I_gb, partial_solution, decisions, final_parent, groebner=groebner)
        
        ###########################################################################################################
        ## Seventh we try a primary decomposition
        logger.info(f"[ideal] +++ Computing a PRIMARY DECOMPOSITION of {len(I)} polynomials")
        logger.debug(f"[ideal] +++ First, we compute the radical")
        I = ideal(I).radical().gens() # Computing the radical of the original ideal
        logger.debug(f"[ideal] +++ Now, we compute the primary decomposition.")
        primary_decomp = ideal(I).primary_decomposition()
        if len(primary_decomp) != 1: # We are not done: several component found
            logger.info(f"[ideal] +++ Found {len(primary_decomp)} components: splitting into decisions")
            args = []
            for primary in primary_decomp:
                logger.debug(f"[ideal] --- Computing radical ideal of primary component")
                primary = primary.radical()
                logger.debug(f"[ideal] --- Applying recursively to the radical ideal ({len(primary.gens())})")
                args.append((primary, partial_solution, decisions + [("prim", primary.gens())], final_parent, groebner))

            return sum((solutions for solutions in LoopInParallel(_analyze_ideal, args)), [])
        
    logger.info(f"[ideal] !!! Reached ending point for analyzing an ideal. Returning this path")
    
    return [SolutionBranch(I, partial_solution, decisions, final_parent)]
  

__all__ = ["analyze_ideal"]