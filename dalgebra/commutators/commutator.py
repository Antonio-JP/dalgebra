r'''
    Computing non-trivial centralizers.

    TODO: CHECK CHANGES FROM NEW DPOLYNOMIAL FRAMEWORK

    This module contains the main functionality used for computing non-trivial centralizers of linear differential operators.

    This software has been used in the presentation in ISSAC'23 "Computing almost-commuting basis of Ordinary Differential
    Operators", by A. Jiménez-Pastor, S.L. Rueda and M.A. Zurro in Tromsø, Norway.


    **Theory explanation**
    -----------------------------------------

    Let us consider an algebraically closed field of characteristic zero `C` and the field of d-polynomials defined by `n-2`
    differential variables `u_2,\ldots,u_{n}`. Let us consider the linear differential operator:


    .. MATH::

        L = \partial^n + u_{2}\partial^{n-2}  + \ldots + u_{n-1}\partial + u_n.

    This operator `L` can be written in terms of d-polynomials in the ring `K\{z\} = C\{u_2,\ldots,u_{n},z\}`. We say that
    another operator `P \in K\{z\}` *commutes with `L`* if and only if the commutator of `L` with `P` (`[L,P]`) is zero.

    In the ring of differential polynomials `K\{z\}`, every operator commutes since we are considering the multiplication
    as usual polynomials. However, if we consider the elements of `K\{z\}` as operators in `z`, we can see them acting via
    substitution in any differential extension of `K`. This action defines a new product operation in `K\{z\}`:

    .. MATH::

        A(z) \cdot B(z) = A(B(z))

    Since `z` is a differential variable, we can see that this multiplication is `C`-linear, which allows to define an
    alternative `C`-algebra structure over `K\{z\}`. This `C`-algebra will be non-commutative, making sense to consider the
    commutator `[A,B] = A\cdot B - B\cdot A` and the concept of centralizer

    .. MATH::

        \mathcal{C}(A) = \left\{B(z) \in K\{z\}\ :\ [A,B] = 0\right\}.

    This module provides methods to study the commutator of differential operators. As this is a difficult problem, we consider
    operators in normal form. These operators are specializations of the operators `L` shown above. Hence, we can apply
    the theory of almost-commuting operators to guide in this search.

    For more information about *almost-commuting* operators and how to compute them, we refer to :mod:`almost_commuting`.

    **Examples of usage**
    -----------------------------------------

    TODO: Add examples of usage of the module that will serve as tests

    **Things remaining TODO**
    -----------------------------------------

    1. Fill the Examples on the documentation

    **Elements provided by the module**
    -----------------------------------------
'''
from __future__ import annotations

import logging
from typing import TextIO
logger = logging.getLogger(__name__)

from contextlib import nullcontext
from functools import reduce, lru_cache

from time import sleep

from sage.calculus.functional import diff
from sage.categories.pushout import pushout
from sage.combinat.combination import Combinations
from sage.combinat.composition import Compositions
from sage.functions.other import binomial
from sage.matrix.constructor import Matrix
from sage.misc.latex import latex as _latex
from sage.rings.ideal import Ideal_generic as Ideal, Ideal as ideal
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element_generic import Polynomial
from sage.rings.rational_field import QQ
from sage.structure.element import parent, Element

from ..dring import DRings, DifferentialRing, DFractionField
from ..dpolynomial.dpolynomial import DPolynomial, DPolynomialGen
from ..logging.logging import loglevel
from .almost_commuting import generic_normal, almost_commuting_wilson
from .ideals import analyze_ideal, SolutionBranch

_DRings = DRings.__classcall__(DRings)

###############################################################################################
## Trying to initialize Maple
###############################################################################################
try:
    from sage.interfaces.maple import maple as Maple
    if not Maple.is_running():
        Maple._start()
    _HAS_MAPLE = True
except RuntimeError:
    _HAS_MAPLE = False

def _generate_maple_command(ideal: list[DPolynomial]) -> str:
    return "\n".join(["seq_polys := " + ",".join(str(p) for p in ideal) + ":",
                      r'print("Read file: ", nops({seq_polys}));',
                      r"solve({seq_polys});"
    ])

def _parse_maple_output(output: str, ring) -> list[Ideal]:
    ## We process the string: "{solution_1}, {solution_2}, ..., {solution_n}
    solutions = output.split("{") ## we split through the opening of each solution
    solutions = [solution.strip()[:solution.find("}")] for solution in solutions[1:]] # we remove the closing bracket in each string

    ## Now we have the following in each solution: "var_1 = value_1, var_2 = value_2, ..., var_n = value_n"
    solutions = [solution.replace("=","-").split(",") for solution in solutions]
    solutions = [ideal([ring(poly) for poly in solution]) for solution in solutions]

    ## Now each solution is an ideal (easy to analyze)
    return solutions

def latex(*args, **kwds) -> str:
    latex_str = str(_latex(*args, **kwds))
    return latex_str.replace(r"\Bold", r"\mathbb")

#################################################################################################
###
### METHODS TO OBTAIN CENTRALIZER UP TO A CERTAIN LEVEL
###
#################################################################################################
def GetCentralizer(
        U: tuple[Element], global_bound: int, *, 
        starting_level:int = 1, update_bound: bool = True, ignore_bound: bool = False,
        extra_info: SolutionBranch = None
        ):
    r'''
        Method to compute the centralizer of a linear differential operator in normal form up to a bound.

        This method computes all the generators of the centralizer for a given operator `L` in normal form
        of fixed order `n` as a `C[L]`-module (see Goodearl's results) up to a given bound order. These results
        guarantee that this `C[L]`-module is generated by a set of operators `A_i` with i \in I \subset \{0,\ldots,n-1\}`,
        an additive subgroup of `\mathbb{Z}_n`, such that:

        * `\ord(A_i) \equiv i (mod\ n)`.
        * `\ord(A_i)` is minimal w.r.t. those operators in the centralizer whose order is congruent with `i` modulo `n`.
        
        We assume the level of the operator `L` (i.e., the first order with a non-trivial element in the centralizer)
        has been computed and is given in ``starting_level``.

        Due to some structural results, when a non-trivial element of the centralizer is found, some extra bounds can be 
        obtained for the orders of some of the generators. More precisely, if operators \{A_{i_1},\ldots,A_{i_k}\} have been
        found already, we know that the order of any other generator $A_j$ must be bound by

        .. MATH::

            \min\{\{n_1\ord(A_{i_1}) + \ldots n_k\ord(A_{i_k})\ :\ (n_1,\ldots,n_k)\in \mathbb{N}^k\} \cap 
            \{kn+j\ :\ k \in \mathbb{k} \in \mathbb{N}\}\}

        The argument ``ignore_bounds`` will allow the code to go beyond the original bound when a new precise bound have been 
        obtained.
    '''
    ## Checking the arguments
    if not global_bound in ZZ or global_bound <= 0:
        raise ValueError(f"[GC] The global bound must be a positive integer")
    if not starting_level in ZZ or starting_level <= 0:
        raise ValueError(f"[GC] The starting level of computation must be a positive integer")
    
    n = len(U) + 1 ## order of the operator

    Goodearl_Basis = [1] + (n-1)*[None]
    bounds = __compute_bounds(n, global_bound=global_bound, ignore_bound=ignore_bound)
    B = max(bounds)
    current = starting_level
    L = None
    logger.log(15, f"[GC] Computing the centralizer of an operator of order {n}")
    logger.log(15, f"[GC] Starting bounds: {bounds}")
    logger.log(15, f"[GC] Starting level:  {starting_level}")

    c_coeffs = list(el for el in range(1,starting_level) if el % n != 0)
    level_flag = None

    while current <= B:
        r = current % n
        if Goodearl_Basis[r] is None and (current == global_bound or current < bounds[r]):
            logger.log(15, f"[GC] ++ Looking for solution at level {current} -- congruence class {r} (mod {n})...")
            logger.log(15, f"[GC] ++ Current bounds: {bounds}")
            logger.log(15, f"[GC] ++ Looking with coefficients: {c_coeffs + [current]}")
            L, Ps, (system, _) = GetHierarchyLinearEquations(
                n, current, U, 
                c_coeffs + [current]
            )

            if extra_info is not None: ## Using the extra information if provided
                logger.log(15, f"[GC] ++     Converting data...")
                system = Matrix([[extra_info.eval(el) for el in row] for row in system])
                system = Matrix([row for row in system if row != 0]) # we ensure the matrix has no zero rows

            if system[:,:-1].rank() == system.rank(): # the linear system with the last column has solution
                logger.log(15, f"[GC] ++     Found a solution!")
                if system.nrows() == 0: ## Case with no left equations
                    cs = (len(Ps)-1)*[0] + [1]
                elif system[:,-1] == 0: ## Last column is all zeros
                    cs = (len(Ps)-1)*[0] + [1]
                else: # there is a system to be solved
                    cs = system[:,:-1].solve_right(-system[:,-1]) 
                    cs = list(c[0] for c in cs) + [1] ## Changing from matrix to list format
                if level_flag == None: level_flag = cs.copy() ## We save the flag
                element_centralizer = sum(c*P for (c,P) in zip(cs, Ps))
                if extra_info is not None:
                    element_centralizer = extra_info.eval(element_centralizer)
                Goodearl_Basis[r] = element_centralizer
                bounds[r] = current
                if update_bound: ## We update the bounds
                    logger.log(15, f"[GC] ++     Updating bounds...")
                    bounds = __compute_bounds(
                        n, 
                        *[bounds[r] for r in range(1,n) if Goodearl_Basis[r] is not None], 
                        global_bound=global_bound, ignore_bound=ignore_bound
                    )
                    B = max(bounds)
            else: ## No solution -- we keep this coefficient for future searches
                c_coeffs.append(current)
                ## We check if there is something more in this congruence class
                if current + n == bounds[r]: # next iteration will reach the bound -> it is a decomposition
                    logger.log(15, f"[GC] +! Preventing bound for congruence class {r} (mod {n}): {(current + n)}")
                    logger.log(15, f"[GC] +!     Computing decomposition with other elements of the basis...")
                    decomposition = len(bounds)*[0]
                    values = {v : i+1 for (i,v) in enumerate(bounds[1:]) if v < (current + n)}
                    compositions = Compositions((current + n), min_part = min(values), max_part=max(values))
                    for comp in compositions:
                        if set(comp).issubset(values.keys()):
                            for v in comp:
                                decomposition[values[v]] += 1
                            break
                    logger.log(15, f"[GC] +!     Element {r} can be computed using {decomposition}")
                    ## we simplify the decomposition, avoiding loops
                    final_decomposition = len(bounds)*[0]
                    for i,v in enumerate(decomposition):
                        if isinstance(Goodearl_Basis[i], (list, tuple)):
                            for j in range(len(Goodearl_Basis[i])):
                                final_decomposition[j] += v*Goodearl_Basis[i][j]
                        elif Goodearl_Basis[i] is not None:
                            final_decomposition[i] += v
                    logger.log(15, f"[GC] +!     Element {r} is computed using {final_decomposition}")
                    Goodearl_Basis[r] = final_decomposition
        elif Goodearl_Basis[r] is None and current == bounds[r]: ## This should never be reached
            logger.log(15, f"[GC] ++ Reached bound for congruence class {r} (mod {n}): {current}")
            logger.log(15, f"[GC] ++     Computing decomposition with other elements of the basis...")
            decomposition = len(bounds)*[0]
            values = {v : i+1 for (i,v) in enumerate(bounds[1:]) if v < current}
            compositions = Compositions(current, min_part = min(values), max_part=max(values))
            for comp in compositions:
                if set(comp).issubset(values.keys()):
                    for v in comp:
                        decomposition[values[v]] += 1
                    break
            logger.log(15, f"[GC] ++     Element {r} can be computed using {decomposition}")
            ## we simplify the decomposition, avoiding loops
            final_decomposition = len(bounds)*[0]
            for i,v in enumerate(decomposition):
                if isinstance(Goodearl_Basis[i], (list, tuple)):
                    for j in range(len(Goodearl_Basis[i])):
                        final_decomposition[j] += v*Goodearl_Basis[i][j]
                elif Goodearl_Basis[i] is not None:
                    final_decomposition[i] += v
            Goodearl_Basis[r] = final_decomposition
        else:
            logger.log(15, f"[GC] ++ Skipping level {current} (congruence class {r}): ({Goodearl_Basis[r] is None} -- {current} -- {bounds[r]} -- {global_bound})")

        logger.log(15, f"[GC] -- Concluded study at level {current}")
        current += 1
    
    ## We change the first element to be the actual "constant" operator
    Goodearl_Basis[0] = L.parent().gen("z")[0]
    return L, Goodearl_Basis, level_flag

def __compute_bounds(n, *K, global_bound, ignore_bound=False):
    import heapq
    bounds = [0] + (n-1)*[None]
    queue = list(K)
    
    while queue:
        k = heapq.heappop(queue)
        r = k%n
        if bounds[r] is None or bounds[r] > k:
            bounds[r] = k
            for l in K:
                heapq.heappush(queue, k+l)

    ## Putting "global_bound" in those places where no bound was found
    for i in range(len(bounds)):
        if bounds[i] is None:
            bounds[i] = global_bound
        elif (not ignore_bound) and bounds[i] > global_bound:
            bounds[i] = global_bound
    
    return bounds
        
#################################################################################################
###
### METHODS TO OBTAIN EQUATIONS FROM TEMPLATES
###
#################################################################################################
@lru_cache
def GetEquationsForLevel(n: int, level: int,
        U: tuple | dict = None,
        simple: bool = False, maple: bool = False, 
        filename: str = None,
        path: str = "./results"
    ):
    r'''
        Method to compute conditions for a template to be of fixed `level`.

        The level of a monic differential operator in normal form of order `n` is the minimal order
        non-congruent with `n` such that there is an element of the centralizer. This is a very rare
        thing to happen.

        We ensure that the output are the conditions and remaining equations determines solutions
        that have exactly level `m`.
    '''
    L, P, conditions = GetEquationsForSolution(n, level, U, simple=simple, maple=maple, filename=filename, path=path)

    ## We filter for cases without solution
    filtered_conditions = conditions
    # for (sol_branch, lin_system, mons) in conditions:
    #     A = lin_system[:,:-1]
    #     b = lin_system[:,-1]

    #     if A.rank() == lin_system.rank():
    #         filtered_conditions.append((sol_branch, lin_system, mons))
    #     else:
    #         pass
    #         ## no solution -- we skip this branch

    ## We collect old solutions
    smaller_conditions = dict()
    for m in range(1, level):
        if m%n != 0:
            smaller_conditions[m] = GetEquationsForLevel(n, m, U, maple=maple)[2]
    
    ## We compare the solutions
    final_conditions = tuple(
        condition for condition in filtered_conditions 
        if all(
            not condition[0].is_subsolution(other[0]) for other in sum((list(v) for v in smaller_conditions.values()), [])
    ))      
    for (i,condition) in enumerate(filtered_conditions):
        if not condition in final_conditions:
            found_it = {k : any(condition[0].is_subsolution(other[0]) for other in smaller_conditions[k]) for k in smaller_conditions}
            logger.log(15, f"[GEFL] Solution already found in lower levels ({list(found_it.keys())}) [{i}]: {condition[0]}")     
            

    return L, P, final_conditions

@loglevel(logger)
def GetEquationsForSolution(n: int, m : int, U: list | dict = None, 
                            simple: bool = False, maple: bool = False, 
                            filename: str = None,
                            path: str = "./results"
) -> tuple[DPolynomial, DPolynomial, Ideal]:
    r'''
        Method to get the equations for a specific type of solutions for non-trivial commutator.

        This method computes the set of algebraic equations that need to be solved for obtaining
        a non-trivial commutator for a given linear differential operator in normal form. Recall that
        an operator in normal form is of the form

        .. MATH::

            L = \partial^n + a_{n-2} \partial^{n-2} + \ldots + a_1 \partial + a_0,

        where `a_*` are differential elements in some **differential field**. Its generic version
        is studied by Wilson and we can compute its basis of almost commuting operators (see method
        :func:`.almost_commuting.almost_commuting_wilson`)

        This method uses the almost commuting basis to create a linear combination of its elements
        up to a fixed order (given by `m`) and then compute all the algebraic equations that need to
        be satisfied for obtaining a non-trivial element of the centralizer of `L`.

        INPUT:

        * ``n``: provides the order of the operator `L` to be used.
          Then, the coefficients are given in the input ``U``, either as a list or as a dictionary.
        * ``m``: order bound for the commutator to be found.
        * ``U``: list or dictionary with the shape for the functions `a_{n-2},\ldots,a_0`. If given as a
          list, it is read as ``[a_0,\ldots,a_{n-2}]``. If given as a map, then it maps `i \mapsto a_i`.

        OUTPUT:

        A tuple `(L, P, H)` where `L` is the main operator we are looking for a commutator, `P` is a list 
        of the almost commuting operators used for building the commutator and `H` is an ideal or set of 
        conditions for `P` to commute with `L`.
    '''
    logger.debug(f"[GEFS] Getting the linear system associated for having a centralizer of order `m`")
    L, Ps, (Hs,mons) = GetHierarchyLinearEquations(n,m,U,tuple(i for i in range(m+1) if i%n != 0))

    ## Hs is a matrix with the linear equations -- each row is an equation
    if len(U) > 0: ## some information is given, we can do something else
        ## We make sure we take a ring of polynomials
        Hs = Hs.change_ring(Hs.parent().base_ring().base()) if Hs.parent().base_ring().is_field() else Hs
        ring = Hs.parent().base_ring()

        ###############################################################################
        ## COMPUTING THE IDEAL OF MINORS
        ###############################################################################
        ncols = Hs.ncols()
        nrows = Hs.nrows()

        total = binomial(nrows,ncols) # this is how many minors we need to compute
        total_10 = total//10
        final_ideal = []

        C = [[i for i in range(Hs.nrows()) if Hs[i][j] != 0] for j in range(Hs.ncols())]

        logger.debug(f"[GEFS] Rows for each column with non-zero elements:\n\t" + "\n\t".join(str(c) for c in C))

        if filename is not None:
            with open(f"{path}/{filename}_{n}_{m}_matrix.md", "w") as f:
                _matrix = ",\n".join(str(list(r)) for r in Hs)
                f.write(f"Matrix([\n{_matrix}\n])")
            with open(f"{path}/{filename}_{n}_{m}_rows.md", "w") as f:
                f.write(f"{mons}")

        ### COMPUTATION OPTION "simple"
        ### If we are in the simple mode, we only look to the last column. This is a simplification
        ### that may not give the complete set of equations. We use this to speed up the process
        ### of obtaining solutions.
        if not simple:
            for i,c in enumerate(Combinations(range(nrows), ncols)):
                if total_10 == 0 or i == total-1 or i % total_10 == 0: 
                    logger.debug(f"[GEFS] ++ Computing minor {i+1}/{total}... (Ideal with {len(final_ideal)} generators)")
                
                A_ = Hs.matrix_from_rows(c)
                det = A_.determinant()

                if det != 0: # there is something to add
                    final_ideal.append(det)
        else:
            logger.debug(f"[GEFS] Simple version: only looking to last columns")
            logger.warning(f"[GEFS] Simple version: results may not be complete")
            final_ideal = list(Hs[:,-1].column(0))

        logger.debug(f"[GEFS] -- Finished elimination of linear variables")
        ###############################################################################
        ## ANALYZING THE SOLUTION IDEAL
        ###############################################################################
        solutions = list()
        ### COMPUTATION OPTION "maple"
        ### If we are in the maple mode, we use the Maple software to compute the different
        ### solutions for the ideal system. This essentially create the equations in Maple 
        ### and then solve them using the "solve" command. If the ideal has dimension higher
        ### than zero, it may not obtain full solutions but some points.
        if maple and _HAS_MAPLE:
            logger.debug(f"[GEFS] Using Maple to solve the system")
            logger.warning(f"[GEFS] If the ideal has non-zero dimension, this may not provide full solutions")
            command = _generate_maple_command(final_ideal)
            if len(command) > 1000:
                from tempfile import NamedTemporaryFile
                with NamedTemporaryFile("w", delete=False) as tmp_file:
                    tmp_file.write(command)
                    tmp_file.close()
                    command = f'read "{tmp_file.name}";' 
                    output = Maple.eval(command)
            else:
                output = Maple.eval(command)
            for solution_branch in _parse_maple_output(output, ring):
                solutions.extend(analyze_ideal(solution_branch, dict(), list()))
        else:
            final_ideal = ideal(ideal(final_ideal).groebner_basis()) if len(final_ideal) > 0 else ideal(ring)

            for primary in final_ideal.primary_decomposition():
                solutions.extend(analyze_ideal(primary.radical(), dict(),list()))

        ## We now evaluate the equations to get the remaining linear equations
        output = list()
        for solution in solutions:
            system = Matrix([[solution.eval(el) for el in row] for row in Hs])
            if system == 0:
                system = system[0,:] ## The matrix was the zero, we keep just one row
            else:
                system = Matrix([row for row in system if row != 0])
            output.append((solution, system, mons))
        return L, Ps, tuple(output)
    else:
        return L, Ps, Hs

def GetHierarchyLinearEquations(n: int, m : int,
        U: list | dict = None, c_list: list = None):
    r'''
        Method to compute the linear system induced by the hierarchy of an operator.

        Let `L` be a differential operator in normal form of order `n`. We know that if there 
        is another operator `Q_m` of order `m` that commutes with `L`, it is a linear combination
        of the Wilson basis of almost commuting operators for `L`.

        In general, if we write:

        .. MATH::

            Q = \sum_{i=0}^{m} c_i P_i,

        where `P_i` are the basic operators of the almost commuting basis, then we know that
        `[L, P_i] = H_{i,0} + H_{i,1}\partial + \ldots + H_{i,n-2}\partial^{n-2}`, so, for `Q`
        to commute with `L` we need that, for all `j = 0,\ldots, n-2`:

        .. MATH::

            c_0 H_{0,j} + c_1 H_{1,j} + \ldots + c_m H_{m,j} = 0.

        This is a linear system in `m+1` variables in the field of coefficients of `L`.

        This method computes the best possible linear system induced for an operator of
        order `n` when we look for an element in the centralizer of order at most `m`.

        INPUT:

        * ``m``: bound for the order of the element in the centralizer.
        * ``n``: order of the operator `L`.
        * ``U``: list or dictionary of the coefficients of `L` such that `[\partial^i]L = U[i]`.
        * ``c_list`` (optional): list of constants to be considered in the sum for the linear system.
          If not provided, we consider all constants possible.

        OUTPUT:

        A tuple `(L,(P_j), (S, m))`, where `L` is the operator `L` for which we are computing the 
        conditions for an element in the centralizer, `P_j` are the operator in the almost commuting 
        basis such that when added with a solution of `S` we obtain an element in the centralizer of 
        `L`. This system `S` will be given in matrix form where the columns are indexed by the 
        constants `c_i`, `i` going through the input ``c``. We include the tuple `m` of "monomials" 
        used to index the rows of `S`.
    '''
    ## Converting the input so it can be cached
    ### Coefficients of the operator `L`
    if not isinstance(U, dict):
        U = {i: U[i] for i in range(len(U))}
    U = tuple(sorted(U.items()))

    ### Elements of c
    if c_list is None:
        c_list = range(m+1)
    c_list = tuple(sorted(i for i in c_list if i >= 0 and i <= m)) ## remove bad elements - c_list is sorted now

    ## We return the cached result with these keys
    return _GetHierarchyLinearEquations(n,m,U,c_list)

@lru_cache
def _GetHierarchyLinearEquations(n: int, m: int, U: tuple, c_list: tuple):
    logger.debug(f"[GHLE] Calling method with {n=}, {m=}, {U=}, {c_list=}")
    ## Checking correctness of arguments
    if n not in ZZ or n < 2:
        raise ValueError(f"[GHLE] The value for `n` must be an integer greater than 1")
    if m not in ZZ:
        raise ValueError(f"[GHLE] The value for `m` must be an integer")
    if U is None:
        logger.warning(f"[GHLE] No values for `U` provided. Impossible to get algebraic equations.")
    U = dict(U)
    if any(el not in ZZ for el in U.keys()) or min(U.keys()) < 0 or max(U.keys()) > n-2:
        raise KeyError(f"[GHLE] The argument ``U`` as dictionary must have integers as keys between 0 and `n-2` ({n-2})")
    
    ## Analyzing the functions in ``U``
    logger.debug(f"[GHLE] Computing common parent for the ansatz functions")
    parent_us = reduce(lambda p, q: pushout(p,q), (parent(v) for v in U.values()), QQ)
    if parent_us not in _DRings:
        raise TypeError(f"[GHLE] We need the coefficient of `L` to be in a differential ring/field")
    
    ### Computing the generic `L` operator
    logger.debug(f"[GHLE] Computing the generic L_{n} operator...")
    L = generic_normal(n)#, output_base=parent_us)
    z = L.parent().gen("z")
    parent_L_with_us = L.parent()
    logger.debug(f"[GHLE] {L=}")

    U = {L.coefficient_full(z[i]).infinite_variables()[0]: parent_us(U.get(i,0)) for i in U} # Dictionary to evaluate generic polynomials
    L = L(dic=U) # parent now without any u variable

    ### Computing the almost commuting basis up to order `m` and the hierarchy up to this point
    logger.debug(f"[GHLE] ++ Computing the basis of almost commuting and the hierarchies...")
    Ps, Hs = list(), list() # [z[0](dic=U)], [(n-1)*[L.parent().zero()]] # the case with m = 0
    for i in c_list:
        nP, nH = almost_commuting_wilson(n, i)
        #nP = parent_L_with_us(nP) # casting to have the ring of the Us
        #nH = tuple(parent_L_with_us(h) for h in nH) # casting to have the ring of the Us
        
        Ps.append(nP(dic=U))
        Hs.append([h(dic=U) for h in nH])

        logger.debug(f"[GHLE]    Computed for order {i}")

    logger.debug(f"[GHLE] -- Computed the basis of almost commuting and the hierarchies")

    system_in_DRing = [[Hs[j][i] for j in range(len(c_list))] for i in range(n-1)]
    extended_system = parent_us.system_for_constant_solutions(system_in_DRing)
    logger.debug(f"[GHLE] -- Computed extended system")

    return L, Ps, extended_system
    # ### Getting the linear system. We use the method extract on the Hs to get the monomials and the coefficients
    # ### for each section of the Hs
    # ## We compute the lcm of the denominators of the elements by columns
    # D = [Hs[0][i].lcm_denominators(*[Hs[j][i] for j in range(1,len(Hs))]) for i in range(n-1)]

    # if len(U) > 0: ## Some information is given
    #     rows = list()
    #     mons = list()
    #     for j in range(n-1):
    #         equs = dict()
    #         for i,c in enumerate(c_list):
    #             for (mon, coeff) in extract(D[j]*Hs[i][j]):
    #                 if not mon in equs:
    #                     equs[mon] = dict()
                    
    #                 equs[mon][c] = coeff
    #         rows.extend([[equs[mon].get(c, 0) for c in c_list] for mon in equs])
    #         mons.extend((j,mon) for mon in equs)
        
    #     return L, Ps, (Matrix(rows), tuple(mons))
    # else: ## simple approach
    #     return L, Ps, (Matrix(Hs), tuple([(i,1) for i in range(n-1)]))

#################################################################################################
###
### SPECIAL CASES
###
#################################################################################################
@loglevel(logger)
def PolynomialCommutator(n: int, m: int, d: int, force_level: bool = False) -> tuple[DPolynomial, DPolynomial, Ideal]:
    logger.debug(f"[PolyComm] Computing equations for polynomial commutators for L_{n} up to order {m} and degree {d}.")
    logger.debug(f"[PolyComm] --- Generating the ansatz polynomials...")
    U = generate_polynomial_ansatz(QQ, n, d)
    logger.debug(f"[PolyComm] --- Generated the ansatz functions:\n\t{U=}")
    logger.debug(f"[PolyComm] --- Computing the equations necessary for the ansatz to commute with L_{n}...")
    if not force_level:
        L, P, H = GetEquationsForSolution(n, m, U)
    else:
        L, P, H = GetEquationsForLevel(n,m, U)
    return L,P,H

#################################################################################################
###
### METHODS TO GENERATE TEMPLATES
###
#################################################################################################
def generate_polynomial_ansatz(base, n: int, d: int, var_name: str = "x", ansatz_var: str = "b") -> list[DPolynomial]:
    r'''
        Generate a list of ansatz for the generic `u` for a generic Schrödinger operator of order `n`

        INPUT:

        * ``base``: the base ring of constants to be used.
        * ``n``: the order of the Schrödinger operator to be considered.
        * ``d``: degree of the ansatz generated
        * ``var_name``: name of the variable to be used as a polynomial element. We will make its derivative to be `1`.
    '''
    logger.debug(f"[GenPolyAn] Generating the variables for the constant coefficients and the polynomial variable")
    var_names = [f"{ansatz_var}_{i}_{j}" for i in range(n-1) for j in range(d+1)] + [var_name]
    logger.debug(f"[GenPolyAn] Creating the differential ring for the ansatz...")
    base = PolynomialRing(base, var_names)
    base_diff = DifferentialRing(base, lambda p : diff(p, base(var_name)))
    logger.debug(f"[GenPolyAn] {base_diff=}")

    logger.debug(f"[GenPolyAn] Creating the list of functions that will act as U's...")
    B = [[base_diff(f"{ansatz_var}_{i}_{j}") for j in range(d+1)] for i in range(n-1)]
    X = [base_diff(var_name)**j for j in range(d+1)]

    logger.debug(f"[GenPolyAn] Returning the ansatz functions")
    return [sum(b*x for (b,x) in zip(row, X)) for row in B]

#################################################################################################
###
### METHODS TO EXTRACT EQUATIONS
###
#################################################################################################
def generate_polynomial_equations(H: DPolynomial, var_name: str = "x") -> list[Polynomial]:
    r'''Method to extract equations assuming a polynomial ansatz'''
    logger.debug(f"[GenPolyEqus] Getting equations (w.r.t. {var_name}) from: H={repr(H)[:20]}...")
    B = H.parent().base()
    # We remove the diff. variable and the diff. structure remaining only the ansatz variables and the polynomial variable
    H = H.coefficients()[0].numerator().wrapped if isinstance(B, DFractionField) else H.coefficients()[0].wrapped
    B = parent(H) # this is the algebraic structure

    if B.is_field() and B != QQ: # field of fractions of polynomials
        x = B.base()(var_name) # this is the polynomial variable that will be removed
        H = H.numerator().polynomial(x)    
    else:
        x = B(var_name) # this is the polynomial variable that will be removed
        H.polynomial(x)

    output = tuple(zip(reversed(H.monomials()), H.coefficients()))
    
    return output

#################################################################################################
###
### METHODS TO ANALYZE CENTRALIZERS
###
#################################################################################################
class GDH_Solution:
    def __init__(self, case: SolutionBranch, gen: DPolynomialGen, L: DPolynomial, centr_GB: tuple[DPolynomial], flag: tuple[Element]):
        from sage.arith.misc import GCD

        self.__gen = gen
        self.__L = L
        self.__centralizer_basis = centr_GB
        self.__flag = flag
        self.__case = case

        ## Order of the operator L
        self.__n = L.order(gen)

        ## Orders of the elements in the centralizer
        self.__orders = None
        ## TeX code for the operators in the centralizer
        self.__operators_tex = None
        ## Goodearl's basis for the Centralizer as C[L]-module
        self.__alg_gens = len([el for el in centr_GB if not isinstance(el, list)])
        ## Rank of the centralizer (computed so far)
        self.__rank = GCD([self.n] + [el for el in self.orders if el is not None])

    @staticmethod
    def Error(case: SolutionBranch, L:DPolynomial) -> GDH_Solution:
        gen = L.parent().gen("z")
        centr = L.order(gen)*[None]
        flag = L.order(gen)*[0]
        return GDH_Solution(case, gen, L, centr, flag)

    @property
    def gen(self) -> DPolynomialGen:
        return self.__gen
    @property
    def L(self) -> DPolynomial:
        return self.__L
    @property
    def n(self) -> int:
        return self.__n
    @property
    def basis(self) -> tuple[DPolynomial]:
        return self.__centralizer_basis
    @property
    def flag(self) -> tuple[Element]:
        return self.__flag
    @property
    def orders(self) -> tuple[int]:
        if self.__orders is None:
            if self.is_error():
                return tuple(self.n*[-1])
            else:
                self.__orders = [
                    el.order(self.gen) if not isinstance(el, list) else 
                    sum(el[k]*self.basis[k].order(self.gen) for k in range(self.n) if el[k] != 0)
                for el in self.basis]
        return self.__orders
    @property
    def operators_tex(self) -> tuple[str]:
        if self.__operators_tex is None:
            self.__operators_tex = [
                latex(el) if not isinstance(el, list) 
                else ''.join(f'A_{k}^{"" if el[k] == 1 else el[k]}' for k in range(self.n) if el[k] != 0)
            for el in self.basis]
        return self.__operators_tex
    
    def relations(self) -> str:
        relations = []
        for i,el in enumerate(self.basis):
            if isinstance(el, list):
                relations.append(f"A_{i} - {self.operators_tex[i]}")
        return ", ".join(relations)

    @property
    def algebraic_generators(self) -> int:
        return self.__alg_gens
    @property
    def rank(self) -> int:
        return self.__rank    
    
    def are_similar(self, other: GDH_Solution) -> bool:
        r'''
            Method to check if two solutions are similar.

            We consider two solutions to be similar if they have the same orders in the generators
            of the Goodearl's basis.
        '''
        return self.orders == other.orders
        
    def is_error(self) -> bool:
        return all(el is None for el in self.__centralizer_basis)
    
    def point_case(self) -> tuple[Element]:
        
        if len(self.__case.remaining_variables()) == 0:
            return tuple(v for (_,v) in sorted(self.__case._SolutionBranch__solution.items()))
        
        return ("Unknown",)

def AnalyzeGDH(n: int, m: int, 
               L: DPolynomial, 
               H: tuple[tuple[SolutionBranch]], 
               Hs: dict[int, tuple[tuple[SolutionBranch]]],
               filename: str = None, 
               path : str = "./results",
               table: bool = False
) -> tuple[tuple[tuple[int,SolutionBranch]], tuple[GDH_Solution]]:
    r'''
        Method to analyze the centralizer of different branches of solutions.

        This method analyzes a specific case where the G.D. hierarchies has been computed for a given set of values 
        `n` and `m`. This method will compute all solution branches that provide non-trivial centralizers of 
        true level `m` and then it computes the centralizer for each of these branches.

        The results are stored in a text file where all the computations (getting the branches and computing centralizers)
        will be summarized.

        INPUT: 

        * `n`: the order of the base operator `L` for which we are looking the centralizer.
        * `m`: the true level we are looking for.
        * `filename`: the name of the file where the results will be stored. This file will be stored in the path
          given by the argument `path`.
        * `L`: the actual operator we are working with. It may have some unknowns that will be solved as a first step
          before the analysis of the centralizer.
        * `H`: branches of the G.D. hierarchy of the operator `L` of order `m`.
        * `Hs`: branches of the G.D. hierarchies of the operator `L` up to order `m`.
        * `path`: (optional) the path where the result file will be stored.

        OUTPUT: 

        A tuple with the cases we found and the solution for each of the cases.
    '''
    with open(f"{path}/{filename}_{n}_{m}_report.md", "w") if filename else nullcontext() as file:
        if filename: file.writelines([f"# ANALYZING CASE ${n=}$, ${m=}$ FOR THE {filename.upper()} COEFFICIENTS\n"])
        logger.info("###############################################################################")
        logger.info(f"# ANALYZING CASE {n=}, {m=} FOR THE {filename.upper()} COEFFICIENTS")
        logger.info("###############################################################################")
        cases = __general_analysis(H, {i: Hs[i] for i in range(m) if i%n != 0}, file=file) 
        cases = sorted(cases, key=lambda case : sum((sum(abs(el) for el in p.coefficients()) if p not in QQ else abs(QQ(p))) for p in case[1][0]._SolutionBranch__solution.values()))
    
        if filename: file.writelines(["## CENTRALIZERS CASE BY CASE:\n"])
        logger.info("###############################################################################")
        logger.info("## CENTRALIZERS CASE BY CASE:")
        logger.info("###############################################################################")
        computed : list[GDH_Solution] = list() 
        for i, case in enumerate(cases): 
            if filename: file.writelines([f"### Starting case {i+1}/{len(cases)}:\n",f"* Branch: ${latex(case[1][0])}$\n"])
            logger.info(f"@@ Starting case {i+1}/{len(cases)}: {case[1][0]}")
            try:
                computed.append(GDH_Solution(case[1][0], *__analyze_centralizer(case[1][0], L, m)))
                logger.info(f"[{','.join(f'{computed[-1].orders[i] if not isinstance(computed[-1].basis[i], (tuple,list)) else computed[-1].basis[i]}' for i in range(len(computed[-1].basis)))}]")
                
                if filename: 
                    file.writelines(
                        [f"* Operator: ${latex(computed[-1].L)}$\n", 
                        f"* Flag: ${latex(computed[-1].flag)}$\n",
                        f"* Algebraic generators: {computed[-1].algebraic_generators}\n",
                        f"* Found rank: {computed[-1].rank}\n",
                        "* Centralizer:\n"] + 
                        [f"  - (${j}$ -- ${computed[-1].orders[j]}$) $G_{j} = {computed[-1].operators_tex[j]}$\n" for j in range(len(computed[-1].basis))] + 
                        [f"* Orders: ${latex(computed[-1].orders)}$\n"]
                    )
            except (KeyboardInterrupt, RecursionError) as error:
                try:
                    if isinstance(error, RecursionError):
                        with open(f"{path}/{filename}_{n}_{m}_error.md", "w") as f:
                            f.writelines([f"ERROR: {error}\n",f"{error.__traceback__}\n"])
                        computed.append(GDH_Solution.Error(case[1][0], L))
                    logger.info(f"@@ Case stopped by {error}... Waiting {5} seconds before continuing")
                    if filename: file.writelines([f"* Case stopped by {error}\n"])
                    sleep(5)
                except KeyboardInterrupt:
                    break
            if filename: file.flush()

        if table:
            __generate_table(cases, computed, f"{filename}_{n}_{m}_table.tex", path, file)

        return cases, computed
    
def __general_analysis(
        branches: tuple[SolutionBranch], 
        prev_branches: dict[int,tuple[SolutionBranch]], 
        vars_not_all_zero: list[str] = [], 
        file = None
) -> list[tuple[int, tuple[SolutionBranch]]]:
    if file: file.writelines([f"## CHECKING VALIDITY OF SOLUTIONS AT THIS LEVEL\n"])
    valid = list()
    vars_not_all_zero = [vars_not_all_zero] if not isinstance(vars_not_all_zero, (list,tuple)) else vars_not_all_zero
    for (i,h) in enumerate(branches):
        if file: file.writelines([f"* Checking case {i}: (${latex(h[0])}$) include any solution for a lower level\n"])
        logger.info(f"Checking case {i}: ({h[0]}) include any solution for a lower level")
        if len(vars_not_all_zero) > 0 and all(h[0][a_name] == 0 for a_name in vars_not_all_zero):
            if file: file.writelines([f"  Invalid branch\n"])
            logger.log(15, f"  + Invalid branch")
        else:
            is_valid = True
            for (k,v) in prev_branches.items():
                if file: file.writelines([f"  - Checking the cases for level {k}:\n"])
                logger.log(15, f"  - Checking the cases for level {k}:")
                for h2 in v:
                    if len(vars_not_all_zero) == 0 or any(h2[0][a_name] != 0 for a_name in vars_not_all_zero):
                        is_valid = is_valid and (not h2[0].is_subsolution(h[0]))
                        if file: file.writelines(f"    [{f'{h2[0].is_subsolution(h[0])}'.ljust(len('False'),' ')}] - ${latex(h2[0])}$\n")
                        logger.log(15, f"    [{f'{h2[0].is_subsolution(h[0])}'.ljust(len('False'),' ')}] - {h2[0]}")
                    else:
                        if file: file.writelines([f"    [Invalid] ${latex(h2[0])}$\n"])
                        logger.log(15, f"    [Invalid] {h2[0]}")
                logger.log(15, f"  -----------------------------------")
            if is_valid:
                if file: file.writelines([f"  Adding new branch to total valid branches\n"])
                logger.info(f"  Adding new branch to total valid branches")
                valid.append((i,h))
        logger.info(f"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
    return valid

def __analyze_centralizer(branch: SolutionBranch, L: DPolynomial, M: int,B: int=None, **kwds):
    B = M if B is None else B
    
    specific_solution = branch if len(kwds) == 0 else branch.subsolution(**kwds)
    L = specific_solution.eval(L)
    Z = L.parent().gen("z")
    Us = tuple([0 if L.coefficient_full(Z[i]) == 0 else L.coefficient_full(Z[i]).coefficients()[0] for i in range(L.order(Z)-1)])

    logger.log(15, f"[Analyze] Analyzing the centralizer for the operator {L} with solution {specific_solution}\n\t-{L.parent()}\n\t-{Us}")
    L, centr_GB, flag = GetCentralizer(
        Us, B, 
        starting_level=M, update_bound=True, ignore_bound=True, 
        extra_info=specific_solution
    )

    return Z, L, centr_GB, flag

def __generate_table(
        cases: list[tuple[int, tuple[SolutionBranch]]], 
        computed: list[GDH_Solution], 
        filename: str, 
        path: str,
        file: TextIO):
    ## We merge the cases that are similar
    final_cases: list[tuple[GDH_Solution,list[GDH_Solution]]] = []
    for (case, comp) in zip(cases, computed):
        for i,(final_case, related) in enumerate(final_cases):
            if comp.are_similar(final_case):
                final_cases[i] = (final_case, related + [comp])
                break
        else:
            final_cases.append((comp,[comp]))
    
    ## Creating the TeX table
    with open(f"{path}/{filename}", "w") as f:
        f.writelines([
            r"\begin{table}[h]" + "\n",
            "\t" + r"\centering" + "\n",
            "\t" + r"$\begin{array}{|c|c|c|c|}" + "\n",
            "\t\t" + r"\hline" + "\n",
            "\t\t" + r"\text{Family} & \text{\# Cases} & \text{Orders} & \text{Found Relations} \\" + "\n",
            "\t\t" + r"\hline" + "\n",
        ])
        for i,(case, related) in enumerate(final_cases):
            f.writelines([
                f"\t\t{i+1} & {len(related)} & {tuple(case.orders[1:])} & {case.relations()} \\\\" + "\n",
            ])
        f.writelines([
            "\t\t" + r"\hline" + "\n",
            "\t" + r"\end{array}$" + "\n",
            r"\end{table}" + "\n",
        ])
    
    ## Updating the report file with the summary
    file.writelines(["## SUMMARY OF THE CASES (by FAMILIES):\n"])
    for (i, (_, related)) in enumerate(final_cases):
        file.writelines([f"### Family {i+1}:\n",
                         f"* Number of cases: {len(related)}\n",
                         f"* Orders: {tuple(related[0].orders[1:])}\n",
                         f"* Relations: {related[0].relations()}\n",
                         f"* Points: " + r"$\left\{" +  ", ".join(f"{p.point_case()}" for p in related) + r"\right\}$" + "\n"
        ])

__all__ = [
    "GetCentralizer", "GetEquationsForLevel", "GetHierarchyLinearEquations", "PolynomialCommutator",
    "generate_polynomial_ansatz",
    "generate_polynomial_equations",
    "AnalyzeGDH"
]