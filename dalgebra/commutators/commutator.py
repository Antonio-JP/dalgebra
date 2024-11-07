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
logger = logging.getLogger(__name__)

from functools import reduce, lru_cache

from sage.calculus.functional import diff
from sage.categories.pushout import pushout
from sage.combinat.combination import Combinations
from sage.functions.other import binomial
from sage.matrix.constructor import Matrix
from sage.rings.ideal import Ideal_generic as Ideal, Ideal as ideal
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element_generic import Polynomial
from sage.rings.rational_field import QQ
from sage.structure.element import parent

from typing import Callable

from ..dring import DRings, DifferentialRing, DFractionField
from ..dpolynomial.dpolynomial import DPolynomial
from ..logging.logging import loglevel
from .almost_commuting import generic_normal, almost_commuting_wilson
from .ideals import analyze_ideal, eliminate_linear_variables

_DRings = DRings.__classcall__(DRings)

#################################################################################################
###
### METHODS TO OBTAIN EQUATIONS FROM TEMPLATES
###
#################################################################################################
@lru_cache
def GetEquationsForLevel(n: int, level: int,
        U: tuple | dict = None, *,
        extract: Callable[[Polynomial], list[Polynomial]],
    ):
    r'''
        Method to compute conditions for a template to be of fixed `level`.

        The level of a monic differential operator in normal form of order `n` is the minimal order
        non-congruent with `n` such that there is an element of the centralizer. This is a very rare
        thing to happen.

        We ensure that the output are the conditions and remaining equations determines solutions
        that have exactly level `m`.
    '''
    L, P, conditions = GetEquationsForSolution(n, level, U, extract=extract)

    n = L.order(L.parent().gen("z"))

    ## We filter for cases without solution
    filtered_conditions = list()
    for (sol_branch, lin_system) in conditions:
        try:
            lin_system[:,:-1].solve_right(-lin_system[:,-1])
            filtered_conditions.append((sol_branch, lin_system))
        except ValueError:
            ## no solution -- we skip this branch
            pass

    ## We collect old solutions
    smaller_conditions = tuple()
    for m in range(1, level):
        if m%n != 0:
            smaller_conditions += GetEquationsForLevel(n, m, U, extract=extract)[2]
    
    ## We compare the solutions
    final_conditions = tuple(
        condition for condition in filtered_conditions 
        if all(
            not condition[0].is_subsolution(other[0]) for other in smaller_conditions
    ))            

    return L, P, final_conditions

@loglevel(logger)
def GetEquationsForSolution(n: int, m : int, U: list | dict = None, *,
        extract: Callable[[Polynomial], list[Polynomial]]) -> tuple[DPolynomial, DPolynomial, Ideal]:
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

        Since the way the algebraic equations arises from the almost commuting basis and the operator
        `L` depends on the differential field over which `L` is defined, we require a method
        ``extract`` that can obtain, for a given element in the differential field, a list of
        equations that guarantee the element to vanish.

        INPUT:

        * ``n``: provides the order of the operator `L` to be used.
          Then, the coefficients are given in the input ``U``, either as a list or as a dictionary.
        * ``m``: order bound for the commutator to be found.
        * ``U``: list or dictionary with the shape for the functions `a_{n-2},\ldots,a_0`. If given as a
          list, it is read as ``[a_0,\ldots,a_{n-2}]``. If given as a map, then it maps `i \mapsto a_i`.
        * ``extract``: a method to extract from the final set of values the equations for
          the obtained operator to actually commute. These equations will include any variable
          within the given functions ``U`` and the flag of constants created.

        OUTPUT:

        A tuple `(L, P, H)` where `L` is the main operator we are looking for a commutator, `P` is a list 
        of the almost commuting operators used for building the commutator and `H` is an ideal or set of 
        conditions for `P` to commute with `L`.
    '''
    logger.debug(f"[GEFS] Getting the linear system associated for having a centralizer of order `m`")
    L, Ps, Hs = GetHierarchyLinearEquations(n,m,U,tuple(i for i in range(m+1) if i%n != 0),extract=extract)

    ## Hs is a matrix with the linear equations -- each row is an equation
    if len(U) > 0: ## some information is given, we can do something else
        ## We make sure we take a ring of polynomials
        Hs = Hs.change_ring(Hs.parent().base_ring().base()) if Hs.parent().base_ring().is_field() else Hs
        ring = Hs.parent().base_ring()

        ###############################################################################
        ## COMPUTING THE IDEAL OF MINORS
        ###############################################################################
        n = Hs.ncols()
        m = Hs.nrows()

        total = binomial(m,n) # this is how many minors we need to compute
        total_10 = total//10
        total_100 = total//100
        final_ideal = ideal(ring)

        C = [[i for i in range(Hs.nrows()) if Hs[i][j] != 0] for j in range(Hs.ncols())]

        logger.debug(f"[GEFS] Rows for each column with non-zero elements:\n\t" + "\n\t".join(str(c) for c in C))
        print(f"[GEFS] Rows for each column with non-zero elements:\n\t" + "\n\t".join(str(c) for c in C), flush=True)
        for i,c in enumerate(Combinations(range(m), n)):
            if total_10 == 0 or i == total-1 or i % total_10 == 0: 
                logger.debug(f"[GEFS] ++ Computing minor {i+1}/{total}... (Ideal with {final_ideal.ngens()} generators)")
            if total_100 == 0 or i == total-1 or i % total_100 == 0:
                print(f"[GEFS] ++ Computing minor {i+1}/{total}... (Ideal with {final_ideal.ngens()} generators)", end="\r", flush=True)
            
            A_ = Hs.matrix_from_rows(c)
            red_det = final_ideal.reduce(A_.determinant())

            if red_det != 0: # there is something to add
                final_ideal = ideal(ideal(final_ideal.gens() + (red_det,)).groebner_basis())
                if 1 in final_ideal:
                    break
        print("\n[GEFS] -- Finished the computation of minors")
                
        logger.debug(f"[GEFS] -- Finished elimination of linear variables")
        ###############################################################################
        ## ANALYZING THE SOLUTION IDEAL
        ###############################################################################
        solutions = list()
        for primary in final_ideal.primary_decomposition():
            solutions.extend(analyze_ideal(primary.radical(), dict(),list()))

        ## We now evaluate the equations to get the remaining linear equations
        output = list()
        for solution in solutions:
            system = Matrix([[solution.eval(el) for el in row] for row in Hs])
            output.append((solution, system))
        return L, Ps, tuple(output)
    else:
        return L, Ps, Hs

def GetHierarchyLinearEquations(n: int, m : int,
        U: list | dict = None, c_list: list = None,
        *,
        extract: Callable):
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

        This is a linear system in `m+1` variables in the field of coefficients of `L`. In 
        order to compute a solution with constants, we need some extra information on the structure
        of these coefficients (see method ``extract`` in the input)

        This method computes the best possible linear system induced for an operator of
        order `n` when we look for an element in the centralizer of order at most `m`.

        INPUT:

        * ``m``: bound for the order of the element in the centralizer.
        * ``n``: order of the operator `L`.
        * ``U``: list or dictionary of the coefficients of `L` such that `[\partial^i]L = U[i]`.
        * ``c_list`` (optional): list of constants to be considered in the sum for the linear system.
          If not provided, we consider all constants possible.
        * ``extract``: method to get a real set of equations for an element of the field of 
          coefficients for `L` to be equal to zero.

        OUTPUT:

        A tuple `(L,(P_j), S)`, where `L` is the operator `L` for which we are computing the 
        conditions for an element in the centralizer, `P_j` are the operator in the almost commuting 
        basis such that when added with a solution of `S` we obtain an element in the centralizer of 
        `L`. This system `S` will be given in matrix form where the columns are indexed by the 
        constants `c_i`, `i` going through the input ``c``.
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
    return _GetHierarchyLinearEquations(n,m,U,c_list,extract)

@lru_cache
def _GetHierarchyLinearEquations(n: int, m: int, U: tuple, c_list: tuple, extract: Callable):
    print(f"[GHLE] Calling method with {n=}, {m=}, {U=}, {c_list=}")
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

    if extract is not None and not callable(extract):
        raise TypeError(f"[GHLE] The argument ``extract`` must be a callable or `None`")
    
    ## Analyzing the functions in ``U``
    logger.debug(f"[GHLE] Computing common parent for the ansatz functions")
    parent_us = reduce(lambda p, q: pushout(p,q), (parent(v) for v in U.values()), QQ)
    if parent_us not in _DRings:
        raise TypeError(f"[GHLE] We need the coefficient of `L` to be in a differential ring/field")
    
    ### Computing the generic `L` operator
    logger.debug(f"[GHLE] Computing the generic L_{n} operator...")
    L = generic_normal(n, output_base=parent_us)
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
        nP = parent_L_with_us(nP) # casting to have the ring of the Us
        nH = tuple(parent_L_with_us(h) for h in nH) # casting to have the ring of the Us
        
        Ps.append(nP(dic=U))
        Hs.append([h(dic=U) for h in nH])

        logger.debug(f"[GHLE]    Computed for order {i}")

    logger.debug(f"[GHLE] -- Computed the basis of almost commuting and the hierarchies")

    ### Getting the linear system. We use the method extract on the Hs to get the monomials and the coefficients
    ### for each section of the Hs
    if len(U) > 0: ## Some information is given
        rows = list()
        for j in range(n-1):
            equs = dict()
            for i,c in enumerate(c_list):
                for (mon, coeff) in extract(Hs[i][j]):
                    if not mon in equs:
                        equs[mon] = dict()
                    
                    equs[mon][c] = coeff
            rows.extend([[equs[mon].get(c, 0) for c in c_list] for mon in equs])
        
        return L, Ps, Matrix(rows)
    else: ## simple approach
        return L, Ps, Matrix(Hs)

@loglevel(logger)
def PolynomialCommutator(n: int, m: int, d: int) -> tuple[DPolynomial, DPolynomial, Ideal]:
    logger.debug(f"[PolyComm] Computing equations for polynomial commutators for L_{n} up to order {m} and degree {d}.")
    logger.debug(f"[PolyComm] --- Generating the ansatz polynomials...")
    U = generate_polynomial_ansatz(QQ, n, d)
    logger.debug(f"[PolyComm] --- Generated the ansatz functions:\n\t{U=}")
    logger.debug(f"[PolyComm] --- Computing the equations necessary for the ansatz to commute with L_{n}...")
    L, P, H = GetEquationsForSolution(n, m, U, extract=generate_polynomial_equations)
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


__all__ = [
    "GetEquationsForLevel", "GetHierarchyLinearEquations", "PolynomialCommutator",
    "generate_polynomial_ansatz",
    "generate_polynomial_equations"
]