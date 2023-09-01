r'''
    Generic almost-commutators and integrable hierarchies.

    This module contains the main functionality to compute the generic almost commutators of linear differential 
    operators. This is based on the work of G. Wilson: "Algebraic curves and soliton equations" in *Geometry today 60*, **1985**,
    pp. 303-239.

    This software has been used in the presentation in ISSAC'23 "Computing almost-commuting basis of Ordinary Differential
    Operators", by A. Jiménez-Pastor, S.L. Rueda and M.A. Zurro in Tromsø, Norway.

    
    **Theory explanation**
    -----------------------------------------

    Let us consider an algebraically closed field of characteristic zero `C` and the field of d-polynomials defined by `n-2` 
    differential varuables `u_0,\ldots,u_{n-2}`. Let us consider the linear differential operator:


    .. MATH::

        L = \partial^n + u_{n-2}\partial^{n-2}  + \ldots + u_1\partial + u_0.

    This operator `L` can be written in terms of d-polynomilas in the ring `K\{z\} = C\{u_0,\ldots,u_{n-2},z\}`. We say that 
    another operator `P \in K\{z\}` *almost commutes with `L`* if and only if the commutator of `L` with `P` (`[L,P]`) has order
    at most `\text{ord}(L) - 2`. 

    In general, the order of `[L,P]` is `\text{ord}(L) + \text{ord}(P) - 1`. Hence, in order to obtain a specific order of at most `\text{ord}(L) - 2`
    we need that the coefficients of `P` satisfy `ord(P) + 1` conditions. 

    It was shown in the article by G. Wilson that, if we set `w(u_i) = n-i`, then for every `m \in \mathbb{N}` there is a unique
    operator `P_m \in K\{z\}` in normal form of order `m` (i.e, `P_m = z^{(m)} + p_{2}z^{(m-2)} + \ldots + p_m`) such that

    * The coefficient `p_i` is homogeneous of weight `i`.
    * `P_m` alsmost commutes with `L`.

    If we consider all the `P_m`, we obtain a basis of the operators that almost commute with `L`. Moreover, the remaining coefficients
    of `[L,P_m]` provide extra differential conditions that the coefficients of `P_m` have to satisfy in order to have an actual 
    commutator of `L`. These sequences of conditions are called **integrable hierarchies** for a given value of `n = ord(L)`.

    This module provides algorithms and methods to quickly generate the hierarchies in a method :func:`almost_commuting_schr`, which takes
    the values for `n = \text{ord}(L)` and `m = \text{ord}(P_m)` and computes the `m`-th step in the corresponding hierarchy. Let us 
    show one example when we consider `L` of order 3 and `P_5` of order 5::

        sage: from dalgebra import *
        sage: from dalgebra.hierarchies import *
        sage: n = 3; m = 5 # Preparing variables for an example
        sage: R = DifferentialPolynomialRing(QQ, [f"p{i+2}" for i in range(m-1)] + [f"u{i}" for i in range(n-1)] + ["z"])
        sage: p,u,z = R.gens()[:m-1], R.gens()[m-1:m+n-2], R.gens()[-1]
        sage: L = z[n] + sum(z[i]*u[i][0] for i in range(n-1))
        sage: P = z[m] + sum(z[m-i]*p[i-2][0] for i in range(2,m+1))
        sage: L
        u0_0*z_0 + u1_0*z_1 + z_3
        sage: P
        p2_0*z_3 + p3_0*z_2 + p4_0*z_1 + p5_0*z_0 + z_5

    Now we can compute the commutator `[L, P_5]` and, then create a system of differential equations with the highest order coefficients of the commutator::

        sage: C = L(z=P) - P(z=L)
        sage: C.orders(), len(C.monomials())
        ((3, 3, 3, 3, 5, 5, 5), 38)
        sage: system = DifferentialSystem([C.coefficient(z[i]) for i in range(n-1, C.order(z)+1)], variables=p)
        sage: system
        System over [Ring of operator polynomials in (p2, p3, p4, p5, u0, u1, z) over Differential Ring [[Rational Field], (0,)]] with variables [(p2_*, p3_*, p4_*, p5_*)]:
        {
            (-3)*p2_0*u0_1 + (-3)*p2_0*u1_2 + p3_1*u1_0 + (-2)*p3_0*u1_1 + p3_3 + 3*p4_2 + 3*p5_1 + (-10)*u0_3 + (-5)*u1_4 == 0
            p2_1*u1_0 + (-3)*p2_0*u1_1 + p2_3 + 3*p3_2 + 3*p4_1 + (-10)*u0_2 + (-10)*u1_3 == 0
            3*p2_2 + 3*p3_1 + (-5)*u0_1 + (-10)*u1_2 == 0
            3*p2_1 + (-5)*u1_1 == 0
        }

    At this state we can simply call a differential solver to find the solution to this system which will provide formulas for the 
    variables `p_i` in term of `u_i`::

        sage: sols = system.solve_linear()
        sage: sols[p[0]] # p2
        5/3*u1_0
        sage: sols[p[1]] # p3
        5/3*u0_0 + 5/3*u1_1
        sage: sols[p[2]] # p4
        5/9*u1_0^2 + 5/3*u0_1 + 10/9*u1_2
        sage: sols[p[3]] # p5
        10/9*u0_0*u1_0 + 10/9*u0_2

    And, as expected by the Theorem from Wilson, we can see these solutions are homogeneous with appropriate weights::

        sage: weight = R.weight_func({u[i]: n-i for i in range(n-1)}, [1]) # Creating the weight function with w(u_i) = n-i
        sage: all(weight.is_homogeneous(sols[p]) for p in sols) # all coefficients are homogeneous
        True
        sage: weight(sols[p[0]]) # weight of p2 (must be 2)
        2
        sage: weight(sols[p[1]]) # weight of p3 (must be 3)
        3
        sage: weight(sols[p[2]]) # weight of p4 (must be 4)
        4
        sage: weight(sols[p[3]]) # weight of p5 (must be 5)
        5

    If we now plug these solutions into the original `P_5`, we can recompute the commutator with `L` and check it has order
    `n-2 = 1`. The last two coefficients that remain will be the conditions on the differential variables `u_0, u_1`::

        sage: P_eval = P(dic=sols); C_eval = L(z=P_eval) - P_eval(z=L)
        sage: C_eval.order(z)
        1
        sage: C_eval.coefficient(z[0])
        5/9*u0_1*u1_0^2 + 10/9*u0_0*u1_1*u1_0 + 5/9*u0_3*u1_0 + (-5/3)*u0_2*u0_0 + 5/3*u0_2*u1_1 + 
        (-5/3)*u0_1^2 + 20/9*u0_1*u1_2 + 10/9*u0_0*u1_3 + 1/9*u0_5
        sage: C_eval.coefficient(z[1])
        5/9*u1_1*u1_0^2 + (-10/3)*u0_1*u0_0 + 5/3*u0_1*u1_1 + 5/3*u0_0*u1_2 + 5/9*u1_3*u1_0 + 5/9*u1_2*u1_1 + 1/9*u1_5

    This module provide a simple method that perform all thes eoperations in one go. More precisely, the 
    method :func:`almost_commuting_schr` receives as input the values of `n` and `m`, the names for the 
    variables `u` and `z` and return two things: the evaluated `P_m`, i.e., after computing the almost commuting
    conditions and evaluating the polynomial `P_m`; and the coefficients of the commutator `[L, P_m]`::

        sage: Q, (c0,c1) = almost_commuting_schr(3,5)
        sage: Q == P_eval
        True
        sage: c0 == C_eval.coefficient(z[0])
        True
        sage: c1 == C_eval.coefficient(z[1])
        True

    **Special hierarchies**
    -----------------------------------------
    
    There are special hierarchies that are specially important for its use in different results. These are 
    the KdV hierarchy (when `n = 2`) and the Boussinesq hierarchies (when `n=3`). We provide in this module 
    methods as shortcuts to compute these hierarchies.

    For example, for the **kdv hierarchy** we can ge the odd elements (i.e., the non-trivial cases)::

        sage: for n in range(4): print(kdv(2*n+1))
        -u_1
        (-3/2)*u_1*u_0 + (-1/4)*u_3
        (-15/8)*u_1*u_0^2 + (-5/8)*u_3*u_0 + (-5/4)*u_2*u_1 + (-1/16)*u_5
        (-35/16)*u_1*u_0^3 + (-35/32)*u_3*u_0^2 + (-35/8)*u_2*u_1*u_0 + (-35/32)*u_1^3 + (-7/32)*u_5*u_0 + (-21/32)*u_4*u_1 + (-35/32)*u_3*u_2 + (-1/64)*u_7

    For the **Boussinesq hierarchy**, for a given value of `m`, we have two polynomials, the one corresponding to the 
    constant coefficient in `[L,P_m]` and the coefficient of ``z[1]``::

        sage: for i in range(2): print(boussinesq(5, i))
        5/9*u0_1*u1_0^2 + 10/9*u0_0*u1_1*u1_0 + 5/9*u0_3*u1_0 + (-5/3)*u0_2*u0_0 + 5/3*u0_2*u1_1 + (-5/3)*u0_1^2 + 20/9*u0_1*u1_2 + 10/9*u0_0*u1_3 + 1/9*u0_5
        5/9*u1_1*u1_0^2 + (-10/3)*u0_1*u0_0 + 5/3*u0_1*u1_1 + 5/3*u0_0*u1_2 + 5/9*u1_3*u1_0 + 5/9*u1_2*u1_1 + 1/9*u1_5

    **Things remaining TODO**
    -----------------------------------------

    1. Incorporate methods to reduce the equations for higher hierarchies.
    
    **Elements provided by the module**
    -----------------------------------------
'''
import logging

logger = logging.getLogger(__name__)

from functools import reduce, lru_cache
from sage.all import diff, ideal, matrix, parent, QQ, vector, ZZ
from sage.categories.pushout import pushout
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from ..dring import DifferentialRing
from ..dpolynomial.dpolynomial_element import DPolynomial, DPolynomialGen
from ..dpolynomial.dpolynomial_ring import DifferentialPolynomialRing, DPolynomialRing_dense
from ..dpolynomial.dpolynomial_system import DSystem

#################################################################################################
###
### METHODS FOR COMPUTING GENRIC HIERARCHIES
###
#################################################################################################
@lru_cache(maxsize=64)
def schr_L(n: int, name_u: str = "u", name_z: str = "z") -> DPolynomial:
    r'''
        Method to create the generic Scrödinger operator of order `n`.

        This operator is written with the generic formula:

        .. MATH::

            L_n = \partial^n + u_{n-2}\partial^{n-2} + \ldots + u_1\partial + u_0,

        where all the elements `u_i` are differential variables.

        INPUT:

        * ``n``: the order of the Schrödinger operator `L_n`.
        * ``name_u`` (optional): base name for the `u` variables that will appear in `L_n` and in the output `P_m`.
        * ``name_z`` (optional): base name for the differential variable to represent `\partial`.
    '''
    if (not n in ZZ) or ZZ(n) <= 0:
        raise ValueError(f"[almost] The value {n = } must be a positive integer")
    if name_u == name_z:
        raise ValueError(f"[almost] The names for the differential variables must be different. Given {name_u} and {name_z}")
    
    names_u = [f"{name_u}{i}" for i in range(n-1)] if n > 2 else [name_u] if n == 2 else []
    output_ring = DifferentialPolynomialRing(QQ, names_u + [name_z])
    output_z = output_ring.gen('z'); output_u = [output_ring.gen(name) for name in names_u]
    return output_z[n] + sum(output_u[i][0]*output_z[i] for i in range(n-1))

def almost_commuting_schr(n: int, m: int, name_u: str = "u", name_z: str = "z", method ="diff"):
    r'''
        Method to compute an element on the almost-commuting basis.

        Let `L` be a linear differential operator of order `n`. We say that `A` *almost commute
        with `L`* if `ord([L,A]) \leq n-2`. In general, the commutator will have order `n+m-1` where 
        `m` is the order of `A`. Then, if the commutator has such a low order, we say that it *almost
        commute*.

        It is easy to see that:
        
        * `A` almost commuting with `L` does not imply that `L` almost commute with `A`.
        * Let `AC(L)` the set of almost commuting linear operators. Then `AC(L)` is a `C`-vector space
          where `C` is the field of constants of the differential ring `R` where `L` and `A` are built over.

        It was shown by Wilson (TODO: add reference), that for a Schrödinger type operator `L` of order `n`

        .. MATH::

            L_n = \partial^n + u_{n-2}\partial^{n-2} + \ldots + u_1\partial + u_0,

        there is a unique basis of `AC(L_n)` generated by a set of operators `\{P_m\ :\ m\in \mathbb{N}\}` 
        such that:

        * `ord(P_m) = m`.
        * `P_m = \partial^m + p_{m,m-2}\partial^{m-2} + \ldots + p_{m,1}\partial + p_{m,0}`, where `p_{m,i} \in C\{u_*\}`.
        * If we give weights `u_i^{(k)} --> n-i+k`, then `p_{m,j}` are homogeneous of weight `m-j`.

        This method computes, for a given pair or orders `n` and `m` the Wilson's almost commuting base element of order `m`
        for the `n`-th order Schrödinger operator `L_n`.

        INPUT:

        * ``n``: the order of the Schrödinger operator `L_n`.
        * ``m``: the desired order for the almost-commutator.
        * ``name_u`` (optional): base name for the `u` variables that will appear in `L_n` and in the output `P_m`.
        * ``name_z`` (optional): base name for the differential variable to represent `\partial`.
        * ``method`` (optional): method to decide how to solve the arising differential system. Currently 
          the methods ``"diff"`` (see :func:`__almost_commuting_diff`) and ``"linear"`` (see :func:`__almost__commuting_linear`).

        OUTPUT: 

        A pair `(P_m, (T_0,\ldots,T_{n-2}))` such that `P_m` is the almost commutator for the generic `L_n` and the `T_i` are such

        .. MATH::

            [L_n, P_m] = T_0 + T_1\partial + \ldots + T_{n-2}\partial^{n-2}
    '''
    if (not n in ZZ) or ZZ(n) <= 0:
        raise ValueError(f"[almost] The value {n = } must be a positive integer")
    if (not m in ZZ) or ZZ(m) <= 0:
        raise ValueError(f"[almost] The value {m = } must be a positive integer")
    if name_u == name_z:
        raise ValueError(f"[almost] The names for the differential variables must be different. Given {name_u} and {name_z}")
    
    names_u = [f"{name_u}{i}" for i in range(n-1)] if n > 2 else [name_u] if n == 2 else []
    output_ring = DifferentialPolynomialRing(QQ, names_u + [name_z])
    output_z = output_ring.gen('z'); output_u = [output_ring.gen(name) for name in names_u]
    
    if n == 1: # special case where `L = \partial`
        ## Clearly, `\partial^n` and `\partial^m` always commute for all `n` and `m`
        ## Then, the `P_m = \partial^m`.
        output_ring = DifferentialPolynomialRing(QQ, [name_z]); z = output_ring.gens()[0]
        return (z[m], tuple())
    elif m == 1: # special case where we do not care about the for computing `P_1`
        z = output_z; u = output_u
        L = output_z[n] + sum(u[i][0]*z[i] for i in range(n-1))
        P = z[1]
        C = L(dic={z:P}) - P(dic={z:L}); T = tuple([C.coefficient(z[i]) for i in range(C.order(z)+1)])
        return (P, T)
    elif m%n == 0: # special case: the order of the required almost-commutator is divisible by order of base operator
        ## Since `L_n` always commute with itself, so it does `L_n^k` for any `k`. 
        z = output_z; u = output_u
        Ln = output_z[n] + sum(u[i][0]*z[i] for i in range(n-1))
        Pm = reduce(lambda p, q: p(dic={z:q}), (m//n)*[Ln])
        return (Pm, tuple((n-1)*[output_ring.zero()]))
    else: # generic case, there are some computations to be done
        name_p = "p" if not "p" in [name_u, name_z] else "q" if not "q" in [name_u, name_z] else "r"
        method = __almost_commuting_diff if method == "diff" else __almost_commuting_linear if method == "linear" else method
        ## building the operators `L_n` and `P_m`
        names_p = [f"{name_p}{i}" for i in range(m-1)] if m > 2 else [name_p]

        R = DifferentialPolynomialRing(QQ, names_u + names_p + [name_z])
        z = R.gen(name_z); u = [R.gen(name) for name in names_u]; p = [R.gen(name) for name in names_p]
        Ln = z[n] + sum(u[i][0]*z[i] for i in range(n-1))
        Pm = z[m] + sum(p[i][0]*z[i] for i in range(m-1))

        ## building the commutator
        C = Ln(dic={z:Pm}) - Pm(dic={z:Ln})

        ## getting equations for almost-commutation and the remaining with 
        equations = [C.coefficient(z[i]) for i in range(n-1, C.order(z)+1)]
        T = [C.coefficient(z[i]) for i in range(n-1)]

        solve_p = method(R, equations, u, p)
        Pm = output_ring(Pm(dic=solve_p))
        T = tuple([output_ring(el(dic=solve_p)) for el in T])

        return (Pm,T)

def __almost_commuting_diff(parent: DPolynomialRing_dense, equations: list[DPolynomial], _: list[DPolynomialGen], p: list[DPolynomialGen]):
    r'''
        Method that solves the system for almost-commutation using a differential approach

        This method sets up a differential system and tries to solve it using the method 
        :func:`~dalgebra.dpolynomial.dpolynomial_system.DSystem.solve_linear`.
    '''
    S = DSystem(equations, parent=parent, variables=p)
    return S.solve_linear()

def __almost_commuting_linear(parent: DPolynomialRing_dense, equations: list[DPolynomial], u: list[DPolynomialGen], p: list[DPolynomialGen]):
        r'''
            Method that solves the system for almost-commutation using a linear approach

            This method exploits the homogeneous structure that the coefficient must have in order to 
            solve the system of almost-commutation.
        '''
        n = len(u) + 1; m = len(p) + 1
        # Creating the Weight function
        w = parent.weight_func({u[i]: n-i for i in range(n-1)}, [1])

        # Creating the homogeneous monomials and the names for the ansatz variables
        hom_monoms = {p[i] : w.homogeneous_monomials(m-i) for i in range(m-1)}
        ansatz_variables = {p[i]: [f"c_{i}_{j}" for j in range(len(hom_monoms[p[i]]))] for i in range(m-1)}

        # Creating the new base ring with all new constants
        base_C = DifferentialRing(PolynomialRing(QQ, sum([name for name in ansatz_variables.values()],[])), lambda p : 0)
        ansatz_variables = {p[i]: [base_C(el) for el in ansatz_variables[p[i]]] for i in range(m-1)}
        cs = base_C.wrapped.gens()

        ## Adapting the DPolynomialRing
        R = parent.change_ring(base_C)
        to_plug = {R.gen(gen.variable_name()) : sum(coeff*R(mon) for (coeff,mon) in zip(hom_monoms[gen], ansatz_variables[gen])) for gen in p}

        ## Creating the new equations
        equations = [R(equ)(dic=to_plug) for equ in equations] 
        new_equations = sum([[base_C(coeff).wrapped for coeff in equ.coefficients()] for equ in equations],[])

        if len(cs) == 1:
            A = matrix([[equ.lc() for _ in cs] for equ in new_equations])
        else: # multivariate polynomials are the base structure
            A = matrix([[equ.coefficient(v) for v in cs] for equ in new_equations])
        b = vector([equ.constant_coefficient() for equ in new_equations])
        sols = A.solve_right(-b)
        ansatz_evaluated = {}; done = 0
        for i in range(m-1):
            monoms = list(hom_monoms[p[i]])
            ansatz_evaluated[p[i]] = sum(parent.base()(sols[done+j])*monoms[j] for j in range(len(monoms)))
            done = len(monoms)

        return ansatz_evaluated

#################################################################################################
###
### SPECIAL HIERARCHIES
###
#################################################################################################
__KDV = dict()
def kdv(m: int):
    r'''
        KdV hierarchy (see :wiki:`KdV_hierarchy`) is the integrable hierarchy that appears from almost commutators of a generic operator of otder 2.
    '''
    if not m in __KDV:
        __KDV[m] = almost_commuting_schr(2, m)[1]
    return __KDV[m][0]

__BOUSSINESQ = dict()
def boussinesq(m: int, i: int):
    r'''
        Boussinesq hierarchy (TODO: add reference)
    '''
    if not m in __BOUSSINESQ:
        __BOUSSINESQ[m] = almost_commuting_schr(3, m)[1]
    return __BOUSSINESQ[m][i]

#################################################################################################
###
### METHODS FOR COMPUTING SPECIAL TYPE SOLUTIONS
###
#################################################################################################
def GetEquationsForSolution(n: int, m: int, U: list | dict, extract, flag_name = "c", **kwds):
    r'''
        Method to get the equations for a specific type of solutions for non-trivial commutator.

        INPUT:

        * ``n``: the order of the basic operator `L` (see :func:`almost_commuting_schr`).
        * ``m``: the order bound of the commutator to look (see :func:`almost_commuting_schr`).
        * ``U``: special values for the generic coefficients of `L`. It is given as a list of 
          elements where `u_i* = U[i]`. It can also be a dictionary with integers as keys.
        * ``extract``: a method to extract from the final set of values the equations for 
          the obtained operator to actually commute. These equations will include any variable 
          within the given functions ``U`` and the flag of constants created.
        * ``flag_name``: name use for the variables used in the flag of constants.

        OUTPUT:

        A pair `(P, H)` where `P` is an operator of order at most `m` such that it **commutes** with `L_n` (see method 
        :func:`schr_L`) for the given set of ``U`` whenever the equations in `H` all vanish. The equations
        on `H` are only *algebraic* equations.
    '''
    to_log = "logger" in kwds
    if to_log:
        old_level = logger.getEffectiveLevel()
        logger.setLevel(kwds.pop("logger"))
    ## Checking the arguments of the method
    if not n in ZZ or n < 2: raise ValueError(f"[GEFS] The value for `n` must be a integer greater than 1")
    if not m in ZZ or m < n: raise ValueError(f"[GEFS] The value for `m` must be a integer greater than `n`")
    if isinstance(U, (list,tuple)):
        if len(U) != n-1: raise ValueError(f"[GEFS] The size of the given functions ``U`` must be of length `n-1` ({n-1})")
        U = {i: U[i] for i in range(len(U))}
    elif not isinstance(U, dict):
        raise TypeError(f"[GEFS] The argument ``U`` must be a list or a dictionary")
    elif any(el not in ZZ for el in U.keys()) or min(U.keys()) < 0 or max(U.keys()) > n-2:
        raise KeyError(f"[GEFS] The argument ``U`` as dictionary must have integers as keys between 0 and `n-2` ({n-2})")
    
    if not callable(extract): raise TypeError(f"[GEFS] The argument ``extract`` must be a callable.")

    ## Analyzing the functions in ``U``
    logger.debug(f"[GEFS] Computing common parent for the ansatz functions")
    parent_us = reduce(lambda p, q: pushout(p,q), (parent(v) for v in U.values()))
    
    ### Computing the generic `L` operator
    logger.debug(f"[GEFS] Computing the generic L_{n} operator...")
    L = schr_L(n)
    u = L.parent().gens()[:n-1]
    logger.debug(f"[GEFS] {L=}")

    ### Coputing the almost commuting basis up to order `m` and the hierarchy up to this point
    logger.debug(f"[GEFS] ++ Computing the basis of almost commuting and the hierachies...")
    Ps = [L.parent().one()]; Hs = [(n-1)*[L.parent().zero()]]
    for i in range(1, m+1):
        ## TODO: should we remove the i with m%n = 0?
        nP, nH = almost_commuting_schr(n, i, method=kwds.pop("method", "diff"))
        Ps.append(nP); Hs.append(nH)
        logger.debug(f"[GEFS]    Computed for order {i}")
    
    logger.debug(f"[GEFS] -- Computed the basis of almost commuting and the hierarchies")

    ## Adding the appropriate number of flag constants
    logger.debug(f"[GEFS] Creating the ring for having the flag of constants...")
    C = [f"c_{i}" for i in range(len(Ps))]
    base = parent_us.wrapped
    if base != QQ and base.is_field(): base = base.base() # we get now a polynomial ring or rationals
    if base.is_field(): ## rational case, no variable there already
        diff_base = DifferentialRing(PolynomialRing(base, C), lambda _ : 0)
    else: # we had variables before
        old_vars = list(base.variable_names())
        dict_imgs = {v : parent_us(v).derivative() for v in old_vars}; dict_imgs.update({v : 0 for v in C})
        diff_base = DifferentialRing(PolynomialRing(base.base(), old_vars + C), lambda v : dict_imgs[str(v)])
        
    logger.debug(f"[GEFS] Ring with flag-constants: {diff_base=}")
    C = [diff_base(C[i]) for i in range(len(C))]
    U = {u[i]: diff_base(U[i]) for i in U}

    logger.debug(f"[GEFS] Computing the guessed commutator...")
    P = sum(c*p(dic=U) for (c,p) in zip(C, Ps)) # this is the evaluated operator that will commute
    logger.debug(f"[GEFS] Computing the commuting equations...")
    H = [sum(C[i]*Hs[i][j](dic=U) for i in range(len(C))) for j in range(n-1)] # the equations that need to be 0
    logger.debug(f"[GEFS] Extracting the algebraic equation from the commuting equations...")
    H = sum([extract(h) for h in H], []) # extract the true equations from 

    if to_log: logger.setLevel(old_level)

    return L(dic=U), P, ideal(H)

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

def generate_polynomial_equations(H: DPolynomial, var_name: str = "x"):
    r'''Method to extract equations assuming a polynomial ansatz'''
    logger.debug(f"[GenPolyEqus] Getting equations (w.r.t. {var_name}) from: {H=}...")
    H = H.coefficients()[0].wrapped # this removes the diff. variable and the diff. structure remaining only the ansatz variables and the polynomial varaible
    B = parent(H) # this is the algebraic structure
    x = B(var_name) # this is the polynomial variable that will be removed

    return list(H.polynomial(x).coefficients())

def PolynomialCommutator(n: int, m: int, d: int):
    logger.debug(f"[PolyComm] Computing equations for polynomial commutators for L_{n} up to order {m} and degree {d}.")
    logger.debug(f"[PolyComm] --- Generating the ansatz polynomials...")
    U = generate_polynomial_ansatz(QQ, n, d)
    logger.debug(f"[PolyComm] --- Generated the ansatz functions:\n\t{U=}")
    logger.debug(f"[PolyComm] --- Computing the equations necessary for the ansatz to commute with L_{n}...")
    L, P, H = GetEquationsForSolution(n, m, U, generate_polynomial_equations)
    return L,P,H


__all__ = [
    "schr_L", "almost_commuting_schr", 
    "kdv", "boussinesq",
    "GetEquationsForSolution", "PolynomialCommutator"
]
