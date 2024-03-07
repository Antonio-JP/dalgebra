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
    differential variables `u_2,\ldots,u_{n}`. Let us consider the linear differential operator:


    .. MATH::

        L = \partial^n + u_{2}\partial^{n-2}  + \ldots + u_{n-1}\partial + u_n.

    This operator `L` can be written in terms of d-polynomials in the ring `K\{z\} = C\{u_2,\ldots,u_{n},z\}`. We say that 
    another operator `P \in K\{z\}` *almost commutes with `L`* if and only if the commutator of `L` with `P` (`[L,P]`) has order
    at most `\text{ord}(L) - 2`. 

    In general, the order of `[L,P]` is `\text{ord}(L) + \text{ord}(P) - 1`. Hence, in order to obtain a specific order of at most `\text{ord}(L) - 2`
    we need that the coefficients of `P` satisfy `ord(P) + 1` conditions. 

    It was shown in the article by G. Wilson that, if we set `w(u_i) = i`, then for every `m \in \mathbb{N}` there is a unique
    operator `P_m \in K\{z\}` in normal form of order `m` (i.e, `P_m = z^{(m)} + p_{2}z^{(m-2)} + \ldots + p_m`) such that

    * The coefficient `p_i` is homogeneous of weight `i`.
    * `P_m` almost commutes with `L`.

    If we consider all the `P_m`, we obtain a basis of the operators that almost commute with `L`. Moreover, the remaining coefficients
    of `[L,P_m]` provide extra differential conditions that the coefficients of `P_m` have to satisfy in order to have an actual 
    commutator of `L`. These sequences of conditions are called **integrable hierarchies** for a given value of `n = ord(L)`.

    This module provides algorithms and methods to quickly generate the hierarchies in a method :func:`almost_commuting_wilson`, which takes
    the values for `n = \text{ord}(L)` and `m = \text{ord}(P_m)` and computes the `m`-th step in the corresponding hierarchy. Let us 
    show one example when we consider `L` of order 3 and `P_5` of order 5::

        sage: from dalgebra import *
        sage: from dalgebra.commutators import *
        sage: n = 3; m = 5 # Preparing variables for an example
        sage: R = DifferentialPolynomialRing(QQ, [f"p{i+2}" for i in range(m-1)] + [f"u{i}" for i in range(2,n+1)] + ["z"])
        sage: p,u,z = R.gens()[:m-1], R.gens()[m-1:m+n-2], R.gens()[-1]
        sage: L = z[n] + sum(z[n-i]*u[i-2][0] for i in range(2,n+1))
        sage: P = z[m] + sum(z[m-i]*p[i-2][0] for i in range(2,m+1))
        sage: L
        u2_0*z_1 + u3_0*z_0 + z_3
        sage: P
        p2_0*z_3 + p3_0*z_2 + p4_0*z_1 + p5_0*z_0 + z_5

    Now we can compute the commutator `[L, P]` and, then create a system of differential equations with the highest order coefficients of the commutator::

        sage: C = L.lie_bracket(P, z)
        sage: C.orders(), len(C.monomials())
        ((3, 3, 3, 3, 5, 5, 5), 38)
        sage: system = DifferentialSystem([C.coefficient(z[i]) for i in range(n-1, C.order(z)+1)], variables=p)
        sage: system
        System over [Ring of operator polynomials in (p2, p3, p4, p5, u2, u3, z) over Differential Ring [[Rational Field], (0,)]] with variables [(p2_*, p3_*, p4_*, p5_*)]:
        {
            (-3)*p2_0*u2_2 + (-3)*p2_0*u3_1 + p3_1*u2_0 + (-2)*p3_0*u2_1 + p3_3 + 3*p4_2 + 3*p5_1 + (-5)*u2_4 + (-10)*u3_3 == 0
            p2_1*u2_0 + (-3)*p2_0*u2_1 + p2_3 + 3*p3_2 + 3*p4_1 + (-10)*u2_3 + (-10)*u3_2 == 0
            3*p2_2 + 3*p3_1 + (-10)*u2_2 + (-5)*u3_1 == 0
            3*p2_1 + (-5)*u2_1 == 0
        }

    At this state we can simply call a differential solver to find the solution to this system which will provide formulas for the 
    variables `p_i` in term of `u_i`::

        sage: sols = system.solve_linear()
        sage: sols[p[0]] # p2
        5/3*u2_0
        sage: sols[p[1]] # p3
        5/3*u2_1 + 5/3*u3_0
        sage: sols[p[2]] # p4
        5/9*u2_0^2 + 10/9*u2_2 + 5/3*u3_1
        sage: sols[p[3]] # p5
        10/9*u2_0*u3_0 + 10/9*u3_2

    And, as expected by the Theorem from Wilson, we can see these solutions are homogeneous with appropriate weights::

        sage: weight = R.weight_func({u[i]: i+2 for i in range(n-1)}, [1]) # Creating the weight function with w(u_i) = i
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

    If we now plug these solutions into the original `P`, we can recompute the commutator with `L` and check it has order
    `n-2 = 1`. The last two coefficients that remain will be conditions on the differential variables `u_2, u_3`::

        sage: P_eval = P(dic=sols); C_eval = L.lie_bracket(P_eval, z)
        sage: C_eval.order(z)
        1
        sage: C_eval.coefficient(z[0])
        10/9*u2_1*u2_0*u3_0 + 5/9*u2_0^2*u3_1 + 10/9*u2_3*u3_0 + 20/9*u2_2*u3_1 + 5/3*u2_1*u3_2 + 5/9*u2_0*u3_3 + 
        (-5/3)*u3_2*u3_0 + (-5/3)*u3_1^2 + 1/9*u3_5
        sage: C_eval.coefficient(z[1])
        5/9*u2_1*u2_0^2 + 5/9*u2_3*u2_0 + 5/9*u2_2*u2_1 + 5/3*u2_2*u3_0 + 5/3*u2_1*u3_1 + (-10/3)*u3_1*u3_0 + 1/9*u2_5

    This module provide a simple method that perform all these operations in one go. More precisely, the 
    method :func:`almost_commuting_wilson` receives as input the values of `n` and `m`, the names for the 
    variables `u` and `z` and return two things: the evaluated `P_m`, i.e., after computing the almost commuting
    conditions and evaluating the polynomial `P_m`; and the coefficients of the commutator `[L, P_m]`::

        sage: Q, (c0,c1) = almost_commuting_wilson(3,5)
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
        u_1
        (-3/2)*u_1*u_0 + (-1/4)*u_3
        (-15/8)*u_1*u_0^2 + (-5/8)*u_3*u_0 + (-5/4)*u_2*u_1 + (-1/16)*u_5
        (-35/16)*u_1*u_0^3 + (-35/32)*u_3*u_0^2 + (-35/8)*u_2*u_1*u_0 + (-35/32)*u_1^3 + (-7/32)*u_5*u_0 + (-21/32)*u_4*u_1 + (-35/32)*u_3*u_2 + (-1/64)*u_7

    For the **Boussinesq hierarchy**, for a given value of `m`, we have two polynomials, the one corresponding to the 
    constant coefficient in `[L,P_m]` and the coefficient of ``z[1]``::

        sage: for i in range(2): print(boussinesq(5, i))
        10/9*u2_1*u2_0*u3_0 + 5/9*u2_0^2*u3_1 + 10/9*u2_3*u3_0 + 20/9*u2_2*u3_1 + 5/3*u2_1*u3_2 + 5/9*u2_0*u3_3 + (-5/3)*u3_2*u3_0 + (-5/3)*u3_1^2 + 1/9*u3_5
        5/9*u2_1*u2_0^2 + 5/9*u2_3*u2_0 + 5/9*u2_2*u2_1 + 5/3*u2_2*u3_0 + 5/3*u2_1*u3_1 + (-10/3)*u3_1*u3_0 + 1/9*u2_5

    **Things remaining TODO**
    -----------------------------------------

    1. Incorporate methods to reduce the equations for higher hierarchies.
    
    **Elements provided by the module**
    -----------------------------------------
'''
from __future__ import annotations

import logging
logger = logging.getLogger(__name__)

from functools import lru_cache
from sage.all import binomial, matrix, QQ, vector, ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing

from ..dring import DifferentialRing, DRings

from ..dpolynomial.dpolynomial import DPolynomial, DPolynomialGen, DPolynomialSimpleMorphism, DPolynomialRing_Monoid, DifferentialPolynomialRing
from ..dpolynomial.dsystems import DSystem
from ..logging.logging import cache_in_file

#################################################################################################
###
### METHODS FOR COMPUTING GENERIC HIERARCHIES
###
#################################################################################################
def __names_variables(order:int, var_name: str, *, simplify_names: bool = True) -> list[str]:
    r'''
        Method that creates a list with the names of the variables for an operator in normal form.

        This method creates a set of list for a operator in normal form where the names are created using the 
        weights in Wilson theorem. Namely, if we ask for variables in an operator of order 15, then we know
        it has the shape

        .. MATH::

            A = \partial^{15} + a_{2} \partial^{13} + a_3 \partial^{12} + \ldots + a_{14}\partial + a_15

        This method will return the list ``['a2', 'a3', ..., 'a15']. In the particular case when ``order`` is 2, 
        then we do not create any subindex. Other degenerate cases, when ``order`` is too low, we return an empty list.

        EXAMPLES::

            sage: from dalgebra.commutators.almost_commuting import __names_variables
            sage: __names_variables(2, "u")
            ['u']
            sage: __names_variables(1, "t")
            []
            sage: __names_variables(0, "p")
            []
            sage: __names_variables(3, "a")
            ['a_2', 'a_3']
            sage: __names_variables(15, "L")
            ['L_2', 'L_3', 'L_4', 'L_5', 'L_6', 'L_7', 'L_8', 'L_9', 'L_10', 'L_11', 'L_12', 'L_13', 'L_14', 'L_15']

        The option ``simplify_names`` decides whether to remove the index "2" to the variable name when ``order`` is 2.
        In some cases, keeping the generic name template with the `2` is cumbersome, but in other cases it is easier to do 
        comparisons::

            sage: __names_variables(2, "u", simplify_names=False)
            ['u_2']
    '''
    return [f"{var_name}_{i+2}" for i in range(order-1)] if (order > 2 or (not simplify_names)) else [var_name] if order == 2 else []

@lru_cache(maxsize=64)
def generic_normal(n: int, 
                   name_var: str = "u", name_partial: str = "z", *,
                   output_ring: DRings.ParentMethods|None = None, simplify_names: bool = True
) -> DPolynomial:
    r'''
        Method to create the generic differential operator of order `n` in normal form.

        A differential operator in normal form enjoys the following formula:

        .. MATH::

            L = \partial^n + u_{2}\partial^{n-2} + \ldots + u_{n-1}\partial + u_n,

        where all the elements `u_i` are differential variables. This method creates this 
        operator for a given set of differential variables `u` and a specific order.

        INPUT:

        * ``n``: the order of the generic operator in normal form `L`.
        * ``name_var`` (optional): base name for the `u` variables that will appear in `L`.
        * ``name_partial`` (optional): base name for the differential variable to represent `\partial`.
        * ``output_ring`` (optional): if provided, we use this ring as a base ring for creating the differential operator.
          It raises an error if any of the required variables is not included in the ring.
        * ``simplify_names`` (optional): used for the argument ``simplify_names`` in method :func:`__names_variables`.

        OUTPUT:

        An operator in a :class:`~dalgebra.dpolynomial.dpolynomial_ring.DPolynomialRing_sparse` of order
        ``n`` and in generic normal form.

        If `n \leq 0` we raise a :class:`ValueError`. The case when `n = 1` it is always `\partial`.

        EXAMPLES::

            sage: from dalgebra.commutators.almost_commuting import generic_normal
            sage: generic_normal(2)
            u_0*z_0 + z_2
            sage: generic_normal(3)
            u_2_0*z_1 + u_3_0*z_0 + z_3
            sage: generic_normal(4)
            u_2_0*z_2 + u_3_0*z_1 + u_4_0*z_0 + z_4
            sage: generic_normal(4, "a")
            a_2_0*z_2 + a_3_0*z_1 + a_4_0*z_0 + z_4
            sage: generic_normal(4, "a", "p")
            a_2_0*p_2 + a_3_0*p_1 + a_4_0*p_0 + p_4
            sage: from dalgebra import DifferentialPolynomialRing
            sage: R = DifferentialPolynomialRing(QQ, ["u_2", "u_3", "u_4", "p", "a", "z"])
            sage: generic_normal(4, output_ring=R).parent() is R
            True
            sage: generic_normal(4).parent()
            Ring of operator polynomials in (u_2, u_3, u_4, z) over Differential Ring [[Rational Field], (0,)]

    '''
    ## Checking the input
    if (not n in ZZ) or ZZ(n) <= 0:
        raise ValueError(f"[almost] The value {n = } must be a positive integer")
    if name_var == name_partial:
        raise ValueError(f"[almost] The names for the differential variables must be different. Given {name_var} and {name_partial}")
    if output_ring != None and not isinstance(output_ring, DPolynomialRing_Monoid):
        raise TypeError(f"[almost] The optional argument `output_ring` must be a ring of d-polynomials or ``None``")
    
    names_u = __names_variables(n, name_var, simplify_names=simplify_names)
    output_ring = DifferentialPolynomialRing(QQ, names_u + [name_partial]) if output_ring is None else output_ring
    try:
        output_z = output_ring.gen(name_partial); output_u = [output_ring.gen(name) for name in names_u] # output_u = [u2, u3, ..., un]
    except ValueError:
        raise IndexError(f"[almost] An output ring was given but does not include all necessary variable: {names_u + [name_partial]}")
    return output_z[n] + sum(output_u[i-2][0]*output_z[n-i] for i in range(2,n+1))

@cache_in_file
def base_almost_commuting_wilson(n: int, m: int, equation_gens:str = "recursive", solver:str ="linear"):
    r'''
        Method to compute an element on Wilson's almost-commuting basis.

        Let `L` be a generic linear differential operator of order `n` in normal form (as generated by :func:`generic_normal`). 
        We say that `A` *almost commute with `L`* if `ord([L,A]) \leq n-2`. In general, the commutator will have order `n+m-1` where 
        `m` is the order of `A`. Then, if the commutator has such a low order, we say that it *almost
        commutes*.

        It is easy to see that:
        
        * `A` almost commuting with `L` does not imply that `L` almost commute with `A`.
        * Let `W(L)` the set of almost commuting linear operators. Then `W(L)` is a `C`-vector space
          where `C` is the field of constants of the differential ring `R` where `L` and `A` are built over.

        It was shown by Wilson (TODO: add reference), that for an operator `L` of order `n` in normal form

        .. MATH::

            L_n = \partial^n + u_{2}\partial^{n-2} + \ldots + u_{n-1}\partial + u_n,

        there is a unique basis of `W(L_n)` generated by a set of operators `\{P_m\ :\ m\in \mathbb{N}\}` 
        such that:

        * `ord(P_m) = m`.
        * `P_m = \partial^m + p_{m,2}\partial^{m-2} + \ldots + p_{m,m-1}\partial + p_{m,m}`, where `p_{m,i} \in C\{u_*\}`.
        * If we give weights `u_i^{(k)} --> i+k`, then `p_{m,j}` are homogeneous of weight `j`.

        This method computes, for a given pair or orders `n` and `m` the Wilson's almost commuting base element of order `m`
        for the `n`-th order normal differential operator `L_n`.

        INPUT:

        * ``n``: the order of the Schrödinger operator `L_n`.
        * ``m``: the desired order for the almost-commutator.
        * ``name_u`` (optional): base name for the `u` variables that will appear in `L_n` and in the output `P_m`.
        * ``name_z`` (optional): base name for the differential variable to represent `\partial`.
        * ``equation_gens`` (optional): method to decide how to create the differential system. Currently 
          the methods ``"direct"`` (see :func:`__almost_commuting_direct`) and ``"recursive"`` (see :func:`__almost__commuting_recursive`).
        * ``solver`` (optional): method to decide how to solve the arising differential system. Currently 
          the methods ``"integral"`` (see :func:`__almost_commuting_integral`) and ``"linear"`` (see :func:`__almost__commuting_linear`).

        OUTPUT: 

        A pair `(P_m, (T_0,\ldots,T_{n-2}))` such that `P_m` is the almost commutator for the generic `L_n` and the `T_i` are such

        .. MATH::

            [L_n, P_m] = T_0 + T_1\partial + \ldots + T_{n-2}\partial^{n-2}

        TESTS::

            sage: from dalgebra.commutators.almost_commuting import base_almost_commuting_wilson
            sage: for n in range(2,3): # long time (> 2 min)
            ....:     for m in range(1, 10):
            ....:         O1 = base_almost_commuting_wilson(n,m,solver="linear", equation_gens="recursive", to_cache=False)
            ....:         O2 = base_almost_commuting_wilson(n,m,solver="diff",   equation_gens="recursive", to_cache=False)
            ....:         O3 = base_almost_commuting_wilson(n,m,solver="linear", equation_gens="direct", to_cache=False)
            ....:         O4 = base_almost_commuting_wilson(n,m,solver="diff",   equation_gens="direct", to_cache=False)
            ....:         assert O1 == O2, f"Error between 1 and 2 ({n=}, {m=})"
            ....:         assert O1 == O3, f"Error between 1 and 3 ({n=}, {m=})"
            ....:         assert O1 == O4, f"Error between 1 and 4 ({n=}, {m=})"
    '''
    name_u: str = "u"; name_z: str = "z"
    if (not n in ZZ) or ZZ(n) <= 0:
        raise ValueError(f"[almost] The value {n = } must be a positive integer")
    if (not m in ZZ) or ZZ(m) <= 0:
        raise ValueError(f"[almost] The value {m = } must be a positive integer")
    if name_u == name_z:
        raise ValueError(f"[almost] The names for the differential variables must be different. Given {name_u} and {name_z}")
    
    names_u = __names_variables(n, name_u)
    output_ring = DifferentialPolynomialRing(QQ, names_u + [name_z])
    output_z = output_ring.gen(name_z) # variable for the `\partial`
    output_u = [output_ring.gen(name) for name in names_u] # sorted `u` variables independent of the lexicographic order
    
    if n == 1: # special case where `L = \partial`
        ## Clearly, `\partial^n` and `\partial^m` always commute for all `n` and `m`
        ## Then, the `P_m = \partial^m`, and there is not `T_i`
        output = (output_z[m], tuple())
    elif m == 1: # Special case
        ## This case is simpler because there is a unique operator in normal form of order 1: \partial
        ## Moreover, [L, \partial] = -\kappa_\partial(L), i.e., the coefficients of the commutator are simply the derivatives of the coefficients of L
        P = output_z[1]
        T = tuple([-output_u[-(i+1)][1] for i in range(n-1)]) # (-u_n', -u_{n-1}',..., -u_2')
        output = (P, T)
    elif m%n == 0: # Special case: the order of the required almost-commutator is divisible by order of base operator
        ## Since `L_n` always commute with itself, so it does `L_n^k` for any `k`. 
        Pm = generic_normal(n, output_ring=output_ring).sym_power(m//n, output_z)
        output = (Pm, tuple((n-1)*[output_ring.zero()]))
    else: # generic case, there are some computations to be done
        name_p = "p" if not "p" in [name_u, name_z] else "q" if not "q" in [name_u, name_z] else "r"
        equation_gens = __almost_commuting_direct if equation_gens == "direct" else __almost_commuting_recursive if equation_gens == "recursive" else equation_gens
        solver = __almost_commuting_integral if solver == "integral" else __almost_commuting_linear if solver == "linear" else solver
        ## Building the equations that need to be solved
        R, equations, T = equation_gens(output_ring, n, m, name_p, name_u, name_z)
        u = [R.gen(name) for name in names_u] # this is [u2, u3, ..., un]
        p = [R.gen(v) for v in __names_variables(m, name_p, simplify_names=False)] # this is [p2, p3, ..., pn]

        ## Creating the simplification morphism
        simplifier = DPolynomialSimpleMorphism(R, output_ring)

        ## Solving the system with the corresponding method
        solve_p = solver(R, equations, u, p)
        solve_p = {v : simplifier(solve_p[v]) for v in p}
        Pm = output_z[m] + sum(solve_p[v] * output_z[m-i-2] for i, v in enumerate(p))
        T = tuple([simplifier(el(dic=solve_p)) for el in T])
        
        output = (Pm,T)
    return output

@cache_in_file
def almost_commuting_wilson(n: int, m: int, name_u: str|list[str]|tuple[str] = "u", name_z: str = "z"):
    import os
    from .. import dalgebra_folder

    #################################################################################################################################
    ## We first call the base code that only cares about "n" and "m" with default names for "u" and "z".
    (Pm, T) = base_almost_commuting_wilson(
        n,m, ## Default values for the call on the base_commuting_wilson
        path_to_folder=os.path.join(dalgebra_folder(), "results", "almost_commuting"), ## Folder for caching results in repository
        extension="out" ## Extension of the cached results
    )

    #################################################################################################################################
    ## Then we proceed to change the names in the differential structure
    if name_u != "u" or name_z != "z":
        true_u = __names_variables(n, "u")
        if isinstance(name_u, (list, tuple)) and len(name_u) == n-1: ## We allow custom names for the us if given in a list format
            names_u = name_u
        else:
            names_u = __names_variables(n, name_u)
        output_R = DifferentialPolynomialRing(QQ, names_u + [name_z])

        output_z = output_R.gen(name_z) # variable for the `\partial`
        output_u = [output_R.gen(name) for name in names_u] # sorted `u` variables independent of the lexicographic order

        dic = {true_u[i] : output_u[i][0] for i in range(len(true_u))}
        dic["z"] = output_z[0]

        Pm = Pm(**dic)
        T = tuple(el(**dic) for el in T)

    return Pm,T

def __almost_commuting_direct(parent: DPolynomialRing_Monoid, order_L: int, order_P: int, name_p: str, name_u: str, name_z: str) -> tuple[DPolynomialRing_Monoid, list[DPolynomial], list[DPolynomial]]:
    r'''
        Direct method to compute the equations to solve for Wilson's almost commuting basis.

        This method computes the equation by creating the operators `L` and `P`, computing its commutator `C = [L,P]` and extracting its coefficients.

        This method receives the usual input for methods that create the equations:

        * ``parent``: a basic :class:`DPolynomialRing_sparse` that must contain the `u` variables and the `\partial` variable.
        * ``order_L``: the value we are using as order of the generic operator `L`.
        * ``order_P``: the order of the almost commuting operator `P` which equations we want to compute.
        * ``name_p``: name of the variables we will create that will be solved (see :func:`__names_variables`)
        * ``name_u``: base name of the differential variables that are the coefficients of the generic operator `L`. Used to recognize them in ``parent``.
        * ``name_z``: name for the `\partial` variable. Used to recognize it in ``parent``.

        Then, the output is in the usual format for these methods: it returns a tuple `(R, eqs, T)` where:

        * `R`: is the final ring of differential polynomials generated to represent the equations.
        * `eqs`: a list/tuple with the equations to be solved.
        * `T`: the remaining equations unnecessary for the almost-commuting that will define the hierarchies.
    '''
    ## We add the variables of `p` into the ring ``parent``.
    R = parent.append_variables(*__names_variables(order_P, name_p, simplify_names=False))

    ## We create the operators `L` and `P`
    L = generic_normal(order_L, name_u, name_z, output_ring=R)
    logger.debug(f"[AC-get_equ-direct] Operator L_{order_L}: {L}")
    P = generic_normal(order_P, name_p, name_z, output_ring=R, simplify_names = False)
    logger.debug(f"[AC-get_equ-direct] Operator P_{order_P}: {P}")
    z = R.gen(name_z) # used for later substitution

    ## We compute now the commutator of L and P
    C = L.lie_bracket(P, z)

    ## Getting equations for almost-commutation and the remaining with 
    equations = [C.coefficient_full(z[i]) for i in range(order_L-1, C.order(z)+1)]
    T = [C.coefficient_full(z[i]) for i in range(order_L-1)]

    ## Returning the full output
    return R, equations, T

@lru_cache(maxsize=128)
def __almost_commuting_recursive(parent: DPolynomialRing_Monoid, order_L: int, order_P: int, name_p: str, name_u: str, name_z: str) -> tuple[DPolynomialRing_Monoid, list[DPolynomial], list[DPolynomial]]:
    r'''
        Recursive method to compute the equations to solve for Wilson's almost commuting basis.

        This method computes the equations using the main recursive structure given by `[L, P_{m+1}] = [L, P_m]\partial + P_m[L, \partial] + [L, p_{m+1}]`.

        This method receives the usual input for methods that create the equations:

        * ``parent``: a basic :class:`DPolynomialRing_sparse` that must contain the `u` variables and the `\partial` variable.
        * ``order_L``: the value we are using as order of the generic operator `L`.
        * ``order_P``: the order of the almost commuting operator `P` which equations we want to compute.
        * ``name_p``: name of the variables we will create that will be solved (see :func:`__names_variables`)
        * ``name_u``: base name of the differential variables that are the coefficients of the generic operator `L`. Used to recognize them in ``parent``.
        * ``name_z``: name for the `\partial` variable. Used to recognize it in ``parent``.

        Then, the output is in the usual format for these methods: it returns a tuple `(R, eqs, T)` where:

        * `R`: is the final ring of differential polynomials generated to represent the equations.
        * `eqs`: a list/tuple with the equations to be solved.
        * `T`: the remaining equations unnecessary for the almost-commuting that will define the hierarchies.

        TEST::

            sage: from dalgebra.dpolynomial import DifferentialPolynomialRing
            sage: from dalgebra.commutators.almost_commuting import __names_variables, __almost_commuting_direct, __almost_commuting_recursive
            sage: for n in range(2, 6): # long time (> 30 s)
            ....:     R = DifferentialPolynomialRing(QQ, __names_variables(n, "u") + ["z"])
            ....:     for m in range(1, 10):
            ....:         O1 = __almost_commuting_direct(R, n, m, "p", "u", "z")
            ....:         O2 = __almost_commuting_recursive(R, n, m, "p", "u", "z")
            ....:         assert O1 == O2
    '''    
    if order_P == 1:
        logger.debug(f"[AC-get_equ-recur] Reached base case with {order_P=}. Returning simple answer.")
        return parent, [], [-parent.gen(name)[1] for name in reversed(__names_variables(order_L, name_u))]
    else:
        logger.debug(f"[AC-get_equ-recur] Computing equation for {order_L=} and {order_P=}")
        logger.debug(f"[AC-get_equ-recur] Recursive call to order_P={order_P-1}")
        R, E, T = __almost_commuting_recursive(parent, order_L, order_P - 1, name_p, name_u, name_z)
        E = T + E # mixing into one to fit format of recursion

        ## Getting the final ring
        R = R.append_variables(f"{name_p}_{order_P}") # we add the last variable ("p_m") into `R` 
        u = list(reversed([R.gen(name) for name in __names_variables(order_L, name_u)]))+ [[R.zero(), R.zero()], [R.one()]] # u[i] := coeff(L, z[i])
        p = [R.one(), R.zero()] + [R.gen(f"{name_p}_{i}") for i in range(2, order_P+1)] # p[i] := p_i (i.e. the coefficient of weight `i`)
        assert len(u) == order_L + 1; assert len(p) == order_P + 1
        ## Casting old things to the new ring
        E = [R(el) for el in E]

        n = order_L; m = order_P-1 # for simplicity in the following formulas

        ## Starting from the recursive part
        logger.debug(f"[AC-get_equ-recur] Creating the recursive part of the output ([L, P_{m}]D)")
        output = [R.zero()] + E + [R.zero() for _ in range(order_L+order_P-3-len(E))]
        assert len(output) == order_L + order_P - 2

        ## Computing the influence of the new variable
        logger.debug(f"[AC-get_equ-recur] Creating the part involving the new variable ([L, p_{m+1}])")
        for l in range(n-1):
            el = binomial(n, l)*p[m+1][n-l] + sum(binomial(i,l)*u[i][0]*p[m+1][i-l] for i in range(l+1, n-1))
            logger.debug(f"[AC-get_equ-recur] - Coefficient {l}: {el}")
            output[l] += el
        logger.debug(f"[AC-get_equ-recur] - Coefficient {n-1}: {n*p[m+1][1]}")
        output[n-1] += n*p[m+1][1]

        ## Computing the generic influence
        logger.debug(f"[AC-get_equ-recur] Creating the remaining part of the output (P_{m} [L, d])")
        for l in range(n+m-1):
            el = (
                sum(sum(binomial(i,k)*p[m-i][0]*u[l-k][i-k+1] for k in range(max(0, l-n+2), min(i,l)+1) )for i in range(max(0, l-n+2), m-1)) +
                sum(binomial(m,k)*u[l-k][m-k+1]for k in range(max(0, l-n+2), min(m,l)+1) )
            )
            logger.debug(f"[AC-get_equ-recur] - Coefficient {l}: {el}")
            output[l] -= el

        return R, output[n-1:], output[:n-1]

def __almost_commuting_integral(parent: DPolynomialRing_Monoid, equations: list[DPolynomial], _: list[DPolynomialGen], p: list[DPolynomialGen]) -> dict[DPolynomialGen, DPolynomial]:
    r'''
        Integration method to solve the equations for obtaining Wilson's almost commuting basis.

        This method solves the system (which is triangular) using a differential solver and using integration of differential polynomials.

        This method receives the usual input for methods that solve the equations:

        * ``parent``: the ring where the equations are.
        * ``equations``: a list of equations to be solved.
        * ``u``: variables from the generic operator `L` for which we are computing the almost commuting basis.
          These are sorted by increasing weight (i.e., `u_2, u_3, \ldots, u_{n}`)
        * ``p``: variables that will be solved in the system. These correspond to the generated variables for the 
          almost commuting operator `P`. They are sorted by increasing weight (i.e., `p_2, p_3,\ldots, p_m`)

        Then, the output is in the usual format for these methods: it returns a dictionary `v \mapsto A` where `v` are 
        the variables given in ``p`` and `A` are the values such that, plugged into ``equations``, make them all vanish.
    '''
    S = DSystem(equations, parent=parent, variables=p)
    return S.solve_linear()

def __almost_commuting_linear(parent: DPolynomialRing_Monoid, equations: list[DPolynomial], u: list[DPolynomialGen], p: list[DPolynomialGen]) -> dict[DPolynomialGen, DPolynomial]:
    r'''
        Method that solves the system for almost-commutation using a linear approach

        This method exploits the homogeneous structure that the coefficient must have in order to 
        solve the system of almost-commutation.

        This method receives the usual input for methods that solve the equations:

        * ``parent``: the ring where the equations are.
        * ``equations``: a list of equations to be solved.
        * ``u``: variables from the generic operator `L` for which we are computing the almost commuting basis.
        These are sorted by increasing weight (i.e., `u_2, u_3, \ldots, u_{n}`)
        * ``p``: variables that will be solved in the system. These correspond to the generated variables for the 
        almost commuting operator `P`. They are sorted by increasing weight (i.e., `p_2, p_3,\ldots, p_m`)

        Then, the output is in the usual format for these methods: it returns a dictionary `v \mapsto A` where `v` are 
        the variables given in ``p`` and `A` are the values such that, plugged into ``equations``, make them all vanish.
    '''
    n = len(u) + 1; m = len(p) + 1
    # Creating the Weight function
    w = parent.weight_func({u[i]: i+2 for i in range(n-1)}, [1])

    # Creating the homogeneous monomials and the names for the ansatz variables
    # Since p = [p_2, p_3, ..., p_m] we create the homogeneous monomials increasingly
    hom_monoms = {weight : w.homogeneous_monomials(weight) for weight in range(2,m+1)}
    ansatz_variables = {weight: [f"c_{weight}_{j}" for j in range(len(hom_monoms[weight]))] for weight in range(2,m+1)}
    # Creating the new base ring with all new constants
    base_C = DifferentialRing(PolynomialRing(parent.base().wrapped,sum([name for name in ansatz_variables.values()],[])))
    ansatz_variables = {weight: [base_C(el) for el in ansatz_variables[weight]] for weight in range(2,m+1)}
    cs = base_C.wrapped.gens() # used for linear equations at the end

    ## Adapting the DPolynomialRing
    # Casting monomials to the new ring (creating again reduce possible errors)
    R = parent.change_ring(base_C)
    to_plug = {f"p_{weight}" : sum(coeff*R(mon) for (mon,coeff) in zip(hom_monoms[weight], ansatz_variables[weight])) for weight in range(2, m+1)}

    ## Creating the new equations
    plugged_equations = [equ(**to_plug) for equ in equations] 
    new_equations = sum([[coeff.wrapped for coeff in equ.coefficients()] for equ in plugged_equations],[])
    
    if len(cs) == 1:
        A = matrix(base_C.wrapped.base(), [[equ.lc() for _ in cs] for equ in new_equations])
    else: # multivariate polynomials are the base structure
        A = matrix(base_C.wrapped.base(), [[equ.coefficient(v) for v in cs] for equ in new_equations])
    b = vector([equ.constant_coefficient() for equ in new_equations])
    sols = A.solve_right(-b)
    sols = {c : sol for (c, sol) in zip (cs, sols)}
    ## The ansatz evaluated contains elements in `parent`
    ansatz_evaluated = {gen: sum(parent.base()(sols[coeff])*mon for (mon, coeff) in zip(hom_monoms[i+2], ansatz_variables[i+2])) for (i,gen) in enumerate(p)}

    return ansatz_evaluated
###
#################################################################################################
def hierarchy(n: int, m: int, i: int | tuple[int] | list[int] | slice | None = None):
    r'''
        Return equations of the `m`-th step of the integrable hierarchy induced by `n`.

        This method computes all the equations in the hierarchy using the method :func:`almost_commuting_wilson` 
        and then return the corresponding equations indicated by the argument `i`,
    '''
    H = almost_commuting_wilson(n,m)[1]
    if isinstance(i, int):
        return H[i]
    elif isinstance(i, (tuple, list)):
        return [H[ind] for ind in i]
    elif isinstance(i, slice):
        return H[i]
    return H

def kdv(m: int):
    r'''
        KdV hierarchy (see :wiki:`KdV_hierarchy`) is the integrable hierarchy that appears from almost commutators of a generic operator of order 2.
    '''
    return hierarchy(2,m,0)

def boussinesq(m: int, i: int | tuple[int] | list[int] | slice | None = None):
    r'''
        Boussinesq hierarchy (TODO: add reference)
    '''
    return hierarchy(3,m,i)

@cache_in_file
def recursion(n: int):
    r'''
        Method that computes the associated recursion matrix that arises from checking the first jumping in the hierarchy.

        Namely, assume we have computed the almost commuting basis given by Wilson's theorem, `P_m(U)` and let 

        .. MATH::

            [L, P_m(U)] = H_{m,0}(U) + \ldots H_{m,n-2}(U) \partial^{n-2}.

        We know that the elements `H_{m,i}` are homogeneous of weight `n+m-i`. Moreover, it is supposed (at least for `n=2` and 
        `n=3`) that there are recursion matrices of pseudo-differential operators `R` such that 

        .. MATH::

            R H_m = H_{m+n},

        where `H_m = (H_{m,0}(U),\ldots, H_{m,n-2}(U))^T`.

        A priori, we do not know how bad is `R` in terms of the pseudo-differential part. However, since this formula works for all
        `m \geq 1`, these operator must be applicable for that particular case `m=1`. This, luckily, is always a very simple case:

        .. MATH::

            H_{1,i}(U) = -u_{n-2-i}'.

        Hence, the operators in `R` can be pseudo differential operators with, at most, negative order `-1`. This can be adapted in the code
        to be working.

        Moreover, the recursion formula gives also structure to the operators in `R`. Since `R H_m = H_{n+m}`, we have that the output of the recursion
        is again homogeneous. This means that the elements of `R` are homogeneous of some particular weights. More precisely,

        .. MATH::

            w(R_{i,j}) = (2n+m-i) - (n+m-j) = n + j - i,

        which is independent of `m`. Hence, we can do an ansatz using the homogeneous monomials of weights `0, \ldots, n+j-i+1` where

        .. MATH::

            R_{i,j} = \sum_{o=-1}^{n+j-i} c_{i,j,o}(U) \partial^o,

        where the elements `c_{i,j,o} are generic homogeneous elements of weight `o`. We can plug these expressions right away into `R H_m = H_{m+n}` for
        `m=1,\ldots,n-1` and then we check the conditions on the generic coefficients to obtain the equality. Solving this system leads to the recursion 
        matrix.

        NOTE: We need to check whether this always leads to a unique solution or not. The hope is that, yes.
    '''
    from sage.rings.ideal import Ideal
    ## Some auxiliary functions
    logger.info(f"[recursion] ++ Defining the auxiliary function...")
    I = lambda p : p.inverse_operation(0) # computes the integral of an element (or tries)
    ACT = lambda op, p: op[0](**{z.variable_name(): p}) + (op[1]*I(p) if op[1] != 0 else op[1]) # computes the action of a pseudo_operator of order -1 `op` over `p`
    ACT_M = lambda M, ps: [sum(ACT(op, p) for (op, p) in zip(M[i], ps)) for i in range(len(M))] # applies a matrix of p.o. of order -1 `M` over a vector of `ps`.
    
    logger.info(f"[recursion] Computing the recursion matrix for {n=}.")
    L = generic_normal(n); z = L.parent().gen("z")
    
    ## We compute now the first two steps of the hierarchy
    logger.info(f"[recursion] ++ Computing the hierarchy up to order {2*n-1}...")
    H = [None] + [hierarchy(n, m) for m in range(1, 2*n)]

    ## We check the valid elements for the pseudo-part
    logger.info("[recursion] ++ Checking which columns on R can have \\partial^{-1}")
    valid_pseudo = []
    for r in range(n-1):
        try:
            for m in range(1,n):
                I(H[m][r])
            # all have exact integrals -> valid for \partial^{-1}
            valid_pseudo.append(r)
        except ValueError:
            pass
    valid_pseudo = set(valid_pseudo)
    logger.info(f"[recursion] ++ Valid columns: {valid_pseudo}")


    ## We compute now the homogeneous monomials
    order_in_matrix = lambda i,j : n + j - i
    logger.info(f"[recursion] ++ Computing the homogeneous monomials up to order {2*n-1}")
    W = L.parent().weight_func([int(v.variable_name()[1:]) for v in L.parent().gens()[:-1]] + [0], [1]) # everything except derivation has weight 1 # TODO: the getting of weight is dubius
    T = [W.homogeneous_monomials(i) for i in range(2*n)]

    ## We first create the ansatz. For that, we need to define the ansatz constants first.
    logger.info(f"[recursion] ++ Creating all the variable names...")
    variable_names_matrix = [
        [
            [[f"c_{i}_{j}_{o}_{k}" for k in range(len(T[o]))] for o in range(order_in_matrix(i,j)+2)]
            for j in range(n-1)
        ]
        for i in range(n-1)
    ]
    all_variables = sum((sum((sum((variable_names_matrix[i][j][o] for o in range(order_in_matrix(i,j)+2)), []) for j in range(n-1)), []) for i in range(n-1)), [])
    logger.info(f"[recursion] ++ Created {len(all_variables)} variables")
    logger.info(f"[recursion] ++ Adding the constants to the ring")
    R = L.parent().add_constants(*all_variables) # The differential ring with the differential variables and all the constants
    logger.info(f"[recursion] ++ Creating the generic matrix of operators...")
    M = [
            [
                (
                    sum(sum(R(c)*R(str(t)) for (c,t) in zip(variable_names_matrix[i][j][o], T[o]))*R(str(z[order_in_matrix(i,j)-o])) for o in range(order_in_matrix(i,j)+1)), 
                    sum(R(c)*R(str(t)) for (c,t) in zip(variable_names_matrix[i][j][n+j-i+1], T[n+j-i+1])) if j in valid_pseudo else R.zero() # homogenous of weight n+j-i+1 for "\partial^{-1}"
                )
            for j in range(n-1)] 
        for i in range(n-1)]

    BwC = R.base().wrapped # base ring w/o differential structure
    B = BwC.base() # base ring w/o ansatz variables --> solutions will live here
    
    ## Casting the computed hierarchy to the new ring
    logger.info(f"[recursion] ++ Casting the Hs into the appropriate ring...")
    H = [None] + [[sum(BwC(c)*R(str(m)) for (c,m) in zip(el.coefficients(), el.monomials())) for el in h] for h in H[1:]]

    ## We compute the equations to be solve
    logger.info(f"[recursion] ++ Computing the equations to be solved...")
    equations = []
    for m in range(1,n):
        MH = ACT_M(M, H[m])
        diff = [MH[i] - H[m+n][i] for i in range(n-1)]
        equations += sum([[BwC(el) for el in h.coefficients()] for h in diff], [])
    
    logger.info(f"[recursion] ++ Created the linear systems. We have {len(equations)} equations")
    ## We solve the system (NOTE: right now we use groebner bases and reduce, maybe it is better to change this)
    
    logger.info(f"[recursion] ++ Solving the linear system... (currently with Grobner basis)")
    ideal_orig = Ideal(equations)
    ideal_gb = ideal_orig.groebner_basis()
    logger.info(f"[recursion] ++ Computing the final solutions")
    
    variables_solved = [
        [
            [[B(BwC(f"c_{i}_{j}_{o}_{k}").reduce(ideal_gb)) for k in range(len(T[o]))] for o in range(order_in_matrix(i,j)+2)]
            for j in range(n-1)
        ]
        for i in range(n-1)
    ]
    M = [
            [
                (
                    sum(sum(c*t for (c,t) in zip(variables_solved[i][j][o], T[o]))*z[order_in_matrix(i,j)-o] for o in range(order_in_matrix(i,j)+1)), 
                    sum(c*t for (c,t) in zip(variables_solved[i][j][n+j-i+1], T[n+j-i+1])) # homogenous of weight n+j-i+1 for "\partial^{-1}"
                )
            for j in range(n-1)] 
        for i in range(n-1)]
    
    logger.info(f"[recursion] ++ Finished computation")
    return M

__all__ = [
    "generic_normal", "almost_commuting_wilson", 
    "hierarchy", "kdv", "boussinesq"
]
