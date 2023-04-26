r'''
    Module with the algorithms to compute commutator of differential oeprators.

    This module provides algorithms and methods to quickly generate the rings and commutators for some integrable hierarchies.

    TODO:

    * Improve explanation on this module.
    * Add examples of this module.
'''
from functools import reduce
from sage.all import ZZ, QQ, PolynomialRing, matrix, vector
from typing import Callable

from ..dring import DifferentialRing
from ..dpolynomial.dpolynomial_element import DPolynomial, DPolynomialGen
from ..dpolynomial.dpolynomial_ring import DifferentialPolynomialRing, DPolynomialRing_dense
from ..dpolynomial.dpolynomial_system import DSystem

def quasi_commuting_schr(n: int, m: int, name_u: str = "u", name_z: str = "z", method: str | Callable ="diff"):
    r'''
        Method to compute an element on the quasi-commuting basis.

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

        This method computes, for a given pair or orders `n` and `m` the Wilson's quasi commuting base element of order `m`
        for the `n`-th order Schrödinger operator `L_n`.

        INPUT:

        * ``n``: the order of the Schrödinger operator `L_n`.
        * ``m``: the desired order for the quasi-commutator.
        * ``name_u`` (optional): base name for the `u` variables that will appear in `L_n` and in the output `P_m`.
        * ``name_z`` (optional): base name for the differential variable to represent `\partial`.
        * ``method`` (optional): method to decide how to solve the arising differential system. Currently 
          the methods ``diff`` (see :func:`__quasi_commuting_diff`) and ``linear`` (see :func:`__quasi__commuting_linear`).

        OUTPUT: 

        A pair `(P_m, (T_0,\ldots,T_{n-2}))` such that `P_m` is the quasi commutator for the generic `L_n` and the `T_i` are such

        .. MATH::

            [L_n, P_m] = T_0 + T_1\partial + \ldots + T_{n-2}\partial^{n-2}
    '''
    if (not n in ZZ) or ZZ(n) <= 0:
        raise ValueError(f"[quasi] The value {n = } must be a positive integer")
    if (not m in ZZ) or ZZ(m) <= 0:
        raise ValueError(f"[quasi] The value {m = } must be a positive integer")
    if name_u == name_z:
        raise ValueError(f"[quasi] The names for the differential variables must be different. Given {name_u} and {name_z}")
    
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
    elif m%n == 0: # special case: the order of the required quasi-commutator is divisible by order of base operator
        ## Since `L_n` always commute with itself, so it does `L_n^k` for any `k`. 
        z = output_z; u = output_u
        Ln = output_z[n] + sum(u[i][0]*z[i] for i in range(n-1))
        Pm = reduce(lambda p, q: p(dic={z:q}), (m//n)*[Ln])
        return (Pm, tuple((n-1)*[output_ring.zero()]))
    else: # generic case, there are some computations to be done
        name_p = "p" if not "p" in [name_u, name_z] else "q" if not "q" in [name_u, name_z] else "r"
        method = __quasi_commuting_diff if method == "diff" else __quasi_commuting_linear if method == "linear" else method
        ## building the operators `L_n` and `P_m`
        names_p = [f"{name_p}{i}" for i in range(m-1)] if m > 2 else [name_p]

        R = DifferentialPolynomialRing(QQ, names_u + names_p + [name_z])
        z = R.gen(name_z); u = [R.gen(name) for name in names_u]; p = [R.gen(name) for name in names_p]
        Ln = z[n] + sum(u[i][0]*z[i] for i in range(n-1))
        Pm = z[m] + sum(p[i][0]*z[i] for i in range(m-1))

        ## building the commutator
        C = Ln(dic={z:Pm}) - Pm(dic={z:Ln})

        ## getting equations for quasi-commutation and the remaining with 
        equations = [C.coefficient(z[i]) for i in range(n-1, C.order(z)+1)]
        T = [C.coefficient(z[i]) for i in range(n-1)]

        solve_p = method(R, equations, u, p)
        Pm = output_ring(Pm(dic=solve_p))
        T = tuple([output_ring(el(dic=solve_p)) for el in T])

        return (Pm,T)

def __quasi_commuting_diff(parent: DPolynomialRing_dense, equations: list[DPolynomial], u: list[DPolynomialGen], p: list[DPolynomialGen]):
    r'''
        Method that solves the system for quasi-commutation using a differential approach

        This method sets up a differential system and tries to solve it using the method 
        :func:`~dalgebra.dpolynomial.dpolynomial_system.DSystem.solve_linear`.
    '''
    S = DSystem(equations, variables=p)
    return S.solve_linear()

def __quasi_commuting_linear(parent: DPolynomialRing_dense, equations: list[DPolynomial], u: list[DPolynomialGen], p: list[DPolynomialGen]):
        r'''
            Method that solves the system for quasi-commutation using a linear approach

            This method exploits the homogenoues structure that the coefficient must have in order to 
            solve the system of quasi-commutation.
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

        ## Adating the DPolynomialRing
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

__all__ = ["quasi_commuting_schr"]