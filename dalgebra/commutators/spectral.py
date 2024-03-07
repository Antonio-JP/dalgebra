r'''    
    Computation of spectral curves.

    This module contains the main functionality to compute and analyze the spectral curves obtained from a pair 
    of commuting linear differential operators.

    **Things remaining TODO**
    -----------------------------------------

    1. CHECK CHANGES FROM NEW DPOLYNOMIAL FRAMEWORK
    2. Extend this documentation
    3. Add references to notation, definitions, etc.
    
    **Elements provided by the module**
    -----------------------------------------
'''
from __future__ import annotations

import logging

logger = logging.getLogger(__name__)

from collections.abc import Sequence as ListType
from sage.all import gcd
from sage.rings.fraction_field import is_FractionField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.polynomial_element_generic import Polynomial
from sage.rings.polynomial.multi_polynomial_element import MPolynomial
from time import time
from typing import TypedDict

from ..dring import DifferentialRing
from ..dpolynomial.dpolynomial import DPolynomial, DifferentialPolynomialRing
from ..logging.logging import loglevel
from .ideals import SolutionBranch

################################################################################################
### TYPES USED IN THIS MODULE
################################################################################################
class SolutionBranch_SpectralData(TypedDict):
    time_res: float
    time_seq: float
    h: Polynomial | MPolynomial
    first_nonzero: int
    rk: int

#################################################################################################
###
### METHODS FOR OBTAINING SPECTRAL CURVES
###
################################################################################################
@loglevel(logger)
def SpectralCurveOverIdeal(L: DPolynomial, P: DPolynomial, branches: ListType[SolutionBranch]) -> dict[SolutionBranch, SolutionBranch_SpectralData]:
    r'''
        Method that automatizes the computation of spectral curve and some extra data throughout the 
        solution branches of an ideal.
    '''
    final_output = dict()
    tot = len(branches)
    for ind,branch in enumerate(branches):
        logger.info(f"##########################################################")
        logger.info(f"### Starting the computation on branch {ind+1}/{tot}   ###")
        logger.debug(f"Evaluating the linear operators on the branch...")
        data = SolutionBranch_SpectralData()
        Lb = branch.eval(L)
        Pb = branch.eval(P)
        logger.debug(f"Computing the spectral operators...")
        L_l, P_m = spectral_operators(Lb, Pb)
        SDR = L_l.parent()
        logger.debug(f"Computing the differential resultant...")
        ctime = time()
        res = SDR.sylvester_resultant(L_l, P_m)
        data["time_res"] = time()-ctime
        h = res.coefficients()[0].wrapped.factor()[0]
        data["h"] = h
        logger.debug(f"Computed: {data['time_res']}")
        logger.debug(f"Computing the differential subresultant sequence...")
        ctime = time()
        seq = SDR.sylvester_subresultant_sequence(L_l, P_m)
        data["time_seq"] = time()-ctime
        logger.debug(f"Computed: {data['time_seq']}")
        logger.debug(f"Checking the first non-zero subresultant over the curve...")
        for i, pseq in enumerate(seq):
            coeffs = [__simplify(c.wrapped, h[0]) for c in pseq.coefficients()]
            if any(el != 0 for el in coeffs):
                data["first_nonzero"] = (i, sum(c*m for m,c in zip(pseq.monomials(), coeffs)))
                logger.debug(f"Found first non-zero subresultant: {i}")
                break
        else:
            logger.debug(f"All subresultants are zero???")
        data["rk"] = gcd(Lb.order(), Pb.order())
        logger.info(f"### Finished the computation on a branch {ind+1}/{tot} ###")
        logger.info(f"##########################################################")
        final_output[branch] = data
    return final_output

def spectral_operators(L: DPolynomial, P: DPolynomial, name_lambda: str = "lambda_", name_mu: str = "mu"):
    r'''
        Method to create the spectral operators associated with two differential operators.
        
        This method assumes `L` and `P` are two linear differential operators in the same parent
        of the form `F[\textbf{x}]\{z\}`, i.e., one differential variable, then a set of algebraic variables
        (may or not be constant) and a base field `F` such that `\partial(F) = 0`.

        To create the spectral operators we need to add algebraically the two constants `\lambda` and 
        `\mu` to `F[\textbf{x}]` at the same level. Then we will need to add again the variable `z`.

        This method will then return the two operators `L_\lambda = L - \lambda` and `P_\mu = P - \mu`.
    '''
    DR = L.parent()
    if not P.parent() == DR: raise TypeError(f"[spectral] Method only implemented with same parent for operators.")

    ## We extract the main polynomial ring / base field
    PR = DR.base() # this is a wrapped of `F[x]`
    R = PR.wrapped # we removed the differential structure

    ## We check if the ring `R` is a FractionField or not
    was_fraction_field = is_FractionField(R)
    R = R.base() if was_fraction_field else R

    ## We treat the base ring `R`
    if R.is_field(): # case R is NumberField
        R = PolynomialRing(R, [name_lambda, name_mu])
    else: # We assume R is a polynomial ring
        R = PolynomialRing(R.base(), list(R.variable_names()) + [name_lambda, name_mu])
    l = R(name_lambda); m = R(name_mu)

    if was_fraction_field: # we set the type of ring to fraction_field if needed
        R = R.fraction_field() 

    ## At this point R is the desired algebraic base ring where `l`,`m` are the new variables.
    ## We add now the differential structure again
    gens_img = {str(v) : v.derivative() for v in PR.gens()}
    gens_img[name_lambda] = 0
    gens_img[name_mu] = 0
    PR = DifferentialRing(R, lambda p : gens_img[str(p)])

    ## We create again teh ring of differential polynomials
    DR = DifferentialPolynomialRing(PR, DR.variable_names())

    ## We cast everything to the goal ring
    z = DR.gens()[0]
    l = DR(l); m = DR(m)
    L = DR(L); P = DR(P)

    ## We return the spectral operators
    return L - l*z[0], P - m*z[0]

def __simplify(element, curve):
    r'''Reduces the element with the generator of a curve'''
    P = element.parent()
    if is_FractionField(P): # element is a rational function
        return __simplify(element.numerator(), curve) / __simplify(element.denominator(), curve)
    return element % curve

def BC_pair(L, P):
    r'''
        Algorithm BC_pair from :doi:`10.3842/sigma.2019.101` (Section 6).

        This method takes as input two operators that commute and computes a pair
        `(L,B)` that is a BC pair and its order.
    '''
    assert L.order() == 4, "[BC_pair] Only working for order `4` operators."
    ## We first compute the spectral curve of L and P
    sL, sP = spectral_operators(L, P)
    R = sL.parent()
    f = R.sylvester_resultant(sL, sP)
    h = f.coefficients()[0].wrapped.factor()[0][0]

    ## Now we compute the coefficient of "lambda" for the spectral curve
    b1 = h.coefficient({h.parent()("mu"): 1})
    M = P - sum(c*L.sym_power(m.degree()) for (c,m) in zip(b1.coefficients(), b1.monomials()))/2

    ## We check if M is zero
    if M == 0:
        return "The given operator `P` was a polynomial in `C[L]`"
    
    raise NotImplementedError(f"[BC_pair] Method not yet implemented")


__all__ = [
    "spectral_operators", "SpectralCurveOverIdeal",
    "BC_pair"    
]