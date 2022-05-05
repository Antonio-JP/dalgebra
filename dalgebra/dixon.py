from sage.all import PolynomialRing, Matrix

from sage.categories.pushout import pushout
from sage.rings.polynomial.polynomial_ring import is_PolynomialRing
from sage.rings.polynomial.multi_polynomial_ring import is_MPolynomialRing

def cayley_polynomial(p1, p2):
    ## Setting up the input to be univariate polynomials
    R = pushout(p1.parent(), p2.parent())

    if(not (is_PolynomialRing(R) or (is_MPolynomialRing(R) and R.ngens()==1))):
        raise TypeError("The Cayley method only work for univariate polynomials")

    if(is_MPolynomialRing(R)):
        R = PolynomialRing(R.base(), R.gens()[0])

    p1 = R(p1); p2 = R(p2)

    ## Creating one extra variable:
    S = PolynomialRing(R.base(), [R.gens()[0], 'aux_var'])
    x,a = S.gens()
    num = p1(**{str(x): x})*p2(**{str(x): a}) - p1(**{str(x): a})*p2(**{str(x): x})
    den = x - a
    
    return num//den, S, (x,a)

def cayley_matrix(p1,p2):
    dixon_poly, S, (x,a) = cayley_polynomial(p1,p2)

    d = max(p1.degree(),p2.degree())
    return Matrix(S.base(), [[dixon_poly.coefficient({x:j, a:i}) for j in range(d)] for i in range(d)])