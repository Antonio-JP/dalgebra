from __future__ import annotations
r'''
    Module to include some modification on SageMath behavior on Quotient rings.

    For further information about the original code, see: https://github.com/sagemath/sage/blob/main/src/sage/rings/quotient.py.
'''

from sage.structure.element import Element
from sage.misc.cachefunc import cached_method
from sage.rings.quotient_ring import QuotientRing_generic
from sage.rings.quotient_ring_element import QuotientRingElement

class QuotientRingElement_extended(QuotientRingElement):
    r"""
        A class to extend the behavior of the QuotientRingElement class.
    """

    def __init__(self, parent, rep, reduce=True):
        super().__init__(parent, rep, reduce=reduce)

    def gcd(self, other: QuotientRingElement_extended) -> QuotientRingElement_extended:
        r"""
            Compute the gcd of two elements in the quotient ring.
            This method is overridden to handle cases where the ambient ring is infinite.
        """
        lself, lother = self.lift(), other.lift() # they are now polynomials over a field
        g = self.parent()(lself.gcd(lother)) # this reduces module the ideal

        c = self.content().gcd(other.content()) # this is the content of the elements

        return c*g 

    def content(self) -> Element:
        from sage.arith.misc import GCD
        return GCD(self.lift().coefficients())

class QuotientRing_extended(QuotientRing_generic):
    r"""
        A class to extend the behavior of the QuotientRing_generic class.
    """
    Element = QuotientRingElement_extended

    def __init__(self, R, I, names, category=None):
        if R.is_finite():
            raise ValueError("The base ring must be infinite for quotient rings.")
        super().__init__(R, I, names, category=category)

    @cached_method
    def is_finite(self):
        r"""
            Return whether the quotient ring is finite. In this case it is always false, since the ambient ring is infinite.
        """ 
        return False
