r'''
Module containing the basic definitions for ore rings.

EXAMPLES::

    TODO

AUTHORS:

    - Antonio Jimenez-Pastor (2022-04-20): initial version
'''

from functools import lru_cache
from sage.all import CommutativeRing, ZZ, latex
from sage.categories.all import Category, CommutativeRings
from sage.categories.map import Map
from sage.categories.pushout import pushout
from sage.misc.abstract_method import abstract_method
from sage.structure.element import Element #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)

class RingsWithOperator(Category):
    # methods of the category itself
    def super_categories(self):
        return [_CommutativeRings]

    # methods that all differential structures must implement
    class ParentMethods:
        @abstract_method
        def operation(self, _):
            raise NotImplementedError

        @abstract_method
        def operator_ring(self):
            r'''
                Method that returns the structure for the ring of linear operators

                The ring defined in ``self`` and the operator included with it define 
                a natural ring of operators `R[d]` where `R` is the ring and `d` is 
                the operator. 

                In many cases, these rings are not commutative and are defined from 
                the commutativity rule of `d \cdot a = f(a) d` for some function `f`.
                Each ring with operator should include a method to return this new 
                ring of linear operators.
            '''
            raise NotImplementedError

    # methods that all differential elements must implement
    class ElementMethods:
        def operation(self, times=1):
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self._operation()
            else:
                return self.operation(times=times-1).operation()

        def _operation(self, *_):
            r'''
                Method that actually computes the operation of an element of a ring with operator.
            '''
            return self.parent().operation(self)

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class RingWithOperatorFactory(UniqueFactory):
    def create_key(self, *args, **kwds):
        ## Allowing the args input to not be unrolled
        if(len(args) == 1 and type(args[0]) in (list, tuple)):
            args = args[0]
        
        if len(args) == 0:
            base = kwds["base"]; operator = kwds["operator"]
        if len(args) == 1:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            base = args[0]; operator = kwds["operator"]
        elif len(args) == 2:
            if "base" in kwds:
                raise TypeError("Duplicated value for the base ring")
            if "operator" in kwds:
                raise TypeError("Duplicated value for the operator")
            base = args[0]; operator = args[1]

        return (base, operator)

    def create_object(self, _, key):
        base, operator = key

        if base in RingsWithOperator:
            # check equality of the operators?
            return base

        if isinstance(operator, Map):
            try:
                domain_po = pushout(operator.domain(), base)
                codomain_po = pushout(operator.codomain(), base) 
                if not domain_po == base:
                    raise TypeError(f"The domain [{operator.domain()}] must be something to be coerced into {base}")
                if not codomain_po == base:
                    raise TypeError(f"The codomain [{operator.codomain()}] must be something to be coerced into {base}")

                if domain_po != operator.domain() or codomain_po != operator.codomain():
                    new_operator = CallableMap(lambda p : operator(p), base, base)
            except:
                raise ValueError(f"{operator.domain()} or {operator.codomain()} could not be pushed into common parent with {base}")
        elif callable(operator):
            new_operator = CallableMap(operator, base, base)

        return RingWithOperator_Wrapper(base, new_operator)

RingWithOperator = RingWithOperatorFactory("dalgebra.ring_w_operator.ring_w_operator.RingWithOperator")

class RingWithOperator_WrapperElement(Element):
    def __init__(self, parent, element):
        if(not isinstance(parent, RingWithOperator_Wrapper)):
            raise TypeError("An element created from a non-wrapper parent")
        elif(not element in parent.wrapped):
            raise TypeError("An element outside the parent [%s] is requested" %parent)

        Element.__init__(self, parent=parent)
        self.__wrapped = element

    @property
    def wrapped(self): return self.__wrapped

    # Arithmetic methods
    def _add_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped + x.wrapped)
    def _sub_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped - x.wrapped)
    def _mul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _rmul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _lmul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), self.wrapped ** n)
    def __str__(self):
        return str(self.wrapped)
    def __repr__(self) -> str:
        return repr(self.wrapped)

class RingWithOperator_Wrapper(CommutativeRing):
    Element = RingWithOperator_WrapperElement

    def __init__(self, base, operator,axioms=None, category=None):
        # creating appropriate structure for operator
        if not isinstance(operator, Map):
            raise TypeError("The operator must be a map")
        if not (operator.domain() == operator.codomain() == base):
            raise ValueError("The map must be withing the base ring")
        
        # testing the operator
        axioms = ["add_group_hom"] if axioms is None else axioms
        test = TestOperator(operator, axioms)
        if not test.test():
            raise ValueError(f"The operator {operator} fo not satisfy the axioms {axioms}")

        # assigning values
        self.__base = base
        new_operator = lambda p : operator(p.wrapped); new_operator.__name__ = operator.__name__
        self.__operator = CallableMap(new_operator, self, self)

        # creating categories
        categories = [RingsWithOperator(), base.category()]
        if(isinstance(category, (list, tuple))):
            categories += list(category)
        elif(category != None): 
            categories.append(category) 

        CommutativeRing.__init__(self, base.base(), category=tuple(categories))

    @property
    def wrapped(self): return self.__base

    @property
    def operator(self): return self.__operator

    def operation(self, element):
        return self.operator(element)

    ## Coercion methods
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        coer =  self._coerce_map_from_(S)
        return (not(coer is False) and not(coer is None))

    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.

            Uses the construction of the class :class:`~sage.rings.polynomial.infinite_polynomial_ring.InfinitePolynomialRing_dense`
            and then transforms the output into a :class:`~dalgebra.differential_polynomial.differential_polynomial_element.DiffPolynomial`.
        '''
        p = self.wrapped._element_constructor_(x)
        return self.element_class(self, p)

    def __call__(self, *args, **kwds):
        try:
            res = self.wrapped(*args, **kwds)
            return self.element_class(self, res)
        except:
            super().__call__(*args, **kwds)

    def __contains__(self, element):
        if(element.parent() in RingsWithOperator):
            return element.parent() == self
        return element in self.wrapped        

    # Rings methods
    def characteristic(self):
        return self.wrapped.characteristic()

    ## Representation methods
    def __repr__(self) -> str:
        return f"Ring [{self.wrapped}] with operator [{repr(self.operator)}]"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        return r"\left(" + latex(self.wrapped) + ", " + latex(self.operator) + r"\right)"

    ## Element generation
    def one(self):
        r'''
            Return the one element in ``self``.

            EXAMPLES::

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], diff)
                sage: R.one()
                1
        '''
        return self.element_class(self, self.wrapped(1))
    
    def zero(self):
        r'''
            Return the zero element in ``self``.

            EXAMPLES::

                sage: from dalgebra import DiffPolynomialRing
                sage: R.<y> = DiffPolynomialRing(QQ['x'])
                sage: R.zero()
                0
        '''
        return self.element_class(self, self.wrapped(0))
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a randome element in this ring.

            This method creates a random element in the base infinite polynomial ring and 
            cast it into an element of ``self``.
        '''
        p = self.wrapped.random_element(*args,**kwds)
        return self(p)
        
class CallableMap(Map):
    def __init__(self, function, domain, codomain):
        super().__init__(domain, codomain)
        if not callable(function):
            raise TypeError("The argument function must be callable")
        self.__method = function

    def _call_(self, element):
        return self.codomain()(self.__method(element))

    def __str__(self):
        return self.__repr__() + f"\n\tFrom {self.domain()}\n\tTo {self.codomain()}"

    def __repr__(self):
        return f"Map from callable {self.__name__}"

    @property
    def __name__(self):
        return self.__method.__name__

class TestOperator:
    def __init__(self, operator, axioms, random = True, ntests = 10):
        # Checking the input
        if not isinstance(operator, Map):
            raise TypeError("The operator must be a map between two rings")
        elif not isinstance(operator.domain(), CommutativeRing):
            raise TypeError("The domain must be a CommutativeRing")
        elif not isinstance(operator.codomain(), CommutativeRing):
            raise TypeError("The codomain must be a CommutativeRing")

        # Assigning values
        self.__operator = operator
        self.__axioms = axioms
        self.__random = random
        self.__ntests = ntests

    @property
    def operator(self): return self.__operator

    @property
    def axioms(self): return self.__axioms

    @lru_cache
    def compute_test(self):
        to_test = set()
        if "derivative" in self.axioms:
            to_test.add(self.is_additive_homomorphism)
            to_test.add(self.is_leibniz)
        elif "homomorphism" in self.axioms:
            to_test.add(self.is_additive_homomorphism)
            to_test.add(self.is_multiplicative_homomorphism)
        elif "add_group_hom" in self.axioms:
            to_test.add(self.is_additive_homomorphism)
        elif "mult_group_hom" in self.axioms:
            to_test.add(self.is_multiplicative_homomorphism)
        
        return to_test

    def test(self):
        return all(test() for test in self.compute_test())

    def is_leibniz(self):
        cases = []
        # basic test cases
        cases.append((0,0,0))
        cases.append((0,1,0))
        cases.append((1,1,0))

        # random cases
        if self.__random:
            for _ in range(self.__ntests):
                a, b = self.operator.domain().random_element(), self.operator.domain().random_element()
                res = self.operator(a)*b + a*self.operator(b)
                cases.append((a,b,res))

        return all(case[2] == self.operator(case[0]*case[1]) for case in cases)

    def is_multiplicative_homomorphism(self):
        cases = []
        # basic test cases
        cases.append((0,0,0))
        cases.append((0,1,0))
        cases.append((1,1,self.operator(1)**2))

        # random cases
        if self.__random:
            for _ in range(self.__ntests):
                a, b = self.operator.domain().random_element(), self.operator.domain().random_element()
                res = self.operator(a)*self.operator(b)
                cases.append((a,b,res))

        return all(case[2] == self.operator(case[0]*case[1]) for case in cases)

    def is_additive_homomorphism(self):
        cases = []
        # basic test cases
        cases.append((0,0,0))
        cases.append((0,1,self.operator(1)))
        cases.append((1,1,2*self.operator(1)))

        # random cases
        if self.__random:
            for _ in range(self.__ntests):
                a, b = self.operator.domain().random_element(), self.operator.domain().random_element()
                res = self.operator(a)+self.operator(b)
                cases.append((a,b,res))

        return all(case[2] == self.operator(case[0]+case[1]) for case in cases)