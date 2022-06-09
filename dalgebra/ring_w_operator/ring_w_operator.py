r'''
Module containing the basic definitions for ore rings.

EXAMPLES::

    TODO

AUTHORS:

    - Antonio Jimenez-Pastor (2022-04-20): initial version
'''

from functools import lru_cache
from sage.all import CommutativeRing, ZZ, latex
from sage.categories.all import Morphism, Category, CommutativeRings
from sage.categories.map import Map #pylint: disable=no-name-in-module
from sage.categories.pushout import ConstructionFunctor, pushout
from sage.misc.abstract_method import abstract_method
from sage.structure.element import parent, Element #pylint: disable=no-name-in-module
from sage.structure.factory import UniqueFactory #pylint: disable=no-name-in-module
from sage.symbolic.ring import SR #pylint: disable=no-name-in-module

_CommutativeRings = CommutativeRings.__classcall__(CommutativeRings)

class RingsWithOperators(Category):
    # methods of the category itself
    def super_categories(self):
        return [_CommutativeRings]

    # methods that all differential structures must implement
    class ParentMethods:
        def operators(self):
            raise NotImplementedError

        def noperators(self):
            return len(self.operators())

        @abstract_method
        def operation(self, element, operator=0):
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
        def operation(self, times=1, operation=0):
            if(not times in ZZ or times < 0):
                raise ValueError("The argument ``times`` must be a non-negative integer")

            if(times == 0):
                return self
            elif(times == 1):
                return self._operation(operation=operation)
            else:
                return self.operation(times=times-1,operation=operation).operation(operation=operation)

        def _operation(self, operation=0, *_):
            r'''
                Method that actually computes the operation of an element of a ring with operator.
            '''
            return self.parent().operation(self,operation=operation) #pylint: disable=no-member

    # methods that all morphisms involving differential rings must implement
    class MorphismMethods: 
        pass

class RingWithOperatorFactory(UniqueFactory):
    def create_key(self, *args, **kwds):
        if "base" in kwds:
            base = kwds["base"]
            operators = args
        else:
            base = args[0]
            operators = args[1:]
        
        if operators is None:
            raise TypeError("No operators were given")
        elif not isinstance(operators,(list,tuple)):
            operators = [operators]

        if len(operators) == 0:
            raise TypeError("No operators were given")

        return (base, operators)

    def create_object(self, _, key):
        base, operators = key

        if base in RingsWithOperators:
            if base.noperators() != len(operators):
                raise ValueError("The number of operators does not match!")
            return base

        new_operators = []
        for operator in operators:
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
            new_operators.append(new_operator)
        
        return RingWithOperators_Wrapper(base, new_operators)

RingWithOperators = RingWithOperatorFactory("dalgebra.ring_w_operator.ring_w_operator.RingWithOperator")

class RingWithOperators_WrapperElement(Element):
    def __init__(self, parent, element):
        if(not isinstance(parent, RingWithOperators_Wrapper)):
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
    def _neg_(self):
        return self.parent().element_class(self.parent(), -self.wrapped)
    def _mul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _rmul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def _lmul_(self, x):
        return self.parent().element_class(self.parent(), self.wrapped * x.wrapped)
    def __pow__(self, n):
        return self.parent().element_class(self.parent(), self.wrapped ** n)

    def __eq__(self, x):
        if x is None: 
            return False
        r = pushout(self.parent(), parent(x))
        s, x = r(self), r(x)
        if isinstance(s.parent(), RingWithOperators_Wrapper):
            return s.wrapped == x.wrapped
        else:
            return s == x

    def is_zero(self):
        return self.wrapped == 0
    def is_one(self):
        return self.wrapped == 1

    ## Other magic methods
    def __hash__(self) -> int:
        return hash(self.wrapped)
    def __str__(self) -> str:
        return str(self.wrapped)
    def __repr__(self) -> str:
        return repr(self.wrapped)
    def _latex_(self) -> str:
        return latex(self.wrapped)

class RingWithOperators_Wrapper(CommutativeRing):
    Element = RingWithOperators_WrapperElement

    def __init__(self, base, operators, axioms=None, category=None):
        if not isinstance(operators, (list, tuple)):
            operators = [operators]
        if axioms is None:
            axioms = len(operators)*[None]
        elif not isinstance(axioms, (list, tuple)):
            axioms = len(operators)*[axioms]
        elif all(not isinstance(axiom, (list, tuple))):
            axioms = len(operators)*[axioms]
        else:
            if len(axioms) < len(operators):
                axioms += (len(operators) - len(axioms))*[None]
            for i in range(len(axioms)):
                if axioms[i] != None and not isinstance(axioms[i], (list, tuple)):
                    axioms[i] = [axioms[i]]

        # creating appropriate structure for operator
        new_operators = []
        for i in range(len(operators)):
            operator = operators[i]
            axiom = axioms[i]
            if not isinstance(operator, Map):
                raise TypeError("The operator must be a map")
            if not (operator.domain() == operator.codomain() == base):
                raise ValueError("The map must be withing the base ring")
            
            # testing the operator
            axiom = ["add_group_hom"] if axiom is None else axiom
            test = TestOperator(operator, axiom)
            if not test.test():
                raise ValueError(f"The operator {operator} do not satisfy the axioms {axiom}")

            # assigning values
            self.__base = base
            new_operator = lambda p : operator(p.wrapped)
            try:
                new_operator.__name__ = operator.__name__
            except AttributeError:
                try:
                    new_operator.__name__ = f"{list(base.gens())} |--> {operator.im_gens()}"
                except AttributeError:
                    new_operator.__name__ = "<callable>"
            new_operators.append(CallableMap(new_operator, self, self))
            
        self.__operators = new_operators

        # creating categories
        categories = [RingsWithOperators(), base.category()]
        if(isinstance(category, (list, tuple))):
            categories += list(category)
        elif(category != None): 
            categories.append(category) 

        CommutativeRing.__init__(self, base.base(), category=tuple(categories))

        # registering conversion to simpler structures
        current = self.base()
        morph = RingWithOperatorsPolySimpleMorphism(self, current)
        current.register_conversion(morph)
        while(not(current.base() == current)):
            current = current.base()
            morph = RingWithOperatorsPolySimpleMorphism(self, current)
            current.register_conversion(morph)

    @property
    def wrapped(self): return self.__base

    def operators(self): return self.__operators

    def operation(self, element, operation=0):
        return self.operators()[operation](element)

    ## Coercion methods
    def _has_coerce_map_from(self, S):
        r'''
            Standard implementation for ``_has_coerce_map_from``
        '''
        if S not in [str, list, tuple]:
            R = pushout(self, S)
            return (R is self)
        return False

    def _coerce_map_from_(self, S):
        if self._has_coerce_map_from(S):
            return CallableMap(lambda p : self.element_class(self, self.wrapped(p)), S, self)

    def _element_constructor_(self, x):
        r'''
            Extended definition of :func:`_element_constructor_`.
        '''
        if x in SR:
            x = str(x)
        p = self.wrapped._element_constructor_(x)
        return self.element_class(self, p)

    def _is_valid_homomorphism_(self, codomain, im_gens, base_map=None):
        return self.wrapped._is_valid_homomorphism_(codomain, im_gens, base_map)

    def __contains__(self, element):
        if(parent(element) in self.category()):
            return parent(element) == self
        try:
            self(element)
            return True
        except:
            return element in self.wrapped        

    def construction(self):
        return RingWithOperatorsFunctor(self.__operators), self.wrapped

    # Rings methods
    def characteristic(self):
        return self.wrapped.characteristic()

    def gens(self):
        return tuple([self(gen) for gen in self.wrapped.gens()])

    def ngens(self):
        return self.wrapped.ngens()

    ## Representation methods
    def __repr__(self) -> str:
        return f"Ring [{self.wrapped}] with operator [{repr(self.operators())}]"

    def __str__(self):
        return repr(self)

    def _latex_(self):
        return r"\left(" + latex(self.wrapped) + ", " + latex(self.operators()) + r"\right)"

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

                sage: from dalgebra import RingWithOperator
                sage: R = RingWithOperator(QQ['x'], lambda p : diff(p))
                sage: R.zero()
                0
        '''
        return self.element_class(self, self.wrapped(0))
    
    def random_element(self,*args,**kwds):
        r'''
            Creates a random element in this ring.

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
        try:
            self.__name__ = function.__name__
        except AttributeError:
            self.__name__ = str(function)

    def _call_(self, element):
        return self.codomain()(self.__method(element))

    def __str__(self):
        return self.__repr__() + f"\n\tFrom {self.domain()}\n\tTo {self.codomain()}"

    def __repr__(self):
        return f"Map from callable {self.__name__}"

    def _latex_(self):
        out = r"\begin{array}{rcl}"
        out += r"\\".join([latex(el) + r"\mapsto" + latex(self(el)) for el in self.domain().gens()])
        out += r"\end{array}"
        return out

class RingWithOperatorsFunctor(ConstructionFunctor):
    def __init__(self, operators):
        self.__operators = operators
        super().__init__(RingsWithOperators(),RingsWithOperators())
        
    ### Methods to implement
    def _coerce_into_domain(self, x):
        if(x not in self.domain()):
            raise TypeError("The object [%s] is not an element of [%s]" %(x, self.domain()))
        return x
        
    def _apply_functor(self, x):
        return RingWithOperators(x,self.__operators)
        
    def _repr_(self):
        return "RingWithOperators(*,[%s])" %(repr(self.__operators))
        
    def __eq__(self, other):
        if(other.__class__ == self.__class__):
            return (other.__operators == self.__operators)

    def merge(self, other):
        pass

    def operators(self):
        return self.__operators

class RingWithOperatorsPolySimpleMorphism (Morphism):
    r'''
        Class representing maps to simpler rings.

        This map allows the coercion system to detect that some elements in a 
        :class:`RingWithOperator_Wrapper` are included in simpler rings.
    '''
    def __init__(self, domain, codomain):
        super().__init__(domain, codomain)
        
    def _call_(self, p):
        return self.codomain()(p.wrapped)


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
        if "derivation" in self.axioms:
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

__all__ = ["RingsWithOperators", "RingWithOperators"]