from __future__ import annotations

from typing import TYPE_CHECKING
from props import *

if TYPE_CHECKING:
    from proof import Line

class Argument:
    def typecheck(self, expected: Prop) -> bool:
        raise NotImplemented
    

class ModusPonens(Argument):
    def __init__(self, imp: Line, ante: Line) -> None:
        self.imp = imp
        self.ante = ante
        
    def typecheck(self, expected: Prop) -> bool:
        return apply(self.imp.typ, self.ante.typ) == expected
    
    def __repr__(self) -> str:
        return f'mp {self.imp.num}, {self.ante.num}'


class ModusTollens(Argument):
    def __init__(self, imp: Line, cont: Line) -> None:
        self.imp = imp
        self.cont = cont
        
    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(self.cont.typ, Imp) and self.cont.typ.q is False, f'{self.cont.num}: {self.cont.typ} is not a negation!'
        return compose(self.imp.typ, self.cont.typ) == expected
    
    def __repr__(self) -> str:
        return f'{self.imp.num}, {self.cont.num}'
    

class Simplify(Argument):
    def __init__(self, conj: Line) -> None:
        self.conj = conj
        
    def typecheck(self, expected: Prop) -> bool:
        return expected in (proj_L(self.conj.typ), proj_R(self.conj.typ))
    
    def __repr__(self) -> str:
        return f'simp {self.conj.num}'
    
    
class Addition(Argument):
    def __init__(self, disj: Line) -> None:
        self.disj = disj
        
    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(expected, Or), f'{expected} is not a disjunction!'
        return self.disj.typ in (expected.p, expected.q)
    
    def __repr__(self) -> str:
        return f'add {self.disj.num}'
    
class HypotheticalSyllogism(Argument):
    def __init__(self, imp1: Line, imp2: Line) -> None:
        self.imp1 = imp1
        self.imp2 = imp2
        
    def typecheck(self, expected: Prop) -> bool:
        return compose(self.imp1.typ, self.imp2.typ) == expected
    
    def __repr__(self) -> str:
        return f'hs {self.imp1.num}, {self.imp2.num}'
    
    
class DisjunctiveSyllogism(Argument):
    def __init__(self, disj: Line, neg: Line) -> None:
        self.disj = disj
        self.neg = neg
        
    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(self.disj.typ, Or), f'{self.disj.num}: {self.disj.typ} is not a disjunction!'
        assert inspect_not(self.neg.typ) in (self.disj.typ.p, self.disj.typ.q)
        return expected in (self.disj.typ.p, self.disj.typ.q)
    
    def __repr__(self) -> str:
        return f'ds {self.disj.num}, {self.neg.num}'
    
    
class DisjunctiveElimination(Argument):
    def __init__(self, disj: Line, imp1: Line, imp2: Line) -> None:
        self.disj = disj
        self.imp1 = imp1
        self.imp2 = imp2
        
    def typecheck(self, expected: Prop) -> bool:
        imp = univ_coprod(self.imp1.typ, self.imp2.typ)
        stack = apply(imp, self.disj.typ)
        return codiag(stack) == expected
    
    def __repr__(self) -> str:
        return f'de {self.disj.num}, {self.imp1.num}, {self.imp2.num}'
    
    
class Hypothesis(Argument):
    def typecheck(self, expected: Prop) -> bool:
        return True

    def __repr__(self) -> str:
        return 'hyp'