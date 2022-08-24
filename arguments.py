from __future__ import annotations

from typing import TYPE_CHECKING, Callable
from props import *
from unification import *

if TYPE_CHECKING:
    from proof import Line, Context
    

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


class Deduction(Argument):
    def __init__(self, hyp: Prop, ded: set[Prop]) -> None:
        self.hyp = hyp
        self.ded = ded
        
    def typecheck(self, expected: Prop) -> bool:
        assert isinstance(expected, Imp), f'Cannot use deduction rule on `{expected}`, as its not an implication!'
        hyp = expected.p
        ded = expected.q
        assert ded in self.ded, f'Cannot deduce `{ded}` from proof!'
        assert hyp == self.hyp, f'Proof does not take `{hyp}` as its hypothesis!'
        return True


class Conjunction(Argument):
    def __init__(self, p: Line, q: Line) -> None:
        self.p = p
        self.q = q
    def typecheck(self, expected: Prop) -> bool:
        assert And(self.p.typ, self.q.typ) == expected, f'Expected `{expected}`, but got type `{And(self.p.typ, self.q.typ)}`!'
        return True

class Disjunction(Argument):
    def __init__(self, p: Line, q: Line) -> None:
        self.p = p
        self.q = q
    def typecheck(self, expected: Prop) -> bool:
        assert Or(self.p.typ, self.q.typ) == expected, f'Expected `{expected}`, but got type `{Or(self.p.typ, self.q.typ)}`!'
        return True



argument_lookup: dict[str, Callable[[list[Line]], Argument]] = {
    'mp': lambda args: ModusPonens(*args),
    'mt': lambda args: ModusTollens(*args),
    'simp': lambda args: Simplify(*args),
    'add': lambda args: Addition(*args),
    'hs': lambda args: HypotheticalSyllogism(*args),
    'ds': lambda args: DisjunctiveSyllogism(*args),
    'de': lambda args: DisjunctiveElimination(*args),
    'conj': lambda args: Conjunction(*args),
    'disj': lambda args: Disjunction(*args),
    'hyp': lambda args: Hypothesis(*args),  # type: ignore
    'prem': lambda args: Hypothesis(*args), # type: ignore
    
    'or_comm': lambda args: OrComm(*args),
    'and_comm': lambda args: AndComm(*args),
    'or_assoc': lambda args: OrAssoc(*args),
    'and_assoc': lambda args: AndAssoc(*args),
    'dn': lambda args: DoubleNeg(*args),
    'imp': lambda args: ImplEquiv(*args),
    'dist_ao': lambda args: DistribAndOr(*args),
    'dist_oa': lambda args: DistribOrAnd(*args),
    'dm_ao': lambda args: DemorganAndOr(*args),
    'dm_oa': lambda args: DemorganOrAnd(*args),
    'exp': lambda args: Exportation(*args),
    'cp': lambda args: Contrapositive(*args)
}

class UninterpJust:
    def __init__(self, name: str, args: list[int]) -> None:
        self.name = name
        self.args = args
        
    def interpret(self, ctx: Context) -> Argument:
        if self.name == 'ded':
            assert tuple(sorted(self.args)) in ctx.proofs, f'{min(self.args)}-{max(self.args)} does not denote a complete proof!'
            proof = ctx.proofs[tuple(sorted(self.args))]
            hyp, ded = ctx.proof_types[proof]
            assert len(hyp) == 1, f'A proof that uses multiple hypotheses cannot be used in the deduction rule! (hypotheses={hyp})'
            return Deduction(list(hyp)[0], ded)
            
        assert self.name in argument_lookup, f'{self.name} is not a recognized justification!'
        lines = [ctx.lines[arg] for arg in self.args]
        return argument_lookup[self.name](lines)
    
    def __repr__(self) -> str:
        return f'{self.name} {self.args}'