
from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Dict
from props import *

if TYPE_CHECKING:
    from proof import Line


def unify(p: Prop, q: Prop, subst: Dict[str, Prop]={}, var_subst: Dict[str, PredVar]={}) -> bool:
    if PropHole in (type(p), type(q)):
        if type(p) is PropHole:
            hole, exp = p.name, q
        else:
            assert type(q) is PropHole # mypy
            hole, exp = q.name, p
            
        if hole in subst:
            return subst[hole] == exp
        
        subst[hole] = exp
        return True
    
    if PredVarHole in (type(p), type(q)):
        if type(p) is PredVarHole:
            hole, exp = p.name, q
        else:
            assert type(q) is PredVarHole
            hole, exp = q.name, p
    
        if not (type(exp) is PredVar):
            return False
        
        if hole in var_subst:
            return var_subst[hole] == exp
    
        var_subst[hole] = exp
        return True
        
        
    
    # match p, q:
    #     case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
    #         return unify(a, c, subst) and unify(b, d, subst)
    #     case PropVar(a), PropVar(b):
    #         assert False, 'Whoops! I need to implement this :)'
    #     case (True, True) | (False, False):
    #         return True
    #     case BaseProp(a), BaseProp(b):
    #         return a == b
    #     case _:
    #         return False
    
    
    if (isinstance(p, And) and isinstance(q, And)) or ((isinstance(p, Or) and isinstance(q, Or))) or ((isinstance(p, Imp) and isinstance(q, Imp))):
        return unify(p.p, q.p, subst, var_subst) and unify(p.q, q.q, subst, var_subst)
    elif isinstance(p, PropHole) and isinstance(q, PropHole):
        assert False, 'Whoops! I need to implement this :)'
    elif isinstance(p, bool) and isinstance(q, bool):
        return p == q
    elif (isinstance(p, BaseProp) and isinstance(q, BaseProp)) or (isinstance(p, PredVar) and isinstance(q, PredVar)):
        return p.name == q.name
    elif (isinstance(p, ForAll) and isinstance(q, ForAll)) or (isinstance(p, Exists) and isinstance(q, Exists)):
        return unify(p.var, q.var, subst, var_subst) and unify(p.formula, q.formula, subst, var_subst)
    elif isinstance(p, Predicate) and isinstance(q, Predicate):
        return p.name == q.name and len(p.args) == len(q.args) and all(unify(xp, xq) for xp, xq, in zip(p.args, q.args))
    else:
        assert type(p) != type(q)
        return False
        
def diff_tree(p: Prop, q: Prop) -> tuple[Prop, Prop]:
    if (isinstance(p, And) and isinstance(q, And)) or ((isinstance(p, Or) and isinstance(q, Or))) or ((isinstance(p, Imp) and isinstance(q, Imp))):
        if p.p != q.p and p.q != q.q:
            return p, q
        if p.p == q.p:
            return diff_tree(p.q, q.q)
        if p.q == q.q:
            return diff_tree(p.p, q.p)
        assert False, f'{p} == {q}'
    elif (isinstance(p, ForAll) and isinstance(q, ForAll)) or (isinstance(p, Exists) and isinstance(q, Exists)):
        if p.var == q.var:
            return diff_tree(p.formula, q.formula)
        return p, q
    elif isinstance(p, Predicate) and isinstance(q, Predicate):
        assert p != q, f'{p} == {q}'
        return p, q
    else:
        return p, q
    # match p, q:
    #     case (And(a, b), And(c, d)) | (Or(a, b), Or(c, d)) | (Imp(a, b), Imp(c, d)):
    #         if a != c and b != d:
    #             return p, q
    #         if a == c:
    #             return diff_tree(b, d)
    #         if b == d:
    #             return diff_tree(a, c)
    #         assert False, f'{p} == {q}!'
    #     case _:
    #         return p, q
        
def try_rewrite(transformation, rule):
    if transformation[0] == transformation[1]:
        return {}
    old_t, new_t = diff_tree(*transformation)
    old_r, new_r = rule
    
    def rewrite():
        subst = {}
        var_subst = {}
        assert unify(old_t, old_r, subst, var_subst) and unify(new_t, new_r, subst, var_subst), f'Failed to apply rule {old_r} <=> {new_r} to {transformation[0]} => {transformation[1]}!'
        return subst, var_subst
    
    try:
        return rewrite()
    except AssertionError:
        old_r, new_r = new_r, old_r
        return rewrite()

    
class Argument:
    def verify(self, line: Line):
        return self.typecheck(line.typ)
    
    def typecheck(self, _: Prop) -> bool:
        raise NotImplemented
    
    
def make_argument(rule: tuple[Prop, Prop], name: str) -> Callable[[Line], Argument]:
    class RW(Argument):
        def __init__(self, old: Line) -> None:
            self.old = old
            
        def typecheck(self, new: Prop) -> bool:
            try_rewrite((self.old.typ, new), rule)
            return True
        
        def __repr__(self) -> str:
            return f'{name} {self.old.num}'
            
    return RW

a, b, c = PropHole('a'), PropHole('b'), PropHole('c')

# comm
or_comm = Or(a, b), Or(b, a)
and_comm = And(a, b), And(b, a)

# assoc
or_assoc = Or(Or(a, b), c), Or(a, Or(b, c))
and_assoc = And(And(a, b), c), And(a, And(b, c))

# double negation
double_neg = a, Imp(Imp(a, False), False)

# contrapositive
cp = Imp(a, b), Imp(Not(b), Not(a))

# implication equivalence
impl_equiv = Imp(a, b), Or(Not(a), b)

# distributivity
distr_and_or = And(a, Or(b, c)), Or(And(a, b), And(a, c))
distr_or_and = Or(a, And(b, c)), And(Or(a, b), Or(a, c))

# demorgan's laws
demorgan_and_or = Not(And(a, b)), Or(Not(a), Not(b))
demorgan_or_and = Not(Or(a, b)), And(Not(a), Not(b))

# self
self_or = a, Or(a, a)
self_and = a, And(a, a)

# exportation
exp = Imp(a, Imp(b, c)), Imp(And(a, b), c)

# quantified demorgan's laws
x, y, z = PredVarHole('x'), PredVarHole('y'), PredVarHole('z')
demorgan_forall_exists = Not(ForAll(x, a)), Exists(x, Not(a))
demorgan_exists_forall = Not(Exists(x, a)), ForAll(x, Not(a))

# alpha equivalence


# turn these all into arguments
OrComm = make_argument(or_comm, 'comm')
AndComm = make_argument(and_comm, 'comm')
OrAssoc = make_argument(or_assoc, 'assoc')
AndAssoc = make_argument(and_assoc, 'assoc')
DoubleNeg = make_argument(double_neg, 'dn')
ImplEquiv = make_argument(impl_equiv, 'impl')
DistribAndOr = make_argument(distr_and_or, 'dist')
DistribOrAnd = make_argument(distr_or_and, 'dist')
DemorganAndOr = make_argument(demorgan_and_or, 'dm')
DemorganOrAnd = make_argument(demorgan_or_and, 'dm')
DemorganForallExists = make_argument(demorgan_forall_exists, 'dm')
DemorganExistsForall = make_argument(demorgan_exists_forall, 'dm')
Exportation = make_argument(exp, 'exp')
Contrapositive = make_argument(cp, 'cp')
SelfOr = make_argument(self_or, 'self_or')
SelfAnd = make_argument(self_and, 'self_and')

__all__ = [
    'Argument',
    'OrComm', 'AndComm', 'OrAssoc', 'AndAssoc', 
    'DoubleNeg', 'ImplEquiv', 
    'DistribAndOr', 'DistribOrAnd', 
    'DemorganAndOr', 'DemorganOrAnd',
    'DemorganForallExists', 'DemorganExistsForall',
    'Exportation',
    'Contrapositive',
    'SelfOr', 'SelfAnd'
]


# A, B, C, D = BaseProp('A'), BaseProp('B'), BaseProp('C'), BaseProp('D')

# old = Imp(And(A, And(B, C)), D)
# new = Imp(And(And(A, B), C), D)

# try:
#     print(try_rewrite((old, new), or_assoc))
# except AssertionError as e:
#     print(e)