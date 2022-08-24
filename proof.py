from __future__ import annotations

from props import *
from arguments import Hypothesis, UninterpJust
from unification import *

class Line:
    def __init__(self, num: int, typ: Prop, just: UninterpJust) -> None:
        self.num = num
        self.typ = typ
        self.just = just
        
    def check(self, ctx: Context):
        self.arg = self.just.interpret(ctx)
        assert self.arg.typecheck(self.typ), f'Cannot use `{self.arg}` to produce {self.typ}!'
        
    def __repr__(self) -> str:
        return f'{self.num}. {self.typ} {self.just}'
    

class Proof:
    def __init__(self, lines: list[Line]):
        self.lines: dict[int, Line] = {}
        for line in lines:
            self.lines[line.num] = line
            
    def compile(self, ctx: Context) -> tuple[set[Prop], set[Prop]]:
        assumptions: set[Prop] = set()
        results: set[Prop] = set()
        
        for line in self.lines.values():
            if isinstance(line.arg, Hypothesis):
                assumptions.add(line.typ)
            else:
                results.add(line.typ)
        ctx.register_type(self, (assumptions, results))
        return assumptions, results
    
    def __repr__(self) -> str:
        return '\n'.join(map(repr, self.lines.values()))




class Context:
    def __init__(self) -> None:
        self.lines: dict[int, Line] = {}
        self.proof_types: dict[Proof, tuple[set[Prop], set[Prop]]] = {}
        self.proofs: dict[tuple[int, ...], Proof] = {}
        self.main_proof: Proof | None = None
    
    def add_proof(self, proof: Proof):
        self.lines.update(proof.lines)
        self.proofs[tuple(sorted(proof.lines.keys()))] = proof
        self.main_proof = proof
        
    def register_type(self, proof: Proof, typ: tuple[set[Prop], set[Prop]]):
        self.proof_types[proof] = typ
        
    def check(self) -> bool:
        if self.main_proof is None:
            print('** No proofs added! **')
            return False
        try:
            remaining_proofs = set(self.proofs.values())
            lines_checked: set[int] = set()
            
            for num in sorted(self.lines.keys()):
                print(f'Checking line: {self.lines[num]}')
                self.lines[num].check(self)
                lines_checked.add(num)
                
                for lines in self.proofs:
                    if self.proofs[lines] in remaining_proofs and set(lines).issubset(lines_checked):
                        self.proofs[lines].compile(self)
                        remaining_proofs.remove(self.proofs[lines])
                
            return True
        except AssertionError as e:
            print(f'Error: {e}')
            return False