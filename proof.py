from props import *
from arguments import *
from unification import *

class Line:
    def __init__(self, num: int, typ: Prop, just: UninterpJust) -> None:
        self.num = num
        self.typ = typ
        self.just = just
    def check(self):
        self.arg = self.just.interpret()
        try:
            assert self.arg.typecheck(self.typ), f'Cannot use `{self.arg}` to produce {self.typ}!'
        except AssertionError as e:
            print(f'\tError: {e}')
            quit()
        
    def __repr__(self) -> str:
        return f'{self.num}. {self.typ} {self.just}'
    

class Proof:
    def __init__(self, lines: list[Line]):
        self.lines: dict[int, Line] = {}
        for line in lines:
            self.lines[line.num] = line
            
    def compile(self) -> tuple[set[Prop], set[Prop]]:
        assumptions: set[Prop] = set()
        results: set[Prop] = set()
        
        for line in self.lines.values():
            if isinstance(line.arg, Hypothesis):
                assumptions.add(line.typ)
            else:
                results.add(line.typ)
        
        return assumptions, results
    
    def __repr__(self) -> str:
        return '\n'.join(map(repr, self.lines.values()))



@dataclass
class Context:
    lines: dict[int, Line]
    proof_types: dict[Proof, tuple[set[Prop], set[Prop]]]
    proofs: dict[tuple[int, ...], Proof]
    
    def add_proof(self, proof: Proof):
        self.lines.update(proof.lines)
        self.proofs[tuple(sorted(proof.lines.keys()))] = proof
        
    def register_type(self, proof: Proof, typ: tuple[set[Prop], set[Prop]]):
        self.proof_types[proof] = typ