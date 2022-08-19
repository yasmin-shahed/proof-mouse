from props import *
from arguments import *
from unification import *

class Line:
    def __init__(self, num: int, typ: Prop, arg: Argument) -> None:
        self.num = num
        self.typ = typ
        self.arg = arg
        
        print(self)
        try:
            assert self.arg.typecheck(self.typ), f'Cannot use `{self.arg}` to produce {self.typ}!'
        except AssertionError as e:
            print(f'\tError: {e}')
            quit()
        
    def __repr__(self) -> str:
        return f'{self.num}. {self.typ} {self.arg}'
    

A = BaseProp('A')
B = BaseProp('B')
C = BaseProp('C')

proof = {}
proof[1] = Line(1, Imp(Or(B, A), C), Hypothesis())
proof[2] = Line(2, A, Hypothesis())
proof[3] = Line(3, Or(A, B), Addition(proof[2]))
proof[4] = Line(4, Or(B, A), OrComm(proof[3]))
proof[5] = Line(5, C, ModusPonens(proof[1], proof[4]))
