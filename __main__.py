from argparse import ArgumentParser
from parser import proof, ProofActionWithContext
from proof import Context
from pyparsing import ParseException


if __name__ == '__main__':
    
    ctx = Context()
    proof.add_parse_action(ProofActionWithContext(ctx))

    parser = ArgumentParser()
    parser.add_argument('input_file', type=str)
    args = parser.parse_args()
    try:
        proof.parse_file(args.input_file)
        print('Parsed successfully!')
        if ctx.check():
            assert ctx.main_proof is not None
            hyp, deds = ctx.proof_types[ctx.main_proof]
            for ded in deds:
                print(f'{{ {", ".join(map(str, hyp))} |- {ded}')
        
    except ParseException as e:
        print(e.explain())