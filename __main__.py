from argparse import ArgumentParser
from concurrent.futures import process
from parser import proof, ProofActionWithContext
from proof import Context
from pyparsing import ParseException

def preprocess(lines: list[str]) -> list[str]:
    processed_lines: list[str] = []
    block = []
    for line in lines:
        if line.startswith('| '):
            block.append(line[2:])
            continue
        if len(block):
            processed_lines += ['{'] + preprocess(block) + ['}']
            block = []
        processed_lines.append(line.strip())
    
    return processed_lines

if __name__ == '__main__':    
    ctx = Context()
    proof.add_parse_action(ProofActionWithContext(ctx))

    parser = ArgumentParser()
    parser.add_argument('input_file', type=str)
    args = parser.parse_args()
    try:
        text = '\n'.join(preprocess(open(args.input_file).readlines()))
        proof.parse_string(text, parse_all=True)
        print('Parsed successfully!')
        if ctx.check():
            assert ctx.main_proof is not None
            hyp, deds = ctx.proof_types[ctx.main_proof]
            for ded in deds:
                print(f'{{ {", ".join(map(str, hyp))} |- {ded}')
        
    except ParseException as e:
        print(e.explain())