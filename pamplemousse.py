from argparse import ArgumentParser
from proof_parser import proof, form, ProofActionWithContext
from proof import Context
from pyparsing import ParseException, delimited_list

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

def main():    
    ctx = Context()
    proof.add_parse_action(ProofActionWithContext(ctx))

    parser = ArgumentParser()
    parser.add_argument('input_file', type=str)
    args = parser.parse_args()
    try:
        lines = open(args.input_file).readlines()
        obligations = delimited_list(form, ',').parse_string(lines[0], parse_all=True)
        # obligation = form.parse_string(lines[0], parse_all=True)[0]
        text = '\n'.join(preprocess(lines[1:]))
        proof.parse_string(text, parse_all=True)
        if ctx.check():
            assert ctx.main_proof is not None
            hyp, deds = ctx.proof_types[ctx.main_proof]
            for obligation in obligations:
                if obligation in deds:
                    print(f'{hyp} |- {obligation}')
                else:
                    raise Exception(f'Proof obligation {obligation} not met!')
        
    except ParseException as e:
        print(e.explain())
        
        
if __name__ == '__main__':
    main()