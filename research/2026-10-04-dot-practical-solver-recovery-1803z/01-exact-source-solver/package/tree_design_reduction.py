#!/usr/bin/env python3
"""Exact source-image reduction for the four-taxon positive-tree design case.

This is the accepted ordinary-tree concordance-factor identity, compiled and
checked for every original source. It is an execution optimization for this
instance, not a new general source-size or G7 theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp
from sympy.printing.mathematica import mathematica_code
from solver import ROOT, identity, digest, census, compile_law, unrooted_law, target_json, graph_json, InvalidInput


def reduce_design(directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    sources = list(census(4, 0))
    if len(sources) != 15:
        raise InvalidInput('Incomplete ordinary-tree source census.')
    coordinates = sorted(unrooted_law(compile_law(sources[0])), key=repr)
    receipts = []
    compact = {}
    z = sp.Symbol('survival', positive=True)
    for source in sources:
        actual = unrooted_law(compile_law(source))
        target = target_json(source)['nontrivial_displayed_split_union']
        if len(target) != 1:
            raise InvalidInput('An ordinary quartet tree must have one nontrivial displayed split.')
        own = coordinates.index((target[0],))
        other = next(i for i in range(3) if i != own)
        survival = sp.expand(3*actual[coordinates[other]])
        xs = source.parameters()[0]
        terms = sp.Poly(survival, *xs).terms()
        if len(terms) != 1 or terms[0][1] != 1:
            raise InvalidInput('Source survival is not the expected single unit monomial.')
        powers = terms[0][0]
        if not any(powers) or any(p not in (0, 1) for p in powers):
            raise InvalidInput('Expected a nonempty product of original positive-edge survivals.')
        law = [1-2*z/3 if i == own else z/3 for i in range(3)]
        if any(sp.expand(actual[event] - (1-2*survival/3 if i == own else survival/3)) != 0
               for i, event in enumerate(coordinates)):
            raise InvalidInput('Actual source law differs from the claimed image reduction.')
        degree = sum(powers)
        reconstruction = {x: z**sp.Rational(1, degree) if p else sp.Rational(1, 2)
                          for x, p in zip(xs, powers)}
        if sp.simplify(survival.subs(reconstruction) - z) != 0:
            raise InvalidInput('The positive source image reconstruction identity fails.')
        compact.setdefault(own, law)
        receipts.append({'graph': graph_json(source), 'actual_target': target,
                         'survival_monomial': str(survival),
                         'used_original_edge_variables': [str(x) for x, p in zip(xs, powers) if p],
                         'reconstruction': {str(x): str(v) for x, v in reconstruction.items()},
                         'compiled_identity': 'PASS_EXACT_SYMPY_POLYNOMIAL_IDENTITY',
                         'image_domain': '0<survival<1',
                         'surjectivity': 'Set each participating original x to the positive kth root of survival; every unused x is1/2.'})
    if set(compact) != {0, 1, 2}:
        raise InvalidInput('Missing actual quartet target image.')
    report = {'schema': 'actual-four-taxon-tree-source-image-reduction-v1',
              'upstream': identity(), 'source_count': len(sources),
              'coordinate_order': coordinates, 'receipts': receipts,
              'proof_scope': 'Exact symbolic identity for all15 actual trees plus elementary positive-monomial image equivalence. Original free edge-specific rates are essential.',
              'general_source_or_policy_closure_claimed': False,
              'Lean_verification_claimed': False}
    path = directory / 'SOURCE-IMAGE-REDUCTION-RECEIPT.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    models = []
    for own in range(3):
        law = '{' + ','.join(mathematica_code(p) for p in compact[own]) + '}'
        models.append('<|"Vars"->{survival},"Domain"->0<survival<1,"Laws"->{' + law + '},"Target"->' + str(own) + '|>')
    code = (ROOT / 'upstream/continuous_optimizer.wl').read_text()
    code += '\nmodels={' + ','.join(models) + '};\n'
    code += 'answer0=TimeConstrained[G7Decide[models,{{1}},0,{{}},0,0],15,"UNKNOWN_TIMEOUT"];\n'
    code += 'answer1=TimeConstrained[G7Decide[models,{{1}},1,{{}},1,0],15,"UNKNOWN_TIMEOUT"];\n'
    code += 'policyCorrect=Resolve[And@@Table[ForAll[s,0<s<1,1-2s/3>s/3],{3}],Reals];\n'
    code += '<|"ActualSourceCount"->15,"ExactSourceImageCount"->3,"ZeroCallBudget"->answer0,"OnePassiveCallBudget"->answer1,"LargestCFPolicyCorrect"->policyCorrect,"Scope"->"complete four-taxon positive original-tree class; exact unrooted law; free edge clocks"|>\n'
    output = directory / 'reduced-actual-source-design.wl'
    output.write_text(code)
    metadata = {'status': 'EXACT_SOURCE_IMAGE_REDUCTION_EXPORTED_BACKEND_PENDING',
                'source_count': 15, 'source_image_count': 3,
                'reduction_receipt_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'wolfram_code_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                'generic_policy_extraction_completed': False}
    (directory / 'REDUCTION-EXPORT.json').write_text(json.dumps(metadata, indent=2)+'\n')
    return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    print(json.dumps(reduce_design(args.output), indent=2))


if __name__ == '__main__':
    main()
