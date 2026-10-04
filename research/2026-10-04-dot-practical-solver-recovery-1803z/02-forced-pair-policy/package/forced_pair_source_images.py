#!/usr/bin/env python3
"""Exact actual-source image computation for the complete n4/r1 forced-row menu.

The original two deterministic rows force the SAME named hybrid to0 or1.
The images retain a single graph/edge assignment. This is a finite execution
instance of the accepted source-design contract, not an unbounded theorem.
"""
from pathlib import Path
import hashlib
import json
import sys
import time
import sympy as sp
BASE = Path(__file__).resolve().parent/'sourcekit'
sys.path.insert(0, str(BASE))
from solver import census, compile_law, unrooted_law, displayed, admitted, identity, graph_json
from sympy.printing.mathematica import mathematica_code


def main():
    root = Path(__file__).resolve().parent
    start = time.monotonic()
    sources = list(census(4, 1))
    if len(sources) != 546:
        raise RuntimeError('Wrong complete original-source census.')
    coordinates = sorted(unrooted_law(compile_law(sources[0], forced={'H0': 0})), key=repr)
    rows = []
    representatives = {}
    for source in sources:
        if not admitted(source):
            raise RuntimeError('Nonadmitted actual source.')
        outputs = []
        for bit in (0, 1):
            target = displayed(source)[(bit,)]
            own = coordinates.index(target)
            law = unrooted_law(compile_law(source, 'independent', forced={'H0': bit}))
            other = next(i for i in range(3) if i != own)
            survival = sp.expand(3*law[coordinates[other]])
            variables = source.parameters()[0]
            terms = sp.Poly(survival, *variables).terms()
            if len(terms) != 1 or terms[0][1] != 1 or not any(terms[0][0]) or any(p not in (0, 1) for p in terms[0][0]):
                raise RuntimeError('Forced response is not a nonempty original-survival monomial.')
            if any(sp.expand(law[event]-(1-2*survival/3 if i == own else survival/3)) != 0 for i, event in enumerate(coordinates)):
                raise RuntimeError('Actual forced source law differs from the image model.')
            support = set(str(x) for x, power in zip(variables, terms[0][0]) if power)
            outputs.append({'bit': bit, 'target_coordinate': own,
                            'survival_monomial': str(survival), 'support': sorted(support),
                            'actual_law': [str(law[event]) for event in coordinates]})
        key = tuple(row['target_coordinate'] for row in outputs)
        first, second = (set(row['support']) for row in outputs)
        exclusive0, exclusive1, shared = first-second, second-first, first&second
        if exclusive0 and exclusive1 and key not in representatives:
            representatives[key] = {'graph': graph_json(source), 'forced_rows': outputs,
                                    'exclusive0': sorted(exclusive0), 'exclusive1': sorted(exclusive1),
                                    'shared': sorted(shared),
                                    'surjection': 'For any0<s,t<1 choose c=(1+max(s,t))/2 when shared is nonempty, else c=1. Shared edges have c^(1/shared_count); exclusive0/1 edges have(s/c)^(1/exclusive0_count),(t/c)^(1/exclusive1_count); unused edges and gamma are1/2. All assigned original parameters are strictly interior and the TWO actual monomials equal s and t on ONE graph.'}
        rows.append({'graph': graph_json(source), 'ordered_target_pair': key, 'forced_rows': outputs,
                     'same_original_parameter_assignment': True})
    expected = {(a, b) for a in range(3) for b in range(3)}
    if set(representatives) != expected:
        raise RuntimeError('Not every complete pair image has an actual source surjection witness.')
    document = {'schema': 'complete-n4-r1-original-force-pair-image-equivalence-v1',
                'source_count': len(sources), 'original_hybrid_ids': ['H0'],
                'original_forcing_rows': [{'H0': 0}, {'H0': 1}],
                'upstream': identity(), 'coordinate_order': coordinates,
                'all_actual_source_rows': rows,
                'surjection_representatives': [representatives[key] for key in sorted(representatives)],
                'source_image_model_count': 9,
                'scope': 'All546 original admitted outer-labelled cut-child binary n4/r1 sources, one-copy unrooted gene quartet; free positive edge-specific clocks, menu ONLY the two full original forcing rows.',
                'general_CAD_policy_or_unknown_size_closure_claimed': False,
                'elapsed_seconds': time.monotonic()-start}
    path = root/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json'
    path.write_text(json.dumps(document, indent=2)+'\n')
    s, t = sp.symbols('survivalA survivalB')
    models = []
    targets = {}
    for a, b in sorted(expected):
        label = targets.setdefault(tuple(sorted({a, b})), len(targets))
        laws = [[1-2*s/3 if i == a else s/3 for i in range(3)],
                [1-2*t/3 if i == b else t/3 for i in range(3)]]
        text = '{'+','.join('{'+','.join(mathematica_code(value) for value in row)+'}' for row in laws)+'}'
        models.append('<|"Vars"->{survivalA,survivalB},"Domain"->0<survivalA<1 && 0<survivalB<1,"Laws"->'+text+',"Target"->'+str(label)+'|>')
    (root/'forced_pair_models.wl').write_text('models={'+',\n'.join(models)+'};\nsupports={{1},{2},{1,2}};\nrowSites={{1},{1}};\n')
    print(json.dumps({'status': 'PASS_EXACT_COMPLETE_ACTUAL_FORCE_PAIR_IMAGES',
                      'source_count': len(sources), 'image_models': 9,
                      'certificate_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                      'elapsed_seconds': document['elapsed_seconds']}, indent=2))


if __name__ == '__main__':
    main()
