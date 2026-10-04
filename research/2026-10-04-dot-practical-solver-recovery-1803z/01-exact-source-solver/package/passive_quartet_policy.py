#!/usr/bin/env python3
"""Execute the verified one-call passive policy on the positive four-taxon TREE class.

This consumes declared exact concordance factors; it does not turn finite
sequence frequencies into exact law or identify an arbitrary network.
"""
from pathlib import Path
import argparse
import json
import sympy as sp
from solver import (
    prepare_request, InvalidInput, Unsupported, census, compile_law,
    unrooted_law, target_json, verify_witness, digest, graph_json, physical_realization,
)


def execute(request):
    n, ids, modes, taxa, rows = prepare_request(request)
    if n != 4 or ids or len(rows) != 1 or rows[0]['kind'] != 'unrooted_splits':
        raise Unsupported('This executable policy is specifically one passive unrooted quartet readout on the complete zero-hybrid tree class.')
    row = rows[0]
    if set(row['samples']) != {f'L{i}' for i in range(4)} or any(len(v) != 1 for v in row['samples'].values()):
        raise Unsupported('One original sampled copy per original taxon is required.')
    observed = row['observed']
    if len(observed) != 3 or any(len(event) != 1 for event in observed):
        raise InvalidInput('A resolved quartet law has three nontrivial split outcomes.')
    winning = max(observed, key=observed.get)
    other = [p for event, p in observed.items() if event != winning]
    if other[0] != other[1] or not 0 < other[0] < sp.Rational(1, 3) or observed[winning] <= other[0]:
        raise InvalidInput('The response is outside the exact positive-tree law image. Use the generic source solver for a delivered catalogue-NO certificate.')
    survival = 3*other[0]
    copy_to_leaf = {copies[0]: leaf for leaf, copies in row['samples'].items()}
    target = tuple(sorted(tuple(sorted(copy_to_leaf[x] for x in side)) for side in winning[0]))
    for source in census(4, 0):
        if target_json(source)['nontrivial_displayed_split_union'] != [target]:
            continue
        law = unrooted_law(compile_law(source))
        unrelated = next(p for event, p in law.items() if event != (target,))
        monomial = sp.Poly(sp.expand(3*unrelated), *source.parameters()[0]).terms()
        if len(monomial) != 1 or monomial[0][1] != 1:
            raise InvalidInput('Unexpected source image.')
        powers = monomial[0][0]
        degree = sum(powers)
        values = {}
        for symbol, power in zip(source.parameters()[0], powers):
            if not power:
                value = {'kind': 'rational', 'value': '1/2'}
            elif degree == 1:
                value = {'kind': 'rational', 'value': str(survival)}
            else:
                value = {'kind': 'algebraic',
                         'polynomial_ascending': [str(-survival)] + ['0']*(degree-1) + ['1'],
                         'real_root_index': 2 if degree % 2 == 0 else 1}
            values[str(symbol)] = value
        # Independent recomputation binds the chosen target to actual source laws.
        verify_witness(source, modes[0], rows, values)
        return {'status': 'IDENTIFIED_ACTUAL_TREE_SPLIT_ONE_PASSIVE_EXACT_CALL',
                'request_sha256': digest(request), 'original_taxa': taxa,
                'engine_taxon_mapping': {f'L{i}': t for i, t in enumerate(taxa)},
                'identified_engine_split': target,
                'identified_original_taxon_split': [[taxa[int(leaf[1:])] for leaf in side] for side in target],
                'source_witness': graph_json(source), 'values': values,
                'physical_realization': physical_realization(source, values),
                'verification': 'RECOMPUTED_EXACT_SOURCE_WITNESS_PLUS_COMPLETE15_SOURCE_IMAGE_POLICY_CERTIFICATE',
                'trajectory_cost': {'exact_calls': 1, 'configurations': 1, 'controlled_sites': 0},
                'budget0_lower_bound': 'At least two admitted positive original tree targets exist with the empty response history.',
                'scope': 'complete four-taxon zero-hybrid positive-tree class, free original edge-specific clocks, declared exact unrooted law',
                'empirical_or_unknown_size_graph_recovery_claimed': False,
                'Lean_verification_claimed': False}
    raise InvalidInput('No admitted original tree has the selected target.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        result = execute(json.loads(Path(args.request).read_bytes()))
    except (Unsupported, InvalidInput, KeyError, TypeError, ValueError) as error:
        print(json.dumps({'status': 'POLICY_INPUT_NOT_ADMITTED', 'reason': str(error)}))
        return 2
    Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'target': result['identified_original_taxon_split'],
                      'trajectory_cost': result['trajectory_cost']}))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
