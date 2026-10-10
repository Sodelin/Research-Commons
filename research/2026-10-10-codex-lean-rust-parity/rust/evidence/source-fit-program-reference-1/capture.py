"""Exact saved-equation/readout reference; no target or legacy engine import."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path('/workspace/Research-Commons')
BASE = ROOT / 'research/2026-10-10-codex-lean-rust-parity/rust'
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    with path.open('x') as handle:
        handle.write(json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n')


def main():
    prior = BASE / 'evidence/source-fit-bank-bridge-1'
    prior_freeze = json.loads((prior / 'SOURCE-FREEZE.json').read_bytes())
    parser = prior / 'capture.py'
    parser_pin = next(row['sha256'] for row in prior_freeze['sources'] if row['path'] == str(parser))
    assert sha(parser) == parser_pin
    # This is the already-captured stdlib AST whitelist, not law_compiler.py,
    # solver.py, any target runtime or a reconstructed genealogy generator.
    reference = runpy.run_path(str(parser), run_name='saved_fraction_reference_only')
    sparse, mapped_tree, rational = [reference[name] for name in ('sparse', 'mapped_tree', 'rational')]
    outputs, input_pins = [], []
    for name in ('hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted'):
        origin_name = 'hybrid-common-sat' if name.endswith('-permuted') else name
        origin_path = prior / (origin_name + '.origin.json')
        request_path = BASE / 'fixtures/source-fit' / (name + '.request.json')
        origin, request = json.loads(origin_path.read_bytes()), json.loads(request_path.read_bytes())
        source_result = Path(origin['path'])
        assert sha(source_result) == origin['sha256']
        input_pins += [{'path': str(p), 'sha256': sha(p)} for p in (origin_path, request_path, source_result)]
        old = origin['request']
        variables = request['variables']
        assignment = [Fraction(row['value']) for row in request['values']]
        dimension = len(variables)
        edge_count = len(request['context']['edges'])
        labels = dict(zip(request['copy_labels'], request['context']['global_labels']))
        old_law = old['rows'][0]['law']
        rows = []
        for i, outcome in enumerate(old_law):
            terms = sparse(origin['entry']['equations'][i], variables)
            zero = (0,) * dimension
            terms[zero] = terms.get(zero, Fraction(0)) + Fraction(outcome['p'])
            edge_terms = {}
            for powers, coefficient in terms.items():
                for j in range(edge_count, dimension):
                    coefficient *= assignment[j] ** powers[j]
                key = powers[:edge_count]
                edge_terms[key] = edge_terms.get(key, Fraction(0)) + coefficient
            edge_terms = {p: c for p, c in edge_terms.items() if c}
            probability = reference['evaluate'](edge_terms, assignment[:edge_count])
            assert probability == Fraction(outcome['p'])
            rows.append({'tree': mapped_tree(outcome['outcome'], labels)[0],
                         'probability': rational(probability),
                         'edge_polynomial': [[list(p), rational(c)] for p, c in sorted(edge_terms.items())]})
        result = {'schema': 'saved_source_fit_expected_all_rooted_coefficients_v1',
                  'fixture': name, 'observer': 'ROOTED_UNRANKED_COMPLETE',
                  'source_origin_sha256': sha(origin_path), 'input_sha256': sha(request_path),
                  'rows': sorted(rows, key=lambda r: r['tree']),
                  'target_executed': False, 'source_observation_fit_claim': False}
        output = HERE / (name + '.expected.json')
        write(output, result)
        outputs.append(output)
    common_path = prior / 'hybrid-common-sat.origin.json'
    common = json.loads(common_path.read_bytes())
    old_rows = common['request']['rows']
    labels = {'a': 0, 'b': 1, 'c': 2}
    configurations = []
    for label, index, weight in [('parent0-quarter', 1, Fraction(1, 4)),
                                 ('parent1-threequarters', 2, Fraction(3, 4))]:
        configurations.append({'label': label, 'weight': rational(weight),
            'forcing': [index == 2], 'outcomes': sorted([
                {'tree': mapped_tree(row['outcome'], labels)[0],
                 'probability': rational(weight * Fraction(row['p']))}
                for row in old_rows[index]['law']], key=lambda r: r['tree'])})
    mixture = sorted([{'tree': mapped_tree(row['outcome'], labels)[0],
                       'probability': rational(row['p'])} for row in old_rows[3]['law']], key=lambda r: r['tree'])
    sums = {}
    for config in configurations:
        assert sum((Fraction(row['probability']) for row in config['outcomes']), Fraction(0)) == Fraction(config['weight'])
        for row in config['outcomes']:
            sums[row['tree']] = sums.get(row['tree'], Fraction(0)) + Fraction(row['probability'])
    assert all(sums[row['tree']] == Fraction(row['probability']) for row in mixture)
    program = HERE / 'hybrid-common-program.expected.json'
    write(program, {'schema': 'saved_source_fit_expected_labelled_program_v1',
        'observer': 'ROOTED_UNRANKED_COMPLETE', 'configurations': configurations,
        'label_forgetting_mixture': mixture, 'source_origin_sha256': sha(common_path),
        'target_executed': False, 'controlled_full_code_claim': False,
        'note': 'Fresh displayed labels retain alpha-weighted rooted laws; inherited observed program row forgot labels.'})
    outputs.append(program)
    test = BASE / 'tests/source_fit_program.rs'
    freeze = HERE / 'SOURCE-FREEZE.json'
    write(freeze, {'schema': 'source_fit_program_reference_freeze_v1',
        'sources': [{'path': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
                    for p in (Path(__file__), parser, test, BASE / 'src/source_fit_bank.rs', BASE / 'src/source_fit_readout.rs')],
        'input_pins': input_pins, 'compiler_processes': 0, 'native_processes': 0,
        'legacy_solver_or_compiler_processes': 0})
    outputs.append(freeze)
    receipt = HERE / 'RECEIPT.json'
    write(receipt, {'schema': 'source_fit_program_saved_reference_v1',
        'status': 'PASS_REFERENCE_ONLY', 'all_coefficient_reference_cases': 3,
        'all_coefficient_reference_rows': 9, 'labelled_configurations': 2,
        'mixture_rows': 3, 'authored_unexecuted_integration_tests': 1,
        'target_processes': 0, 'compiler_processes': 0,
        'scientific_admission_claim': False, 'controlled_full_code_claim': False,
        'outputs': [{'path': str(p), 'sha256': sha(p), 'bytes': p.stat().st_size} for p in outputs]})
    print(json.dumps({'status': 'PASS_REFERENCE_ONLY', 'receipt': str(receipt),
        'receipt_sha256': sha(receipt), 'test_sha256': sha(test), 'target_processes': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
