"""Review saved native CLI outputs only; no solver/checker/compiler execution."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

BASE = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust')
NATIVE = BASE / 'evidence/source-fit-native-slot-20261010T221453.635194Z'
REFERENCE = BASE / 'evidence/source-fit-program-reference-1'
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin(path):
    return {'path': str(path), 'sha256': sha(path), 'bytes': path.stat().st_size}


def main():
    final = json.loads((NATIVE / 'FINAL-RECEIPT.json').read_bytes())
    batch = json.loads((NATIVE / 'cli-challenges/RECEIPT.json').read_bytes())
    assert final['status'] == 'PASS_ALL_FOCUSED_NATIVE_COMMANDS'
    assert final['private_binary']['sha256'] == batch['binary_sha256'] == '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'
    assert sha(Path(final['private_binary']['path'])) == batch['binary_sha256']
    controls, pins, term_count = [], [pin(NATIVE / 'FINAL-RECEIPT.json'), pin(NATIVE / 'cli-challenges/RECEIPT.json')], 0
    by_name = {case['name']: case for case in batch['cases']}
    for name in ['hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted']:
        request_path = BASE / 'fixtures/source-fit' / (name + '.request.json')
        expected_path = REFERENCE / (name + '.expected.json')
        expected = json.loads(expected_path.read_bytes())
        assert expected['input_sha256'] == sha(request_path)
        case = by_name[name + '-readout-file']
        assert case['exit_code'] == 0 and case['status'] == 'PASS'
        actual_request = Path(case['command'][2])
        assert actual_request.read_bytes() == request_path.read_bytes()
        file_output = NATIVE / 'cli-challenges' / (name + '-readout-file') / 'stdout'
        stdin_output = NATIVE / 'cli-challenges' / (name + '-readout-stdin') / 'stdout'
        assert sha(file_output) == case['stdout_sha256']
        assert file_output.read_bytes() == stdin_output.read_bytes()
        assert by_name[name + '-readout-stdin']['input_sha256'] == sha(request_path)
        data = json.loads(file_output.read_bytes())
        assert data['schema'] == 'source_fit_rooted_result_v1' and data['status'] == 'TABLE'
        assert data['observer'] == 'ROOTED_UNRANKED_COMPLETE'
        for field in ['source_admission_verified', 'source_observation_fit_verified', 'source_provenance_verified',
                      'timed_readout_verified', 'full_code_evaluated', 'universal_native_refinement_verified',
                      'certificate_valid', 'full_solver_verified']:
            assert data[field] is False
        assert data['mixture'] == expected['rows']
        assert len(data['configurations']) == 1
        assert data['configurations'][0]['label'] == 'natural'
        assert data['configurations'][0]['weight'] == '1/1'
        assert data['configurations'][0]['outcomes'] == data['mixture']
        request = json.loads(request_path.read_bytes())
        values = [Fraction(value['value']) for value in request['values']]
        mass = Fraction(0)
        for row in data['mixture']:
            evaluated = Fraction(0)
            for powers, coefficient in row['edge_polynomial']:
                assert len(powers) == len(request['context']['edges'])
                value = Fraction(coefficient)
                for atom, power in zip(values, powers):
                    assert type(power) is int and power >= 0
                    value *= atom ** power
                evaluated += value
                term_count += 1
            assert evaluated == Fraction(row['probability'])
            mass += evaluated
        assert mass == 1
        controls.append({'fixture': name, 'pass': True, 'all_rooted_coefficients_equal_saved_old_trace': True,
            'rows': len(data['mixture']), 'file_stdin_bytes_identical': True, 'input_sha256': sha(request_path),
            'response_sha256': sha(file_output)})
        pins += [pin(p) for p in (request_path, expected_path, actual_request, file_output, stdin_output,
            NATIVE / 'cli-challenges' / (name + '-readout-file') / 'RECEIPT.json')]
    current = [(BASE / 'src/source_fit_bank.rs', 'e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a'),
        (BASE / 'src/source_fit_readout.rs', '7a3a75b60af55f1138e82aa66c5a2e94b5dc9c8a597eadb0ff25230f03dae7c5')]
    assert all(sha(p) == digest for p, digest in current)
    pins += [pin(p) for p, _ in current]
    result = {'schema': 'source_fit_saved_native_coefficient_review_v1', 'status': 'PASS_SAVED_OUTPUT_REVIEW',
        'controls': controls, 'complete_rooted_rows_checked': 9, 'nonzero_edge_terms_checked': term_count,
        'source_pins': pins, 'review_source': pin(Path(__file__)), 'target_processes_started_by_reviewer': 0,
        'compiler_processes_started_by_reviewer': 0, 'baseline_compiler_processes_started_by_reviewer': 0,
        'source_admission_claim': False, 'general_refinement_claim': False,
        'scope': 'All saved natural ROOTED_UNRANKED_COMPLETE E-polynomial coefficients and exact probabilities at the three frozen supplied rational assignments; input/output/compiler receipts authenticated, no producer rerun.'}
    receipt = HERE / 'RECEIPT.json'
    with receipt.open('x') as handle:
        handle.write(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'rows': 9, 'terms': term_count,
        'receipt': str(receipt), 'receipt_sha256': sha(receipt), 'target_processes': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
