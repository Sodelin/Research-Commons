#!/usr/bin/env python3
"""Exercise actual application native-cell delegation and saved provenance."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.work.mkdir(parents=True, exist_ok=False)
    args.output.mkdir(parents=True, exist_ok=False)
    launcher = ROOT / 'applications/practical-solver/run.py'
    identities = {'launcher': sha(launcher), 'binary': sha(args.binary)}
    (args.output / 'REVIEWER.py').write_bytes(Path(__file__).read_bytes())
    examples = ROOT / 'applications/practical-solver/examples'
    cases = [
        ('affine-sat-regression', 'affine-cell', PACKET / 'design/fixtures/two_tip_natural_cell.req', 'MATRIX_WITNESS', 0, None),
        ('chart-sat-example', 'natural-cell', examples / 'natural-cell.rc1', 'MATRIX_WITNESS', 0, identities['binary']),
        ('chart-unsat', 'natural-cell', PACKET / 'quality/evidence/chart-bank-review-1/ordinary-calendar-contradiction/REQUEST.rc1', 'MATRIX_EXCLUSION', 0, None),
    ]
    ordinary = (PACKET / 'quality/evidence/chart-bank-review-1/ordinary-bare/REQUEST.rc1').read_bytes()
    unknown = args.work / 'unknown.rc1'
    unknown.write_bytes(ordinary.replace(b'0 0 4096\n', b'0 0 0\n', 1))
    invalid = args.work / 'invalid.rc1'
    invalid.write_bytes(ordinary.replace(b'EDGE 1 0 2\n', b'EDGE 1 0 1\n', 1))
    cases += [
        ('chart-budget', 'natural-cell', unknown, 'UNKNOWN', 2, None),
        ('chart-invalid-structure', 'natural-cell', invalid, 'REFUSED_REQUEST', 1, None),
        ('chart-bad-pin', 'natural-cell', examples / 'natural-cell.rc1', 'REFUSED_REQUEST', 1, '0' * 64),
        ('law-table-example', 'genealogy-law', examples / 'genealogy-law.rc1', 'FORMAL_GENEALOGY_TABLE', 0, identities['binary']),
        ('law-budget', 'genealogy-law', PACKET / 'design/law-fixtures/law_history_limit_zero.req', 'UNKNOWN', 2, None),
        ('law-invalid-structure', 'genealogy-law', PACKET / 'design/law-fixtures/law_bad_parent_alias.req', 'REFUSED_REQUEST', 1, None),
        ('law-bad-pin', 'genealogy-law', examples / 'genealogy-law.rc1', 'REFUSED_REQUEST', 1, '0' * 64),
    ]
    results, commands = [], {}
    for name, command, request, expected_status, expected_code, pin in cases:
        output = args.work / name
        argv = [sys.executable, '-B', str(launcher), command, '--request', str(request),
                '--native-binary', str(args.binary.resolve()), '--output', str(output)]
        if pin:
            argv += ['--expected-binary-sha256', pin]
        commands[name] = argv
        process = subprocess.run(argv, capture_output=True, timeout=180)
        (args.output / (name + '.stdout')).write_bytes(process.stdout)
        (args.output / (name + '.stderr')).write_bytes(process.stderr)
        data = json.loads((output / 'RESULT.json').read_bytes())
        (args.output / (name + '.RESULT.json')).write_bytes((output / 'RESULT.json').read_bytes())
        errors = []
        if process.returncode != expected_code or data['status'] != expected_status:
            errors.append('Wrong status or exit')
        if data['component'] != command or not data['component_called']:
            errors.append('Wrong delegation provenance')
        for flag in ('source_admission_verified', 'statistical_coverage_verified',
                     'parameter_accuracy_released', 'whole_application_lean_verified',
                     'physical_survival_image_verified',
                     'original_nine_parameter_producer_called'):
            if data[flag] is not False:
                errors.append('Unexpected promotion ' + flag)
        child = data['component_result']
        if expected_status in ('MATRIX_WITNESS', 'MATRIX_EXCLUSION'):
            if not (data['native_solver_called'] and data['native_checker_called'] and child['fraction_checker_called']):
                errors.append('Missing native/Fraction start evidence')
        if expected_status == 'FORMAL_GENEALOGY_TABLE':
            if not (data['native_solver_called'] and data['native_checker_called']
                    and child['reference_checker_called'] and data['formal_table_checked']
                    and child['inherited_baseline_all_coefficients_checked']):
                errors.append('Missing full table coefficient-check evidence')
            for flag in ('physical_survival_image_verified', 'observation_law_admission_verified',
                         'full_joint_calendar_law_verified', 'statistical_confidence_verified',
                         'complete_source_registry_verified', 'certificate_checked'):
                if child.get(flag) is not False:
                    errors.append('Unexpected LAW promotion ' + flag)
            if child.get('native_checker_algorithm_independent') is not False:
                errors.append('Native replay presented as independent algorithm')
        if name.endswith('bad-pin') and (data['native_solver_called'] or data['native_checker_called']):
            errors.append('Bad pin reached native process')
        if not all((output / name).is_file() for name in ('REPORT.md', 'REPORT.html', 'ARTIFACTS.json')):
            errors.append('Missing readable/artifact report')
        results.append({'case': name, 'status': data['status'], 'exit_code': process.returncode,
                        'native_solver_called': data['native_solver_called'],
                        'native_checker_called': data['native_checker_called'],
                        'fraction_checker_called': child['fraction_checker_called'],
                        'output': str(output), 'pass': not errors, 'errors': errors})
    saved = args.work / 'chart-sat-example/RESULT.json'
    before = sha(saved)
    repeat = subprocess.run(commands['chart-sat-example'], capture_output=True, timeout=30)
    overwrite_refused = repeat.returncode != 0 and sha(saved) == before
    stable = sha(launcher) == identities['launcher'] and sha(args.binary) == identities['binary']
    receipt = {'status': 'PASS' if stable and overwrite_refused and all(row['pass'] for row in results) else 'FAIL',
               'cases': results, 'fresh_output_overwrite_refused': overwrite_refused,
               'source_and_binary_stable': stable, 'identities': identities,
               'scope': 'Actual finite-cell and genealogy-law application delegation, refusal and process provenance. No new source admission or biological accuracy.'}
    (args.output / 'RECEIPT.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'cases_passed': sum(row['pass'] for row in results),
                      'cases_total': len(results), 'fresh_output_overwrite_refused': overwrite_refused}))
    return receipt['status'] != 'PASS'


if __name__ == '__main__':
    raise SystemExit(main())
