#!/usr/bin/env python3
"""Exactly three fresh completed-calendar application controls; no new kernel."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
RUST = HERE.parents[1]
ROOT = RUST.parents[2]
sys.path.insert(0, str(RUST))
import native_calendar_component as component

NATIVE = Path('/workspace/scratch/lean-rust-parity-native/runtime/calendar-cli-artifact-1/calendar-solver')
NATIVE_SHA = '580bab497f2f2963ec938891e69d1cbdcf443b1c2dea694e548817b14fbebd05'
INPUTS = RUST.parent / 'design/evidence/calendar-original-input-freeze-1'
INVENTORY_SHA = '4d39a2d825686e135dc727dd9a705320af0c5b54c4c65d7251c28f42ddb5c2ba'
EXPECTED_ROWS = {'twoTipCalendar': 2, 'serialNegativeTips': 12, 'parallelCommonCalendar': 24}
GUARDS = [
    ('applications/practical-solver/run.py', '8c00f261d180452daa094b87f50a788b862efe7c0c5b0e2e133e44bb269352a7'),
    ('research/2026-10-10-codex-lean-rust-parity/rust/native_calendar_component.py', '9de9c1bf056a7b0d40900b33ebd3d29f12b2efacab61e90f9ab5b633a86f0db6'),
    ('research/2026-10-10-codex-lean-rust-parity/design/calendar_check.py', '6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb'),
    ('research/2026-10-10-codex-lean-rust-parity/rust/CALENDAR-COMPONENT-PINS.json', '23751b40d609fce76ae82c0d921e81e74669a0dd0fe9b7da72f436ce92a99800'),
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    path.open('x').write(json.dumps(value, indent=2, sort_keys=True) + '\n')


def guard():
    for name, digest in GUARDS:
        assert sha((ROOT / name).read_bytes()) == digest, name
    assert sha(NATIVE.read_bytes()) == NATIVE_SHA
    assert sha((INPUTS / 'INVENTORY.json').read_bytes()) == INVENTORY_SHA


def main():
    guard()
    inventory_raw = (INPUTS / 'INVENTORY.json').read_bytes()
    inventory = json.loads(inventory_raw)
    assert inventory['expected_outputs_included'] is False
    assert {entry['fixture'] for entry in inventory['inputs']} == set(EXPECTED_ROWS)
    (HERE / 'INPUT-INVENTORY.json').open('xb').write(inventory_raw)
    origins = HERE / 'inputs'; origins.mkdir()
    logs = HERE / 'launcher-logs'; logs.mkdir()
    cases = HERE / 'cases'; cases.mkdir()
    audits = HERE / 'independent-audits'; audits.mkdir()
    staged, helper, reference_pins = component.capture_sources()
    (HERE / 'CAPTURED-REFERENCE.py').open('xb').write(staged)
    write(HERE / 'REFERENCE-SOURCES.json', reference_pins)
    receipt = {'schema': 'completed_calendar_application_review_v1', 'status': 'INCOMPLETE', 'cases': [],
        'input_inventory_sha256': INVENTORY_SHA, 'guards': [{'path': path, 'sha256': digest} for path, digest in GUARDS],
        'binary': str(NATIVE), 'binary_sha256': NATIVE_SHA, 'harness_sha256': sha(Path(__file__).read_bytes()),
        'reference_sources': reference_pins, 'captured_reference_sha256': sha(staged),
        'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        'Lean_execution': False, 'native_completion_execution': True, 'broader_suites_rerun': False,
        'original_calendar_phase_PMF_correspondence_checked': False, 'source_admission_verified': False,
        'certificate_valid': False, 'full_solver_verified': False,
        'scope': 'Exactly three supplied completed-calendar forward tables through the current application. '
                 'Full coefficients, views, witnesses, registers, agenda and physical substitutions independently '
                 'checked by the captured existing spectral/copy helper. Original-calendar phase PMF/code '
                 'correspondence and universal native refinement remain separate.'}
    try:
        for entry in inventory['inputs']:
            name = entry['fixture']; raw = (INPUTS / entry['path']).read_bytes()
            assert sha(raw) == entry['sha256'] and len(raw) == entry['bytes']
            assert raw == (ROOT / entry['original_path']).read_bytes()
            request = helper.parse_request(raw)
            assert request['terminal'] == 'ANCESTRAL_COMPLETE'
            saved = origins / entry['path']; saved.open('xb').write(raw)
            output = cases / name
            command = [sys.executable, '-B', str(ROOT / 'applications/practical-solver/run.py'),
                'calendar-law', '--request', str(saved), '--native-binary', str(NATIVE),
                '--expected-binary-sha256', NATIVE_SHA, '--output', str(output)]
            before = time.monotonic()
            env = {'PATH': os.defpath, 'LANG': 'C.UTF-8', 'PYTHONDONTWRITEBYTECODE': '1',
                   'PYTHONNOUSERSITE': '1', 'PYTHONHASHSEED': '0'}
            execution = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, timeout=65)
            (logs / (name + '.stdout')).open('xb').write(execution.stdout)
            (logs / (name + '.stderr')).open('xb').write(execution.stderr)
            launched = {'command': command, 'process_started': True, 'exit_code': execution.returncode,
                'timed_out': False, 'wall_seconds': time.monotonic() - before,
                'stdout_sha256': sha(execution.stdout), 'stderr_sha256': sha(execution.stderr)}
            write(logs / (name + '.execution.json'), launched)
            assert execution.returncode == 0, (name, execution.stderr)
            parent = json.loads((output / 'RESULT.json').read_bytes())
            child = json.loads((output / 'component/RESULT.json').read_bytes())
            assert parent['status'] == child['status'] == 'SUPPLIED_CALENDAR_TABLE'
            assert parent['request_bytes_sha256'] == child['request_sha256'] == sha(raw)
            assert (output / 'REQUEST.json').read_bytes() == raw
            assert (output / 'component/REQUEST.json').read_bytes() == raw
            assert parent['launcher_sha256'] == GUARDS[0][1]
            assert all(child[key] is False for key in component.FALSE_CLAIMS)
            assert all(child[key] is True for key in component.TABLE_FLAGS)
            assert all(child[key] is True for key in ('solver_called', 'checker_called', 'reference_checker_called'))
            assert child['binary_pin_verification'] == 'EXPECTED_PIN_MATCHED'
            for key in ('solver_execution', 'checker_execution', 'reference_checker_execution'):
                assert child[key]['process_started'] and child[key]['exit_code'] == 0 and not child[key]['timed_out']
            table_raw = (output / 'component/TABLE.json').read_bytes()
            # Fresh auditor computation reuses the reviewed independent helper,
            # not an expected output file or any native recurrence.
            checked = helper.verify_certificate(raw, table_raw, 0)
            assert checked['status'] == 'TABLE' and checked['result_valid'] is True
            assert all(checked[key] is True for key in component.TABLE_FLAGS)
            assert checked['full_view_rows'] == EXPECTED_ROWS[name]
            table = helper.strict_json(table_raw, helper.MAX_CERTIFICATE_BYTES, canonical=True)
            assert table['request']['terminal'] == 'ANCESTRAL_COMPLETE'
            for row in table['word_result']['rows']:
                assert all(location == ['A', request['context']['root']] for location in row['view']['location'])
                assert len(row['witness']['live']) == 1
            write(audits / (name + '.json'), checked)
            record = {'fixture': name, 'status': 'PASS', 'request_sha256': sha(raw),
                'origin_request': str((INPUTS / entry['path']).relative_to(ROOT)), 'outer_execution': launched,
                'application_result_sha256': sha((output / 'RESULT.json').read_bytes()),
                'component_result_sha256': sha((output / 'component/RESULT.json').read_bytes()),
                'table_sha256': sha(table_raw), 'full_view_rows': checked['full_view_rows'], 'terms': checked['terms'],
                'terminal': 'ANCESTRAL_COMPLETE', 'native_solver_called': True, 'native_replay_called': True,
                'independent_reference_called': True, 'fresh_auditor_helper_checked': True,
                'full_original_register_retained': True, 'original_ancestral_location_checked': True,
                'native_executions': {key: child[key] for key in
                    ('solver_execution', 'checker_execution', 'reference_checker_execution')}}
            receipt['cases'].append(record)
        guard()
        for name, digest in component.PINS:
            assert sha((RUST.parent / 'design' / (name + '.py')).read_bytes()) == digest
        assert len(receipt['cases']) == 3
        receipt.update(status='PASS', cases_passed=3, full_view_rows=sum(c['full_view_rows'] for c in receipt['cases']),
            all_input_and_source_identities_stable=True)
    except BaseException as error:
        receipt.update(status='FAIL', error_type=type(error).__name__, error=str(error))
        raise
    finally:
        receipt['ended_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        write(HERE / 'RECEIPT.json', receipt)
    print(json.dumps({'status': receipt['status'], 'cases': 3, 'full_view_rows': receipt['full_view_rows'],
                      'receipt_sha256': sha((HERE / 'RECEIPT.json').read_bytes())}))


if __name__ == '__main__':
    main()
