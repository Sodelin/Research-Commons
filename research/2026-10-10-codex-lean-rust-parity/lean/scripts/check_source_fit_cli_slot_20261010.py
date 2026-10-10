#!/usr/bin/env python3
"""Bounded serial stdin/file/check challenges for the newly built private CLI."""
import datetime
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

from check_core import save, sha

PACKET = Path(__file__).resolve().parents[2]
WORK = Path('/dev/shm/rc-source-fit-native-20261010T221453.635194Z')
BINARY = WORK / 'target/debug/source-fit-solver'
BINARY_SHA = '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'
GUARD = Path(__file__).with_name('guard_g7_survival_run_20261010_v2.py')
GUARD_SHA = '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4'


def main():
    assert sha(BINARY) == BINARY_SHA and sha(GUARD) == GUARD_SHA
    spec = importlib.util.spec_from_file_location('guard', GUARD)
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    build = json.loads((WORK / 'FINAL-RECEIPT.json').read_bytes())
    assert build['status'] == 'PASS_ALL_FOCUSED_NATIVE_COMMANDS'
    plan = json.loads((WORK / 'PLAN.json').read_bytes())
    out = WORK / 'cli-challenges'
    out.mkdir()
    inputs, results = [], []
    for name in ['hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted']:
        for suffix in ['request', 'expected']:
            original = PACKET / 'rust/fixtures/source-fit' / f'{name}.{suffix}.json'
            frozen = out / original.name
            frozen.write_bytes(original.read_bytes())
            inputs.append({'original': str(original), 'frozen': str(frozen), 'sha256': sha(frozen)})
    save(out / 'PRE-USE-PLAN.json', {'status': 'AUTHORIZED_CANONICAL_PRIVATE_CLI_CHALLENGES',
        'script_sha256': sha(Path(__file__)), 'binary': str(BINARY), 'binary_sha256': BINARY_SHA,
        'build_receipt_sha256': sha(WORK / 'FINAL-RECEIPT.json'), 'inputs': inputs,
        'cases': '3 exact saved COMMON/INDEP/permuted banks and rooted readouts: stdin/file equality, good checker acceptance, forged-claim checker rejection. Unknown-field, noncanonical-rational, full-view refusal controls.',
        'native_memory_or_scratch_limits_changed': False, 'compiler_invoked': False,
        'source_admission_or_universal_native_refinement_claim': False})

    def invoke(name, args, payload=None, expected_code=0, expected_status=None):
        assert sha(BINARY) == BINARY_SHA
        assert all(sha(Path(p)) == v['sha256'] for p, v in plan['source_pins'].items())
        assert guard.memory()['nonreclaimable_estimate'] < plan['shared_nonreclaimable_memory_abort_bytes']
        directory = out / name
        directory.mkdir()
        command = [str(BINARY), *map(str, args)]
        started = time.monotonic()
        with (directory / 'stdout').open('wb') as stdout, (directory / 'stderr').open('wb') as stderr:
            child = subprocess.Popen(command, stdin=subprocess.PIPE if payload is not None else subprocess.DEVNULL,
                stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                if payload is not None:
                    child.stdin.write(payload)
                    child.stdin.close()
                while child.poll() is None:
                    assert time.monotonic() - started < 30
                    assert guard.memory()['nonreclaimable_estimate'] < plan['shared_nonreclaimable_memory_abort_bytes']
                    assert guard.allocated([Path(p) for p in plan['allocation_roots']]) < plan['native_abort_with_transient_headroom_bytes']
                    time.sleep(0.02)
            finally:
                if child.poll() is None:
                    guard.terminate_group(child)
                rc = child.wait()
        raw = (directory / 'stdout').read_bytes()
        data = json.loads(raw)
        result = {'name': name, 'command': command, 'exit_code': rc, 'elapsed_seconds': time.monotonic() - started,
            'stdout_sha256': sha(directory / 'stdout'), 'stderr_sha256': sha(directory / 'stderr'),
            'expected_exit_code': expected_code, 'expected_status': expected_status,
            'actual_status': data.get('status'), 'input_sha256': __import__('hashlib').sha256(payload).hexdigest() if payload is not None else None}
        result['status'] = 'PASS' if rc == expected_code and (expected_status is None or data.get('status') == expected_status) else 'PRESERVED_FAILURE'
        save(directory / 'RECEIPT.json', result)
        results.append(result)
        assert result['status'] == 'PASS', result
        return raw, data

    false_flags = ['source_admission_verified', 'source_observation_fit_verified', 'source_provenance_verified',
        'timed_readout_verified', 'full_code_evaluated', 'universal_native_refinement_verified', 'certificate_valid', 'full_solver_verified']
    for name in ['hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted']:
        request = out / f'{name}.request.json'
        expected = json.loads((out / f'{name}.expected.json').read_bytes())
        for mode, checker, status in [('bank', 'check', 'SYMBOLIC_BANK'), ('readout', 'check-readout', 'TABLE')]:
            raw, data = invoke(f'{name}-{mode}-file', [mode, request], expected_status=status)
            stdin_raw, _ = invoke(f'{name}-{mode}-stdin', [mode, '-'], request.read_bytes(), expected_status=status)
            assert raw == stdin_raw
            response = out / f'{name}.{mode}.response.json'
            response.write_bytes(raw)
            invoke(f'{name}-{mode}-check-good', [checker, request, response], expected_status='ACCEPT')
            forged = dict(data)
            forged['source_admission_verified'] = True
            forged_path = out / f'{name}.{mode}.forged.json'
            forged_path.write_text(json.dumps(forged) + '\n')
            invoke(f'{name}-{mode}-check-forged', [checker, request, forged_path], expected_code=1, expected_status='REJECT')
            assert data['source_admission_verified'] is False
            if mode == 'readout':
                assert all(data[flag] is False for flag in false_flags)
                rows = [{'tree': r['tree'], 'probability': r['probability']} for r in data['mixture']]
                assert rows == expected['expected_global_rows']
                assert data['configurations'][0]['outcomes'] == data['mixture']
    common = json.loads((out / 'hybrid-common-sat.request.json').read_bytes())
    changed = dict(common, unexpected_field=True)
    invoke('unknown-field-rejected', ['bank', '-'], json.dumps(changed).encode(), expected_code=1)
    invalid = json.loads(json.dumps(common))
    invalid['values'][0] = '2/4'
    invoke('noncanonical-rational-rejected', ['bank', '-'], json.dumps(invalid).encode(), expected_code=1)
    full = dict(common, terminal='FULL_VIEW')
    invoke('full-view-readout-refused', ['readout', '-'], json.dumps(full).encode(), expected_code=2, expected_status='UNSUPPORTED')
    stable = all(sha(Path(r['original'])) == r['sha256'] for r in inputs) and sha(BINARY) == BINARY_SHA
    assert stable and all(sha(Path(p)) == v['sha256'] for p, v in plan['source_pins'].items())
    receipt = {'status': 'PASS_PRIVATE_CLI_STDIN_FILE_AND_CHECK_CHALLENGES', 'binary_sha256': BINARY_SHA,
        'cases': results, 'command_count': len(results), 'saved_original_rooted_laws_compared': 3,
        'original_and_frozen_inputs_stable': stable, 'source_pins_stable': True,
        'native_allocation_bytes': guard.allocated([Path(p) for p in plan['allocation_roots']]),
        'final_memory': guard.memory(), 'source_admission_or_universal_refinement_claim': False,
        'scope': 'Supplied exact bank/trace and completed rooted readout at rational assignments; no source provenance, full-Code, timed readout or full solver claim.'}
    save(out / 'RECEIPT.json', receipt)
    print(json.dumps({k: receipt[k] for k in ['status', 'command_count', 'saved_original_rooted_laws_compared', 'native_allocation_bytes']}))


if __name__ == '__main__':
    main()
