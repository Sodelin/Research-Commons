#!/usr/bin/env python3
"""Six authorized private source-fit application controls, strictly serial."""
import datetime
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
from check_core import save, sha

PACKET = Path(__file__).resolve().parents[2]
REPO = PACKET.parents[1]
APP = REPO / 'applications/practical-solver'
BINARY = Path('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver')
BINARY_SHA = '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    pins = {str(APP / 'run.py'): '82f4547efeb1ee118398a46fb5c0c29d1137b87b8643be40e615d9c4e642baf0',
        str(APP / 'README.md'): 'e8a40f40e805d07f4e42e40c4b710f746655e0a4dd2086a469d0b474143e27dd',
        str(PACKET / 'rust/native_source_fit_component.py'): '6f02d176aaa25a723796496a01ebdaafd5b4b842a4853f94befd419133a0f2ff',
        str(PACKET / 'rust/native_component.py'): 'cbad55d031621f8e6d29ddc58d6156188c6b9344705d4612642b2423ca6aea3c',
        str(Path(__file__).with_name('guard_g7_survival_run_20261010_v2.py')): '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4',
        str(BINARY): BINARY_SHA}
    assert all(sha(Path(p)) == h for p, h in pins.items())
    guard = load('guard', Path(__file__).with_name('guard_g7_survival_run_20261010_v2.py'))
    cleanup = load('pinned_launcher', APP / 'run.py').terminate_process_tree
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-source-fit-application-' + stamp)
    work.mkdir()
    roots = [*Path('/dev/shm').glob('rc-source-fit-native-*'), work]
    inputs = {}
    for name in ['hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted']:
        for suffix in ['request', 'expected']:
            original = PACKET / 'rust/fixtures/source-fit' / f'{name}.{suffix}.json'
            frozen = work / original.name
            shutil.copyfile(original, frozen)
            inputs[str(original)] = sha(original)
    budget = json.loads((work / 'hybrid-common-sat.request.json').read_bytes())
    budget['limits']['equations'] = 0
    save(work / 'equations-zero.request.json', budget)
    cases = [('common-bank', 'source-fit-bank', 'hybrid-common-sat', 0, 'SUPPLIED_FIT_BANK'),
        ('common-readout', 'source-fit-readout', 'hybrid-common-sat', 0, 'SUPPLIED_FIT_ROOTED_LAW'),
        ('independent-readout', 'source-fit-readout', 'hybrid-independent-sat', 0, 'SUPPLIED_FIT_ROOTED_LAW'),
        ('permuted-readout', 'source-fit-readout', 'hybrid-common-permuted', 0, 'SUPPLIED_FIT_ROOTED_LAW'),
        ('mismatched-pin', 'source-fit-bank', 'hybrid-common-sat', 1, 'REFUSED_REQUEST'),
        ('equations-zero', 'source-fit-bank', 'equations-zero', 2, 'UNKNOWN')]
    plan = {'status': 'PRE_USE_NATIVE_ONLY_APPLICATION_CONTROLS', 'script_sha256': sha(Path(__file__)),
        'workspace': str(work), 'pins': pins, 'inputs': inputs, 'cases': cases,
        'allocation_roots': list(map(str, roots)), 'native_limit_bytes': 2**30,
        'native_abort_bytes': 2**30 - 128 * 2**20, 'memory_abort_bytes': 15 * 2**30,
        'initial_memory': guard.memory(), 'reference_python_selected': False, 'compiler_invoked': False,
        'child_cleanup': 'Pinned launcher STOP_AND_WALK_LINUX_PROC handles nested child process sessions.'}
    save(work / 'PLAN.json', plan)
    shutil.copyfile(Path(__file__), work / 'RUNNER.py')
    print(json.dumps({'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json')}), flush=True)
    records = []
    flags = ['certificate_valid', 'source_admission_verified', 'source_observation_fit_verified',
        'source_provenance_verified', 'timed_readout_verified', 'full_code_evaluated',
        'universal_native_refinement_verified', 'full_solver_verified', 'source_witness_certified',
        'unrestricted_exclusion_certified', 'complete_source_registry_verified', 'observation_law_admission_verified',
        'statistical_confidence_verified', 'physical_survival_image_verified', 'full_joint_calendar_law_verified']
    for name, operation, fixture, expected_rc, expected_status in cases:
        assert all(sha(Path(p)) == h for p, h in pins.items())
        assert guard.memory()['nonreclaimable_estimate'] < plan['memory_abort_bytes']
        control = work / name
        control.mkdir()
        request = work / f'{fixture}.request.json'
        result_dir = control / 'application'
        digest = '0' * 64 if name == 'mismatched-pin' else BINARY_SHA
        command = [sys.executable, '-B', str(APP / 'run.py'), operation, '--request', str(request),
            '--output', str(result_dir), '--native-binary', str(BINARY), '--expected-binary-sha256', digest]
        error = None
        started = time.monotonic()
        peak_mem = peak_alloc = 0
        with (control / 'stdout').open('wb') as stdout, (control / 'stderr').open('wb') as stderr:
            child = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                while child.poll() is None:
                    m, a = guard.memory(), guard.allocated(roots)
                    peak_mem, peak_alloc = max(peak_mem, m['nonreclaimable_estimate']), max(peak_alloc, a)
                    assert m['nonreclaimable_estimate'] < plan['memory_abort_bytes']
                    assert a < plan['native_abort_bytes']
                    assert time.monotonic() - started < 60
                    time.sleep(0.05)
            except BaseException as exc:
                error = repr(exc)
            finally:
                if error is not None or child.poll() is None:
                    cleanup(child)
                rc = child.wait()
        rec = {'name': name, 'command': command, 'exit_code': rc, 'expected_exit_code': expected_rc,
            'expected_status': expected_status, 'monitor_error': error, 'stdout_sha256': sha(control / 'stdout'),
            'stderr_sha256': sha(control / 'stderr'), 'elapsed_seconds': time.monotonic() - started,
            'peak_nonreclaimable_bytes': max(peak_mem, guard.memory()['nonreclaimable_estimate']),
            'peak_native_allocated_bytes': max(peak_alloc, guard.allocated(roots))}
        try:
            assert error is None and rc == expected_rc
            result = json.loads((result_dir / 'RESULT.json').read_bytes())
            assert result['status'] == expected_status
            component = result['component_result']
            assert result['request_bytes_sha256'] == component['request_sha256'] == sha(request)
            assert all(result[f] is False and component[f] is False for f in flags)
            assert result['reference_checker_called'] is False and result['independent_all_coefficients_checked'] is False
            if name == 'mismatched-pin':
                assert component['binary_pin_verification'] == 'MISMATCH_REFUSED_BEFORE_LAUNCH'
                assert result['native_solver_called'] is False and result['native_checker_called'] is False
                assert not (result_dir / 'component/component/native/source-fit-solver').exists()
            else:
                assert result['native_solver_called'] and result['native_checker_called'] and result['native_replay_verified']
                assert component['semantic_request_echo_checked'] and component['source_identity_recheck_stable']
                assert component['staged_identity_recheck_stable']
                native = result_dir / 'component/NATIVE-RESULT.json'
                assert sha(native) == component['native_result_sha256']
                frame = json.loads(native.read_bytes())
                if name == 'equations-zero':
                    assert frame['status'] == 'UNKNOWN' and 'bank' not in frame
                    assert result['supplied_trace_checked'] is False and result['rooted_law_evaluated'] is False
                elif operation == 'source-fit-readout':
                    expected = json.loads((work / f'{fixture}.expected.json').read_bytes())
                    assert [{'tree': r['tree'], 'probability': r['probability']} for r in frame['mixture']] == expected['expected_global_rows']
            assert all(sha(Path(p)) == h for p, h in pins.items())
            assert guard.memory()['nonreclaimable_estimate'] < plan['memory_abort_bytes'] and guard.allocated(roots) < plan['native_abort_bytes']
            rec['status'] = 'PASS'
            rec['application_result_sha256'] = sha(result_dir / 'RESULT.json')
            rec['component_result_sha256'] = sha(result_dir / 'component/RESULT.json')
        except BaseException as exc:
            rec.update(status='PRESERVED_APPLICATION_FAILURE', verification_error=repr(exc))
        save(control / 'RECEIPT.json', rec)
        records.append(rec)
        print(json.dumps(rec), flush=True)
        if rec['status'] != 'PASS':
            break
    final = {'status': 'PASS_SIX_NATIVE_ONLY_SOURCE_FIT_APPLICATION_CONTROLS' if len(records) == len(cases) and all(r['status'] == 'PASS' for r in records) else 'PRESERVED_APPLICATION_FAILURE',
        'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json'), 'cases': records,
        'native_binary_sha256': BINARY_SHA, 'reference_python_selected': False,
        'inputs_stable': all(sha(Path(p)) == h for p, h in inputs.items()),
        'pins_stable': all(sha(Path(p)) == h for p, h in pins.items()),
        'compiler_invoked': False, 'source_or_old_native_paths_modified': False}
    save(work / 'FINAL-RECEIPT.json', final)
    print(json.dumps({'status': final['status'], 'workspace': str(work), 'final_receipt_sha256': sha(work / 'FINAL-RECEIPT.json')}))
    raise SystemExit(0 if final['status'].startswith('PASS_') else 1)

if __name__ == '__main__':
    main()
