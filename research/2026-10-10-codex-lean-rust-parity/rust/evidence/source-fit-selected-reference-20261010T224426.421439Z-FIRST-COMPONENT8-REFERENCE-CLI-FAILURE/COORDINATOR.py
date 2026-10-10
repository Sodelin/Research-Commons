#!/usr/bin/env python3
"""Prepare/run the authorized adapter8 then launcher4 reference controls.

Preparation starts no runtime. Each selected phase uses the unchanged reviewed
memory/allocation primitives and pinned launcher process-tree cleanup, because
the adapter creates nested child sessions. No compiler or old suite is run.
"""
import argparse
import datetime
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import time

from check_core import save, sha

PACKET = Path(__file__).resolve().parents[2]
REPO = PACKET.parents[1]
PYTHON = Path('/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3')
SITE = PYTHON.parent.parent / 'lib/python3.12/site-packages'
BINARY = Path('/dev/shm/rc-source-fit-native-20261010T221453.635194Z/target/debug/source-fit-solver')
APP = REPO / 'applications/practical-solver/run.py'
GUARD = Path(__file__).with_name('guard_g7_survival_run_20261010_v2.py')
FREEZES = {
    PACKET / 'rust/evidence/source-fit-component-reference-freeze-1/SOURCE-FREEZE.json': 'c63a4b7e074ac0b8624a427e197e798afb1bcc4afe0962053b50bb7074c7fcc8',
    PACKET / 'rust/evidence/source-fit-application-reference-freeze-1/SOURCE-FREEZE.json': '060cfede2c766d7f837ca8e5b3cb6ed3c1dfc58bcc2dc481306abe7ee110c8d9',
}


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepare():
    pins = {
        PYTHON: 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7',
        SITE / 'sympy/__init__.py': '4e9476348ba105feab28d82f5bcf6cdba2e3e84de6e059bbfe7a13728c0a4ab0',
        SITE / 'mpmath/__init__.py': 'b241584d2c1fc0304b0a1015ea923749d7b0800411dd406dcab7c82bf25d9fe8',
        BINARY: '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00',
        GUARD: '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4',
        REPO / 'applications/practical-solver/README.md': '326a03ec6bc1c86ec1c8fd75fd4921725ed4ed98940e5d5ebe059f5013b823c3',
        PACKET / 'rust/evidence/source-fit-saved-reference-20261010T223418.843872Z/FINAL-RECEIPT.json': 'bc1393c3c3e58e20847020dad99d75efe19514b6f494aad60522ec3588d0b9dd',
    }
    for freeze, digest in FREEZES.items():
        assert sha(freeze) == digest
        pins[freeze] = digest
        data = json.loads(freeze.read_bytes())
        for key in ['sources', 'fixture_origins', 'watched_unchanged']:
            for row in data.get(key, []):
                path = REPO / row['path']
                assert path not in pins or pins[path] == row['sha256']
                pins[path] = row['sha256']
    assert all(sha(path) == digest for path, digest in pins.items())
    guard = load('selected_reference_resource_guard', GUARD)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-source-fit-selected-reference-' + stamp)
    work.mkdir()
    roots = sorted(Path('/dev/shm').glob('rc-source-fit-*'))
    commands = {}
    for phase, script in [('component', 'review_source_fit_component_reference.py'),
                          ('application', 'review_source_fit_application_reference.py')]:
        command = [str(PYTHON), '-B', str(PACKET / 'rust' / script), '--binary', str(BINARY),
            '--reference-python', str(PYTHON), '--output', str(work / phase / 'review')]
        if phase == 'component':
            command += ['--four-copy-request', str(PACKET / 'design/fixtures/source-fit-reference-four-copy-fork.request.json')]
        commands[phase] = command
    plan = {'status': 'PREPARED_NO_RUNTIME_LAUNCHED', 'workspace': str(work),
        'coordinator_sha256': sha(Path(__file__)), 'pins': {str(p): h for p,h in pins.items()},
        'commands': commands, 'allocation_roots': list(map(str, roots)),
        'initial_memory': guard.memory(), 'initial_allocated_bytes': guard.allocated(roots),
        'estimated_additional_native_staging_bytes': 64 * 2**20,
        'native_hard_limit_bytes': 2**30, 'native_abort_bytes': 2**30 - 128 * 2**20,
        'memory_abort_bytes': 15 * 2**30, 'wall_seconds_each_phase': 240,
        'compiler_invoked': False, 'old_native_binary_or_sources_modified': False,
        'launch_order': ['component', 'application'],
        'launch_qualification': 'Authorized by root after accepted saved reference14 and after root large Lean-union review has finished; sole scheduler executes phases serially.',
        'cleanup': 'Pinned application launcher STOP_AND_WALK_LINUX_PROC includes nested process sessions.'}
    assert plan['initial_memory']['nonreclaimable_estimate'] < plan['memory_abort_bytes']
    assert plan['initial_allocated_bytes'] + plan['estimated_additional_native_staging_bytes'] < plan['native_abort_bytes']
    save(work / 'PLAN.json', plan)
    shutil.copyfile(Path(__file__), work / 'COORDINATOR.py')
    print(json.dumps({'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json'),
        'initial_native_allocated_bytes': plan['initial_allocated_bytes'], 'runtime_launched': False}), flush=True)


def run(work, phase):
    plan = json.loads((work / 'PLAN.json').read_bytes())
    assert plan['coordinator_sha256'] == sha(Path(__file__))
    assert not (work / phase).exists(), 'Each phase is executed once in its dated context.'
    if phase == 'application':
        predecessor = json.loads((work / 'component/OUTER-RECEIPT.json').read_bytes())
        assert predecessor['status'] == 'PASS_AUTHORIZED_REFERENCE_PHASE'
    pins = {Path(p): h for p,h in plan['pins'].items()}
    assert all(sha(path) == digest for path,digest in pins.items())
    guard = load('selected_reference_resource_guard', GUARD)
    cleanup = load('pinned_selected_reference_launcher', APP).terminate_process_tree
    roots = list(map(Path, plan['allocation_roots']))
    output = work / phase
    output.mkdir()
    save(output / 'PRE-LAUNCH-PINS.json', {str(p): sha(p) for p in pins})
    command = plan['commands'][phase]
    started = time.monotonic()
    error = None
    child = None
    peak_memory = peak_allocation = 0
    with (output / 'stdout').open('wb') as stdout, (output / 'stderr').open('wb') as stderr:
        try:
            assert guard.memory()['nonreclaimable_estimate'] < plan['memory_abort_bytes']
            assert guard.allocated(roots) < plan['native_abort_bytes']
            child = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
            with (output / 'RESOURCE-SAMPLES.jsonl').open('w') as samples:
                while child.poll() is None:
                    memory, allocation = guard.memory(), guard.allocated(roots)
                    peak_memory = max(peak_memory, memory['nonreclaimable_estimate'])
                    peak_allocation = max(peak_allocation, allocation)
                    samples.write(json.dumps({'elapsed_seconds': time.monotonic() - started,
                        'memory': memory, 'distinct_inode_allocated_bytes': allocation}) + '\n')
                    samples.flush()
                    assert memory['nonreclaimable_estimate'] < plan['memory_abort_bytes']
                    assert allocation < plan['native_abort_bytes']
                    assert time.monotonic() - started < plan['wall_seconds_each_phase']
                    time.sleep(0.1)
        except BaseException as exc:
            error = repr(exc)
        finally:
            if child is not None:
                if error is not None or child.poll() is None:
                    cleanup(child)
                rc = child.wait()
            else:
                rc = None
    record = {'status': 'PRESERVED_REFERENCE_PHASE_FAILURE', 'phase': phase, 'workspace': str(work),
        'plan_sha256': sha(work / 'PLAN.json'), 'command': command, 'exit_code': rc,
        'monitor_error': error, 'elapsed_seconds': time.monotonic() - started,
        'stdout_sha256': sha(output / 'stdout'), 'stderr_sha256': sha(output / 'stderr'),
        'compiler_invoked': False, 'old_native_binary_or_sources_modified': False}
    try:
        final_memory, final_allocation = guard.memory(), guard.allocated(roots)
        record.update(final_memory=final_memory, final_native_allocated_bytes=final_allocation,
            peak_nonreclaimable_bytes=max(peak_memory, final_memory['nonreclaimable_estimate']),
            peak_native_allocated_bytes=max(peak_allocation, final_allocation),
            post_pin_rechecks={str(p): sha(p) for p in pins})
        assert error is None and rc == 0
        assert final_memory['nonreclaimable_estimate'] < plan['memory_abort_bytes']
        assert final_allocation < plan['native_abort_bytes']
        assert all(sha(path) == digest for path,digest in pins.items())
        receipt_path = output / 'review/RECEIPT.json'
        receipt = json.loads(receipt_path.read_bytes())
        assert receipt['status'] == 'PASS'
        assert len(receipt['tests']) == (8 if phase == 'component' else 4)
        record.update(status='PASS_AUTHORIZED_REFERENCE_PHASE', passed_controls=len(receipt['tests']),
            review_receipt_sha256=sha(receipt_path), source_admission_verified=False,
            universal_native_refinement_verified=False, full_solver_verified=False)
    except BaseException as exc:
        record['verification_error'] = repr(exc)
    save(output / 'OUTER-RECEIPT.json', record)
    print(json.dumps({'status': record['status'], 'phase': phase, 'workspace': str(work),
        'outer_receipt_sha256': sha(output / 'OUTER-RECEIPT.json')}), flush=True)
    return 0 if record['status'].startswith('PASS_') else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--workspace', type=Path)
    parser.add_argument('--phase', choices=['component', 'application'])
    args = parser.parse_args()
    if args.prepare:
        assert not args.workspace and not args.phase
        prepare()
        return 0
    assert args.workspace and args.phase
    return run(args.workspace.resolve(strict=True), args.phase)


if __name__ == '__main__':
    raise SystemExit(main())
