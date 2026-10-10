#!/usr/bin/env python3
"""Prepare/run the authorized saved-witness transport34 and one existing app pipeline.

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
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def prepare():
    previous = Path('/dev/shm/rc-source-fit-selected-reference-20261010T224953.200869Z')
    assert sha(previous / 'PLAN.json') == 'fd3791e65e286a525950475ff342b1faae333aa9de0d98f9b7530ad4abe8c81e'
    pins = {Path(p): h for p,h in json.loads((previous / 'PLAN.json').read_bytes())['pins'].items()}
    for phase, expected in [('component', 'd0ef5eaeabed98c556c010034c642914503819635c743a4a1c77835badc1e6f4'),
                            ('application', 'e00c30f378678a912380e008db223136320749ed532d581b70c63b01fc39d16d')]:
        path = previous / phase / 'OUTER-RECEIPT.json'
        assert sha(path) == expected and json.loads(path.read_bytes())['status'] == 'PASS_AUTHORIZED_REFERENCE_PHASE'
        pins[path] = expected
    freeze = PACKET / 'rust/evidence/fitted-source-request-freeze-1/SOURCE-FREEZE.json'
    assert sha(freeze) == '1fda2e0d0d56151bd98a92870a6da4eb69f8ac45cfabd79a1bef389e0931381f'
    pins[freeze] = sha(freeze)
    data = json.loads(freeze.read_bytes())
    for key in ['sources', 'unchanged_watch']:
        for row in data[key]:
            base = REPO if row['path'].startswith(('applications/', 'research/')) else PACKET
            path = base / row['path']
            assert path not in pins or pins[path] == row['sha256']
            pins[path] = row['sha256']
    qc = PACKET / 'design/FITTER-WITNESS-TRANSPORT-HARNESS-STATIC-QC-20261010T2255Z.json'
    pins[qc] = 'bd74c5757f931675458a29eb9cf5d1b4c3072933b6d2909e21eb8df7d0fa2626'
    assert all(sha(path) == digest for path,digest in pins.items())
    guard = load('fitted_transport_resource_guard', GUARD)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-source-fit-fitted-transport-' + stamp)
    work.mkdir()
    roots = sorted(Path('/dev/shm').glob('rc-source-fit-*'))
    command = [str(PYTHON), '-B', str(PACKET / 'rust/review_fitted_source_request.py'),
        '--binary', str(BINARY), '--reference-python', str(PYTHON), '--output', str(work / 'transport/review')]
    plan = {'status': 'PREPARED_NO_RUNTIME_LAUNCHED', 'workspace': str(work),
        'coordinator_sha256': sha(Path(__file__)), 'pins': {str(p): h for p,h in pins.items()},
        'parent_coordinator_sha256': '9a5be627f6b127be7cb42dc62fe97c575dc35487cf7c2eae9df3f6453177701c',
        'derivation': 'Same reviewed phase monitor/cleanup/final thresholds; only frozen transport command/pins and its34-control receipt validation replace adapter8/application4.',
        'commands': {'transport': command}, 'allocation_roots': list(map(str, roots)),
        'initial_memory': guard.memory(), 'initial_allocated_bytes': guard.allocated(roots),
        'estimated_additional_native_staging_bytes': 32 * 2**20,
        'native_hard_limit_bytes': 2**30, 'native_abort_bytes': 2**30 - 128 * 2**20,
        'memory_abort_bytes': 15 * 2**30, 'wall_seconds_each_phase': 240,
        'compiler_invoked': False, 'fitter_or_semantic_source_checker_invoked': False,
        'old_native_binary_or_sources_modified': False,
        'launch_order': ['transport'], 'launch_qualification': 'Root authorized after repaired8+4 and Design ecbf harnessQC; sole scheduler at a Lean idle boundary.',
        'cleanup': 'Same pinned E21 launcher STOP_AND_WALK_LINUX_PROC includes nested native/reference sessions.'}
    assert plan['initial_memory']['nonreclaimable_estimate'] < plan['memory_abort_bytes']
    assert plan['initial_allocated_bytes'] + plan['estimated_additional_native_staging_bytes'] < plan['native_abort_bytes']
    save(work / 'PLAN.json', plan)
    shutil.copyfile(Path(__file__), work / 'COORDINATOR.py')
    print(json.dumps({'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json'),
        'coordinator_sha256': sha(Path(__file__)), 'pins': len(pins), 'initial_native_allocated_bytes': plan['initial_allocated_bytes'], 'runtime_launched': False}), flush=True)


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
        assert receipt['checks_passed'] == len(receipt['checks']) == 34
        assert len({r['name'] for r in receipt['checks']}) == 34
        assert all(r['pass'] is True for r in receipt['checks'])
        assert receipt['compiler_processes_started'] == receipt['fitter_processes_started'] == receipt['semantic_source_checker_processes_started'] == 0
        assert [r['name'] for r in receipt['processes']] == ['cli-export', 'cli-no-overwrite', 'application-process']
        assert [r['returncode'] for r in receipt['processes']] == [0, 1, 0]
        assert all(receipt[k] is False for k in ['source_admission_verified', 'source_observation_fit_verified', 'universal_native_refinement_verified', 'full_solver_verified'])
        record.update(status='PASS_AUTHORIZED_REFERENCE_PHASE', passed_controls=receipt['checks_passed'],
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
    parser.add_argument('--phase', choices=['transport'])
    args = parser.parse_args()
    if args.prepare:
        assert not args.workspace and not args.phase
        prepare()
        return 0
    assert args.workspace and args.phase
    return run(args.workspace.resolve(strict=True), args.phase)


if __name__ == '__main__':
    raise SystemExit(main())
