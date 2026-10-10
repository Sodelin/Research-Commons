#!/usr/bin/env python3
"""Run the authorized saved-output reference review in a guarded Python slot.

This coordinator launches no native executable or compiler. It retains the
existing native scratch policy and the reviewed resource-monitor primitives.
"""
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
REVIEW = PACKET / 'design/review_source_fit_reference.py'
GUARD = Path(__file__).with_name('guard_g7_survival_run_20261010_v2.py')
SITE = PYTHON.parent.parent / 'lib/python3.12/site-packages'
PINS = {
    PYTHON: 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7',
    REVIEW: '013954eb3570cecf64707444a1548b8a236602e330b649bdc5e9b28cdef9e799',
    GUARD: '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4',
    PACKET / 'design/certificate_check.py': 'ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24',
    PACKET / 'design/chart_check.py': '3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a',
    PACKET / 'design/source_fit_reference.py': '0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6',
    REPO / 'research/2026-10-01-g7-continuous-design/law_compiler.py': 'eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7',
    SITE / 'sympy/__init__.py': '4e9476348ba105feab28d82f5bcf6cdba2e3e84de6e059bbfe7a13728c0a4ab0',
    SITE / 'mpmath/__init__.py': 'b241584d2c1fc0304b0a1015ea923749d7b0800411dd406dcab7c82bf25d9fe8',
}
CASES = [
    ('hybrid-common-sat', '63d6b2242c428d98fe89c3c6e6295948026de220095a3fe852d5e66069db6591', '3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039'),
    ('hybrid-independent-sat', '0d3d30b9be0cf8ccbb9473c5fdeffd6a4c6a129fa122fff1ea0b181411dd7ef4', '16bc758e3cc05c9277859bac9c29b3b3586de7ff9d8c379011303ecdef0bcbdb'),
    ('hybrid-common-permuted', 'a01f07c1cd2fa5a84880bd46ea7a3890356af9c936ca4873ebd5bb7b5f40875e', '446d2dfb9f66dca6155ffbb48d5a39c3aa7550175441a043cac57457fd59e352'),
]


def main():
    pins = dict(PINS)
    saved = PACKET / 'rust/evidence/source-fit-native-slot-20261010T221453.635194Z/cli-challenges'
    for name, input_hash, output_hash in CASES:
        pins[PACKET / f'rust/fixtures/source-fit/{name}.request.json'] = input_hash
        pins[saved / f'{name}-readout-file/stdout'] = output_hash
    assert all(sha(path) == digest for path, digest in pins.items())
    spec = importlib.util.spec_from_file_location('reviewed_resource_guard', GUARD)
    guard = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(guard)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-source-fit-saved-reference-' + stamp)
    work.mkdir()
    roots = sorted(Path('/dev/shm').glob('rc-source-fit-*'))
    command = [str(PYTHON), '-I', '-B', str(REVIEW), '--output', str(work / 'review')]
    plan = {'status': 'PRE_USE_SAVED_OUTPUT_REFERENCE_ONLY', 'workspace': str(work),
        'coordinator_sha256': sha(Path(__file__)), 'command': command,
        'pins': {str(path): digest for path, digest in pins.items()},
        'allocation_roots': list(map(str, roots)), 'native_hard_limit_bytes': 2**30,
        'native_abort_bytes': 2**30 - 128 * 2**20, 'memory_abort_bytes': 15 * 2**30,
        'wall_seconds': 180, 'native_processes_started': 0, 'compiler_processes_started': 0,
        'prior_native_outputs_reused_without_rerun': True, 'initial_memory': guard.memory(),
        'initial_allocated_bytes': guard.allocated(roots)}
    assert plan['initial_memory']['nonreclaimable_estimate'] < plan['memory_abort_bytes']
    assert plan['initial_allocated_bytes'] < plan['native_abort_bytes']
    save(work / 'PLAN.json', plan)
    shutil.copyfile(Path(__file__), work / 'COORDINATOR.py')
    print(json.dumps({'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json')}), flush=True)
    started = time.monotonic()
    child = None
    error = None
    peak_memory = plan['initial_memory']['nonreclaimable_estimate']
    peak_allocation = plan['initial_allocated_bytes']
    with (work / 'stdout').open('wb') as stdout, (work / 'stderr').open('wb') as stderr:
        try:
            assert all(sha(path) == digest for path, digest in pins.items())
            child = subprocess.Popen(command, stdout=stdout, stderr=stderr, start_new_session=True)
            with (work / 'RESOURCE-SAMPLES.jsonl').open('w') as samples:
                while child.poll() is None:
                    memory = guard.memory()
                    allocation = guard.allocated(roots)
                    peak_memory = max(peak_memory, memory['nonreclaimable_estimate'])
                    peak_allocation = max(peak_allocation, allocation)
                    samples.write(json.dumps({'elapsed_seconds': time.monotonic() - started,
                        'memory': memory, 'distinct_inode_allocated_bytes': allocation}) + '\n')
                    samples.flush()
                    assert memory['nonreclaimable_estimate'] < plan['memory_abort_bytes']
                    assert allocation < plan['native_abort_bytes']
                    assert time.monotonic() - started < plan['wall_seconds']
                    time.sleep(0.1)
        except BaseException as exc:
            error = repr(exc)
        finally:
            if child is not None:
                if error is not None or child.poll() is None:
                    guard.terminate_group(child)
                rc = child.wait()
            else:
                rc = None
    record = {'status': 'PRESERVED_REFERENCE_FAILURE', 'workspace': str(work),
        'plan_sha256': sha(work / 'PLAN.json'), 'exit_code': rc, 'monitor_error': error,
        'elapsed_seconds': time.monotonic() - started, 'native_processes_started': 0,
        'compiler_processes_started': 0, 'stdout_sha256': sha(work / 'stdout'),
        'stderr_sha256': sha(work / 'stderr')}
    try:
        final_memory, final_allocation = guard.memory(), guard.allocated(roots)
        record.update(final_memory=final_memory, final_allocated_bytes=final_allocation,
            peak_nonreclaimable_bytes=max(peak_memory, final_memory['nonreclaimable_estimate']),
            peak_native_allocated_bytes=max(peak_allocation, final_allocation),
            pin_rechecks={str(path): sha(path) for path in pins})
        assert final_memory['nonreclaimable_estimate'] < plan['memory_abort_bytes']
        assert final_allocation < plan['native_abort_bytes']
        assert error is None and rc == 0
        assert all(sha(path) == digest for path, digest in pins.items())
        receipt = json.loads((work / 'review/RECEIPT.json').read_bytes())
        assert receipt['status'] == 'PASS' and receipt['passed'] == 14
        assert receipt['native_processes_started'] == receipt['lean_compiler_processes_started'] == 0
        assert receipt['runtime_observed']['sympy']['version'] == '1.14.0'
        assert receipt['runtime_observed']['mpmath']['version'] == '1.3.0'
        for package in ['sympy', 'mpmath']:
            assert receipt['runtime_observed'][package]['initializer_sha256'] == pins[SITE / package / '__init__.py']
        record.update(status='PASS_FOURTEEN_SAVED_OUTPUT_REFERENCE_CONTROLS',
            review_receipt_sha256=sha(work / 'review/RECEIPT.json'), passed=14,
            saved_native_rows=receipt['saved_native_rows'], saved_native_terms=receipt['saved_native_terms'],
            source_admission_verified=False, timed_readout_verified=False,
            universal_native_refinement_verified=False, full_solver_verified=False)
    except BaseException as exc:
        record['verification_error'] = repr(exc)
    save(work / 'FINAL-RECEIPT.json', record)
    print(json.dumps({'status': record['status'], 'workspace': str(work),
        'final_receipt_sha256': sha(work / 'FINAL-RECEIPT.json')}), flush=True)
    return 0 if record['status'].startswith('PASS_') else 1


if __name__ == '__main__':
    raise SystemExit(main())
