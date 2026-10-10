#!/usr/bin/env python3
"""Focused, serial Rust source-fit build in a separately bounded dated target.

Preparation is separate from execution. Original source/native/target paths are
read-only inputs. This reuses the reviewed external memory/cleanup monitor, not
the Lean builder, and changes no Lean caps or source-refinement claims.
"""
from __future__ import annotations

import argparse
import datetime
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from check_core import save, sha

PACKET = Path(__file__).resolve().parents[2]
RUST = PACKET / 'rust'
UTILITY = Path(__file__).parent / 'guard_g7_survival_run_20261010_v2.py'
UTILITY_SHA = '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4'


def utility():
    assert sha(UTILITY) == UTILITY_SHA
    spec = importlib.util.spec_from_file_location('reviewed_memory_guard', UTILITY)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workspace', type=Path)
    args = parser.parse_args()
    guard = utility()
    if not args.workspace:
        expected = {'src/source_fit_bank.rs': 'e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a',
                    'src/source_fit_readout.rs': '7a3a75b60af55f1138e82aa66c5a2e94b5dc9c8a597eadb0ff25230f03dae7c5',
                    'calendar-cli/src/source_fit_forward.rs': '0eef0719f7e5343bd3fc4655cc0dbba629dc29afe79e3cc7638e22fd8e03d2d5',
                    'calendar-cli/src/source_fit.rs': 'a4e86fe9948ab93f6128f430e9182b445c69b580f9fee01161f95f41a9966839',
                    'calendar-cli/src/source_fit_main.rs': 'b4b539439678b4a681c385ee1472072f648caf30cd53a8d501171e4034b8454e'}
        assert all(sha(RUST / p) == h for p, h in expected.items())
        roots = [RUST, RUST / 'calendar-cli', RUST.parent.parent / '2026-10-08-cloud-rust-interval-root-0000z',
                 RUST.parent.parent / '2026-10-08-cloud-rust-signed-nine-0008z', RUST.parent.parent / '2026-10-07-rust-count-pilot']
        pins = {}
        for root in roots:
            assert root.is_dir()
            for source in [root / 'Cargo.toml', root / 'Cargo.lock', *sorted((root / 'src').rglob('*.rs'))]:
                if source.is_file():
                    pins[str(source)] = {'sha256': sha(source), 'bytes': source.stat().st_size}
        cargo = Path(shutil.which('cargo')).resolve(strict=True)
        rustc = Path(shutil.which('rustc')).resolve(strict=True)
        assert shutil.disk_usage('/dev/shm').free > 2**30
        measured = guard.memory()
        assert measured['nonreclaimable_estimate'] < 15 * 2**30
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
        work = Path('/dev/shm') / ('rc-source-fit-native-' + stamp)
        work.mkdir()
        commands = [
            {'name': 'library-source-fit', 'cwd': str(RUST), 'args': ['test', '--offline', '--locked', '--jobs', '1', '--lib', 'source_fit']},
            {'name': 'frontend-source-fit', 'cwd': str(RUST / 'calendar-cli'), 'args': ['test', '--offline', '--locked', '--jobs', '1', '--lib', 'source_fit']},
            {'name': 'source-fit-solver-build', 'cwd': str(RUST / 'calendar-cli'), 'args': ['build', '--offline', '--locked', '--jobs', '1', '--bin', 'source-fit-solver']},
        ]
        plan = {'status': 'PRE_USE_FOCUSED_NATIVE_SLOT_PLAN', 'workspace': str(work),
                'runner_sha256': sha(Path(__file__)), 'reviewed_guard_sha256': UTILITY_SHA,
                'source_pins': pins, 'owned_source_pins': expected, 'cargo': str(cargo), 'cargo_sha256': sha(cargo),
                'rustc': str(rustc), 'rustc_sha256': sha(rustc), 'commands': commands,
                'environment': {'CARGO_TARGET_DIR': str(work / 'target'), 'CARGO_INCREMENTAL': '0',
                                'CARGO_PROFILE_DEV_DEBUG': '0', 'CARGO_PROFILE_TEST_DEBUG': '0'},
                'native_scratch_limit_bytes': 2**30, 'native_abort_with_transient_headroom_bytes': 2**30 - 128 * 2**20,
                'shared_nonreclaimable_memory_abort_bytes': 15 * 2**30, 'initial_memory': measured,
                'source_bytes': sum(v['bytes'] for v in pins.values()),
                'empirical_target_estimate_qualification': 'Source owner estimates100–250MiB, unmeasured. Hard abort leaves128MiB under a separately authorized1GiB native target limit.',
                'authorization': 'Root focused native bank/readout/frontend command authorization after design staticPASS; separate slot, no concurrent Lean or native compiler.',
                'lean_scratch_policy_or_compiler_flags_changed': False, 'old_native_or_target_paths_written': False}
        save(work / 'PLAN.json', plan)
        shutil.copyfile(Path(__file__), work / 'RUNNER.py')
        save(work / 'RUSTC-VERSION.json', {'stdout': subprocess.check_output([str(rustc), '-vV'], text=True)})
        print(json.dumps({'status': plan['status'], 'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json'),
                          'runner_sha256': plan['runner_sha256'], 'source_bytes': plan['source_bytes'], 'commands': commands}))
        return
    work = args.workspace.resolve(strict=True)
    plan = json.loads((work / 'PLAN.json').read_bytes())
    assert sha(Path(__file__)) == plan['runner_sha256'] and sha(UTILITY) == plan['reviewed_guard_sha256']
    assert sha(Path(plan['cargo'])) == plan['cargo_sha256'] and sha(Path(plan['rustc'])) == plan['rustc_sha256']
    assert not (work / 'FINAL-RECEIPT.json').exists()
    env = dict(os.environ, **plan['environment'])
    steps = []
    for step in plan['commands']:
        assert all(sha(Path(p)) == pin['sha256'] for p, pin in plan['source_pins'].items())
        assert guard.memory()['nonreclaimable_estimate'] < plan['shared_nonreclaimable_memory_abort_bytes']
        assert guard.allocated([work]) < plan['native_abort_with_transient_headroom_bytes']
        out = work / step['name']
        out.mkdir()
        command = [plan['cargo'], *step['args']]
        reason, error = None, None
        peak_mem = peak_alloc = 0
        started = time.monotonic()
        with (out / 'stdout').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
            child = subprocess.Popen(command, cwd=step['cwd'], env=env, stdout=stdout, stderr=stderr, start_new_session=True)
            try:
                with (out / 'RESOURCE-SAMPLES.jsonl').open('a') as samples:
                    while child.poll() is None:
                        m, a = guard.memory(), guard.allocated([work])
                        peak_mem, peak_alloc = max(peak_mem, m['nonreclaimable_estimate']), max(peak_alloc, a)
                        samples.write(json.dumps({'seconds': round(time.monotonic() - started, 3), **m, 'allocated_bytes': a}) + '\n')
                        samples.flush()
                        if m['nonreclaimable_estimate'] >= plan['shared_nonreclaimable_memory_abort_bytes']:
                            reason = 'SHARED_MEMORY_GUARD'
                        elif a >= plan['native_abort_with_transient_headroom_bytes']:
                            reason = 'NATIVE_TARGET_ALLOCATION_GUARD'
                        if reason:
                            guard.terminate_group(child)
                            break
                        time.sleep(0.5)
            except BaseException as exc:
                reason, error = 'MONITOR_EXCEPTION', repr(exc)
            finally:
                if error is not None or child.poll() is None:
                    guard.terminate_group(child)
                rc = child.wait()
        m, a = guard.memory(), guard.allocated([work])
        if m['nonreclaimable_estimate'] >= plan['shared_nonreclaimable_memory_abort_bytes'] or a >= plan['native_abort_with_transient_headroom_bytes']:
            reason = reason or 'FINAL_RESOURCE_THRESHOLD_EXCEEDED'
        source_stable = all(sha(Path(p)) == pin['sha256'] for p, pin in plan['source_pins'].items())
        result = {'status': 'PASS' if rc == 0 and reason is None and source_stable else 'PRESERVED_NATIVE_FAILURE',
                  'name': step['name'], 'command': command, 'cwd': step['cwd'], 'exit_code': rc,
                  'abort_reason': reason, 'monitor_error': error, 'source_pins_stable': source_stable,
                  'elapsed_seconds': time.monotonic() - started, 'peak_nonreclaimable_bytes': max(peak_mem, m['nonreclaimable_estimate']),
                  'peak_allocated_bytes': max(peak_alloc, a), 'stdout_sha256': sha(out / 'stdout'), 'stderr_sha256': sha(out / 'stderr')}
        save(out / 'RECEIPT.json', result)
        steps.append(result)
        print(json.dumps(result), flush=True)
        if result['status'] != 'PASS':
            break
    final = {'status': 'PASS_ALL_FOCUSED_NATIVE_COMMANDS' if len(steps) == len(plan['commands']) and all(r['status'] == 'PASS' for r in steps) else 'PRESERVED_NATIVE_COMMAND_FAILURE',
             'workspace': str(work), 'plan_sha256': sha(work / 'PLAN.json'), 'steps': steps,
             'target_allocated_bytes': guard.allocated([work]), 'lean_or_old_native_targets_written': False,
             'source_and_toolchain_pins_stable': all(sha(Path(p)) == pin['sha256'] for p, pin in plan['source_pins'].items())}
    binary = work / 'target/debug/source-fit-solver'
    if binary.is_file():
        final['private_binary'] = {'path': str(binary), 'sha256': sha(binary), 'bytes': binary.stat().st_size}
    save(work / 'FINAL-RECEIPT.json', final)
    print(json.dumps(final))
    raise SystemExit(0 if final['status'].startswith('PASS_') else 1)


if __name__ == '__main__':
    main()
