#!/usr/bin/env python3
"""One fixed owned-provider batch; source-only draft, no automatic successor."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

ROOT = Path('/workspace/Research-Commons')
HERE = ROOT / 'research/2026-10-14-astra-detached-owned-batch-0025z'
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
PREVIOUS = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
TRANSPORT = ROOT / 'research/2026-10-13-astra-bounded-detached-guard-2320z/detached_transport.py'
SOURCE = Path('/workspace/scratch/astra-support-sources-0936')
EXTERNAL = Path('/workspace/scratch/astra-support-external-0840')
STATE = Path('/workspace/scratch/astra-support-owned-namespace-0025')
MATHLIB = Path('/workspace/scratch/astra-mathlib-0645')
LEAN_BIN = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')
PYTHON = '/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3'
PYTHON_SHA = 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7'
PINS_SHA = '0b1c54a9e69ae368dc25fbfcd5687bf31f228c9cd70de20b6dce7a61c1e225ff'
TRANSPORT_SHA = '4c396546825b108f48fe9633a0df576f78fb8af77830233c77751db1e9e56db1'
BUILDER_SHA = '2d5c8504c9380b5b2353539560b5b8e954cb2e909a09e5e80903214fc346ccda'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'
CAPTURE_SHA = 'c748a27508cec46ee243ebc77ab256f515f87fbbb0e5c8c2b28d654d22febad4'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def check_pins():
    if Path(__file__).resolve() != HERE / 'one_owned_batch.py' or digest(HERE / 'SOURCE-PINS.json') != PINS_SHA:
        raise ValueError('fixed driver location or source-pin record differs')
    pins = json.loads((HERE / 'SOURCE-PINS.json').read_text())
    for row in pins['files']:
        if digest(row['path']) != row['sha256']:
            raise ValueError('selected source/configuration changed: ' + row['path'])
    if digest(PYTHON) != PYTHON_SHA:
        raise ValueError('fixed Python executable differs')
    return pins


def load(name, path):
    if name in sys.modules:
        module = sys.modules[name]
        if Path(module.__file__).resolve() != path:
            raise ValueError('loaded provider origin differs: ' + name)
        return module
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def configured(batch, start, budget):
    if not 1 <= batch <= 999 or not 0 <= start <= 323 or not 1 <= budget <= 16:
        raise ValueError('explicit batch1..999, owned receipt start0..323, fresh budget1..16 required')
    pins = check_pins()
    transport = load('astra_owned_fixed_transport', TRANSPORT)
    capture = load('capture_batch', SUPPORT / 'capture_batch.py')
    helper = load('astra_owned_delta_helper', SUPPORT / 'run_provider_namespace_batches.py')
    if transport.LOADED_SHA != TRANSPORT_SHA or capture.LOADED_SHA != CAPTURE_SHA:
        raise ValueError('loaded transport/capture differs')
    output = HERE / 'evidence' / f'owned-batch-{batch:03d}'
    directory = HERE / 'evidence' / f'production-{batch:03d}'
    command = [PYTHON, '-B', str(PREVIOUS / 'guard.py'), '--out', str(output),
        '--cwd', str(ROOT), '--wall', '900', '--cpu', '600', '--memory-mib', '6144',
        '--file-mib', '1024', '--', PYTHON, '-B', str(SUPPORT / 'build_support_namespace.py'),
        '--source-root', str(SOURCE), '--external-state', str(EXTERNAL), '--state', str(STATE),
        '--mathlib-root', str(MATHLIB), '--lean-bin', str(LEAN_BIN), '--prepare-provider', '--batch', str(budget)]
    limits = dict(cpu_seconds=600, wall_seconds=900, address_space_bytes=6144 * 1024**2,
        file_bytes=1024**3, disk_floor=8 * 1024**3, ram_floor=1024**3, cgroup_stop=4 * 1024**3)
    profile = dict(name='fixed_detached_owned_provider_batch_v1', command=command,
        child_command=command[command.index('--') + 1:], cwd=str(ROOT), batch_output=str(output),
        python_exe=str(Path(PYTHON).resolve()), guard_sha256=GUARD_SHA, limits=limits,
        source_pins={row['path']: row['sha256'] for row in pins['files']}, source_pin_record_sha256=PINS_SHA,
        launcher_sha256=digest(__file__), transport_sha256=TRANSPORT_SHA,
        batch_id=batch, expected_start_index=start, fresh_budget=budget, owned_state=str(STATE),
        external_authentication='Guarded pinned builder verifies complete sources/logs/objects/routes before any compiler.',
        environment={'PATH': '/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
                     'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'PYTHONDONTWRITEBYTECODE': '1'})
    return transport, capture, helper, profile, output, directory


def preliminary(profile, output, capture, helper):
    """Refusal gates only; do not hash external objects outside the guard."""
    check_pins()
    if (SUPPORT / 'PAUSE-BUILDS').exists() or output.exists() or STATE.is_symlink():
        raise ValueError('paused or explicit batch output already exists')
    names = {'lean', 'lake', 'guard.py', 'build_external_serial.py', 'build_support.py',
        'build_support_namespace.py', 'run_external_batches.py', 'run_external_batches_6g.py',
        'run_provider_batches.py', 'run_provider_namespace_batches.py', 'one_guard.py', 'one_batch.py', 'one_batch_small.py',
        'one_owned_batch.py', 'diagnose_module.py', 'diagnose_thread_failure.py'}
    for path in Path('/proc').iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            state = (path / 'stat').read_text().rsplit(') ', 1)[1].split()[0]
            argv = (path / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if state not in ('Z', 'X') and any(Path(arg).name in names for arg in argv):
            raise ValueError('compiler/guard/launcher lane occupied')
    if (EXTERNAL / 'PLAN.json').read_bytes() != (SUPPORT / 'EXTERNAL-PLAN.json').read_bytes():
        raise ValueError('external selected plan differs')
    plan = json.loads((EXTERNAL / 'PLAN.json').read_text())
    if len(plan['modules']) != 3591:
        raise ValueError('selected external plan is not the frozen3591 closure')
    expected = {f'{index:04d}' for index in range(3591)}
    for suffix in ['json', 'stdout', 'stderr']:
        if {p.stem for p in EXTERNAL.glob('[0-9][0-9][0-9][0-9].' + suffix)} != expected:
            raise ValueError('external receipt/log set incomplete or orphaned; no owned pilot')
    for index, selected in enumerate(plan['modules']):
        receipt = json.loads((EXTERNAL / f'{index:04d}.json').read_text())
        if receipt['exit_code'] != 0 or any(receipt[k] != selected[k] for k in
               ['module', 'source', 'source_sha256', 'repo', 'target', 'imports']):
            raise ValueError('external receipt metadata is not the complete selected successful set')
    start = profile['expected_start_index']
    if profile['batch_id'] == 1:
        if start != 0 or STATE.exists() or STATE.is_symlink():
            raise ValueError('first pilot requires absent NEW owned state and start0')
    else:
        prior = HERE / 'evidence' / f"production-{profile['batch_id'] - 1:03d}" / 'FINISH.json'
        previous = json.loads(prior.read_text())
        if (not previous.get('provider_batch_verified') or previous['owned_state'] != str(STATE)
                or previous['next_owned_receipt_index'] != start or previous['provider_preparation_complete']):
            raise ValueError('previous owned checkpoint is not an authenticated resumable predecessor')
        delta_path = prior.parent / 'OWNED-STATE-DELTA.json'
        if digest(delta_path) != previous['owned_delta_sha256']:
            raise ValueError('previous owned evidence delta changed')
        delta = json.loads(delta_path.read_text())
        if (dict(capture.inventory(STATE), **helper.source_inventory(STATE)) != delta['after_inventory']
                or helper.exact_file(STATE / 'PLAN.json') != delta['selected_plan']
                or helper.exact_file(STATE / 'NAMESPACE-RESOLUTION.json') != delta['namespace_resolution']):
            raise ValueError('owned evidence/selected plan/namespace changed since previous closed batch')
    indices = sorted(int(p.stem) for p in STATE.glob('[0-9][0-9][0-9][0-9].json'))
    if indices != list(range(start)):
        raise ValueError('owned receipt prefix differs from explicit start')
    for index in indices:
        row = json.loads((STATE / f'{index:04d}.json').read_text())
        if row['exit_code'] != 0 or row['runner_sha256'] != BUILDER_SHA:
            raise ValueError('owned predecessor receipt failed or uses a different builder')
    return dict(status='PRELIMINARY_METADATA_REFUSAL_GATE_ONLY', external_receipts=3591,
                external_objects_authenticated=False, authoritative_gate='guarded build_support_namespace before compilation')


def before_state(capture, helper, preliminary_result):
    return dict(indexed=capture.inventory(STATE), sources=helper.source_inventory(STATE),
        selected_plan=helper.exact_file(STATE / 'PLAN.json') if (STATE / 'PLAN.json').exists() else None,
        namespace_resolution=helper.exact_file(STATE / 'NAMESPACE-RESOLUTION.json')
            if (STATE / 'NAMESPACE-RESOLUTION.json').exists() else None,
        preliminary=preliminary_result)


def finish(transport, capture, helper, profile, output, directory):
    status = transport.status(profile, directory)
    if status['status'] != 'ORIGINAL_PROCESS_NOT_RUNNING':
        raise transport.Refused('owned guard still running; no terminal capture')
    intent = json.loads((directory / 'INTENT.json').read_text())
    before_path = directory / 'PRE-BATCH-STATE.json'
    if digest(before_path) != intent['prebatch_sha256']:
        raise transport.Refused('prelaunch inventory changed')
    before = json.loads(before_path.read_text())
    # Preserve source/log/receipt/PLAN/NAMESPACE bytes before interpreting a receipt.
    # This also works when the guard never produced its output directory.
    delta_sha = helper.preserve_delta(STATE, directory, before['indexed'], before['sources'])
    result = dict(schema='astra_detached_owned_finish_v1', status='UNVERIFIED',
        observed_utc=transport.utc(), guard_process_exit_code=None, owned_state=str(STATE),
        launcher_sha256=digest(__file__), launch_sha256=digest(directory / 'LAUNCH.json'),
        prebatch_sha256=digest(before_path), owned_delta_sha256=delta_sha,
        owned_delta_path=str(directory / 'OWNED-STATE-DELTA.json'),
        provider_batch_verified=False, provider_preparation_complete=False,
        next_owned_receipt_index=None, fresh_invocations=[], newly_authenticated_clones=[],
        fresh_invocation_count=None, newly_authenticated_clone_count=None,
        resumed_receipts=None, no_automatic_next_batch=True,
        new_adapter_compilation_requested=False, actual_final_lake_target_run=False,
        final_axiom_audit_completed=False, full1613_aggregate_compiled=False,
        physical_representative_claimed=False, compiler_objects_independently_reaudited=False)
    try:
        terminal = transport.read_receipt(profile, directory)
        result.update(terminal)
        if terminal['guard_error'] or terminal['requested_stop']:
            result['interpretation'] = 'All changed bytes preserved as unverified; no success promotion after guard error/stop.'
        else:
            transport.write_new(output / 'PRE-BATCH-STATE.json', before['indexed'])
            result['invocation_capture'] = capture.capture(STATE, output)
            actual = json.loads((output / 'MODULE-RECEIPTS.json').read_text())
            if actual['prebatch_inventory_sha256'] != digest(output / 'PRE-BATCH-STATE.json') or actual['capture_runner_sha256'] != CAPTURE_SHA:
                raise ValueError('generic invocation capture binding differs')
            result['generic_capture_note'] = 'External schema is invocation evidence only; guard_exit_code is the builder code, not OS guard exit.'
            plan = json.loads((STATE / 'PLAN.json').read_text())
            if plan['runner_sha256'] != BUILDER_SHA:
                raise ValueError('owned plan builder changed')
            fresh = actual['completed_compiler_invocations']
            for entry in fresh:
                index, row = entry['index'], entry['receipt']
                selected = plan['modules'][index]
                if (index < profile['expected_start_index'] or row['execution'] != 'FRESH_SOURCE_COMPILE'
                        or row['runner_sha256'] != BUILDER_SHA or row['namespace_sha256'] != plan['namespace_sha256']
                        or row['module'] != selected['module'] or row['source_sha256'] != selected['sha256']
                        or selected['kind'] == 'new_adapter'):
                    raise ValueError('captured invocation differs from this owned provider stage')
            result['fresh_invocations'] = [dict(index=e['index'], module=e['receipt']['module'],
                exit_code=e['receipt']['exit_code'],
                compiler_exit_code=e['receipt'].get('compiler_exit_code', e['receipt']['exit_code']),
                receipt_sha256=e['receipt_sha256']) for e in fresh]
            result['fresh_invocation_count'] = len(fresh)
            result['interrupted_unverified_invocations'] = actual['interrupted_unverified_invocations']
            if terminal['status'] == 'GUARD_RECEIPT_SUCCESS':
                after = capture.inventory(STATE)
                for name, pin in before['indexed'].items():
                    if after.get(name) != pin:
                        raise ValueError('previous indexed evidence changed during successful batch')
                after_sources = helper.source_inventory(STATE)
                for name, pin in before['sources'].items():
                    if after_sources.get(name) != pin:
                        raise ValueError('previous copied selected source changed during successful batch')
                indices = sorted(int(p.stem) for p in STATE.glob('[0-9][0-9][0-9][0-9].json'))
                if indices != list(range(len(indices))):
                    raise ValueError('owned successful receipt prefix is not contiguous')
                new_rows = []
                for index in range(profile['expected_start_index'], len(indices)):
                    row = json.loads((STATE / f'{index:04d}.json').read_text())
                    selected = plan['modules'][index]
                    saved_source = STATE / 'source' / Path(*selected['module'].split('.')).with_suffix('.lean')
                    if (row['exit_code'] or row['runner_sha256'] != BUILDER_SHA
                            or row['namespace_sha256'] != plan['namespace_sha256']
                            or row['module'] != selected['module'] or row['source_sha256'] != selected['sha256']
                            or selected['kind'] == 'new_adapter' or digest(saved_source) != selected['sha256']):
                        raise ValueError('new owned receipt/source differs from successful selected plan')
                    new_rows.append((index, row))
                clones = [(i, r) for i, r in new_rows if r['execution'] == 'AUTHENTICATED_REUSE']
                if (len(fresh) > profile['fresh_budget'] or any(e['receipt']['exit_code'] for e in fresh)
                        or {e['index'] for e in fresh} != {i for i, r in new_rows if r['execution'] == 'FRESH_SOURCE_COMPILE'}
                        or len(fresh) + len(clones) != len(new_rows)):
                    raise ValueError('fresh versus clone accounting differs')
                summary = []
                for line in (output / 'stdout').read_text().splitlines():
                    try:
                        entry = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    if isinstance(entry, dict) and entry.get('status') == 'BATCH_COMPLETE':
                        summary.append(entry)
                if (len(summary) != 1 or summary[0]['freshly_compiled'] != len(fresh)
                        or summary[0]['authenticated_reuse'] != profile['expected_start_index'] + len(clones)):
                    raise ValueError('builder summary conflates new clones, resumed receipts or fresh invocations')
                ready = helper.provider_ready(STATE)
                if len(fresh) != profile['fresh_budget'] and not ready:
                    raise ValueError('successful short batch did not finish its provider stage')
                result.update(provider_batch_verified=True, provider_preparation_complete=ready,
                    next_owned_receipt_index=len(indices), resumed_receipts=profile['expected_start_index'],
                    newly_authenticated_clone_count=len(clones),
                    newly_authenticated_clones=[dict(index=i, module=r['module'], origin=r['origin'],
                        receipt_sha256=digest(STATE / f'{i:04d}.json')) for i, r in clones],
                    authentication_basis='Pinned guarded builder completed exact source/log/object and namespace checks; no independent object re-audit by capture.')
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        result.update(status='UNVERIFIED_CAPTURE_OR_TERMINAL_ERROR', provider_batch_verified=False,
                      provider_preparation_complete=False,
                      error=dict(type=type(error).__name__, message=str(error)))
    transport.write_new(directory / 'FINISH.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['launch', 'status', 'stop', 'finish'])
    parser.add_argument('--batch-id', type=int, required=True)
    parser.add_argument('--start-index', type=int, required=True)
    parser.add_argument('--fresh-budget', type=int, required=True)
    args = parser.parse_args()
    transport, capture, helper, profile, output, directory = configured(args.batch_id, args.start_index, args.fresh_budget)
    if args.action == 'launch':
        preliminary_result = preliminary(profile, output, capture, helper)
        before = before_state(capture, helper, preliminary_result)
        def last_preflight():
            preliminary(profile, output, capture, helper)
            if before_state(capture, helper, preliminary_result) != before:
                raise ValueError('owned preinventory changed before launch')
        result = transport.launch(profile, directory, before, last_preflight)
    elif args.action == 'status':
        result = transport.status(profile, directory)
    elif args.action == 'stop':
        result = transport.stop(profile, directory)
    else:
        result = finish(transport, capture, helper, profile, output, directory)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        print(json.dumps(dict(status='REFUSED_OR_UNVERIFIED', completion_verified=False,
            error=type(error).__name__, message=str(error))), file=sys.stderr)
        raise SystemExit(2)
