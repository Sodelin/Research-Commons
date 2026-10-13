#!/usr/bin/env python3
"""Prepare the exact provider closure in at most three serial guarded batches.

No compiler is launched on import. Each batch uses build_support.py's complete
source/external-state authentication and --prepare-provider, at most16 fresh
compilations, 5GiB virtual allowance and original4GiB physical stop. Run only
with the compiler slot free; see VIRTUAL-RESERVATION-REPAIR.json for the measured
reason for the virtual-only change.

The unchanged capture_batch helper uses an external-batch schema label. Its
MODULE-RECEIPTS.json is reused only as an invocation-evidence format here;
PROVIDER-SCOPE.json records the actual provider scope. OWNED-STATE-DELTA.json
separately preserves changed receipt/log bytes and copied Lean sources, including
authenticated-reuse receipts which emit no compiler event. No object bytes are
published. Preexisting state is inventoried, not represented as fresh execution.
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from capture_batch import capture, inventory, LOADED_SHA as CAPTURE_SHA

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
ROOT = HERE.parent.parent
PREVIOUS_MANIFEST_SHA = '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exclusive_json(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def source_inventory(state):
    return {str(path.relative_to(state)): digest(path)
            for path in sorted((state / 'source').rglob('*.lean'))}


def exact_file(path):
    data = path.read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
                exact_bytes_base64=base64.b64encode(data).decode('ascii'))


def preserve_delta(state, output, before, before_sources):
    """Preserve evidence before parsing receipts or calling generic capture."""
    after = dict(inventory(state), **source_inventory(state))
    previous = dict(before, **before_sources)
    changed = {name: exact_file(state / name) for name, value in sorted(after.items())
               if previous.get(name) != value}
    plan = state / 'PLAN.json'
    result = dict(schema='astra_owned_provider_state_delta_v1',
                  before_inventory=previous, after_inventory=after,
                  changed_files=changed,
                  missing_since_prebatch=sorted(set(previous) - set(after)),
                  selected_plan=exact_file(plan) if plan.is_file() else None,
                  interpretation='Preserved evidence bytes; this delta alone does not authenticate a successful compilation.',
                  binary_objects_included=False)
    path = output / 'OWNED-STATE-DELTA.json'
    exclusive_json(path, result)
    return digest(path)


def provider_ready(state):
    """Called only after successful guarded full state authentication."""
    modules = json.loads((state / 'PLAN.json').read_text())['modules']
    prefix = []
    for index, row in enumerate(modules):
        if row['kind'] == 'new_adapter':
            break
        prefix.append((index, row))
    else:
        raise ValueError('owned plan lacks the separate new-adapter stage')
    if not prefix:
        raise ValueError('empty provider stage')
    for index, row in prefix:
        path = state / f'{index:04d}.json'
        if not path.is_file():
            return False
        receipt = json.loads(path.read_text())
        if (receipt['exit_code'] != 0 or receipt['module'] != row['module']
                or receipt['source_sha256'] != row['sha256']):
            raise ValueError('provider-stage receipt differs after guarded authentication')
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--first-batch', type=int, required=True)
    parser.add_argument('--batches', type=int, default=3)
    parser.add_argument('--batch-size', type=int, default=16)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--external-state', type=Path, required=True)
    parser.add_argument('--owned-state', type=Path, required=True)
    parser.add_argument('--mathlib-root', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    args = parser.parse_args()
    if args.first_batch < 1 or not 1 <= args.batches <= 3 or not 1 <= args.batch_size <= 16:
        raise ValueError('positive first batch; at most three batches of at most16 fresh modules')
    for name in ['source_root', 'external_state', 'owned_state', 'mathlib_root', 'lean_bin']:
        setattr(args, name, getattr(args, name).resolve())
    if args.owned_state == args.external_state:
        raise ValueError('owned and external states must be separate')
    if (args.external_state / 'PLAN.json').read_bytes() != (HERE / 'EXTERNAL-PLAN.json').read_bytes():
        raise ValueError('external selection differs from exact selected closure')
    manifest_path = PREVIOUS / 'PACKET-MANIFEST.json'
    if digest(manifest_path) != PREVIOUS_MANIFEST_SHA:
        raise ValueError('published previous packet manifest differs')
    pins = {row['path']: row['sha256'] for row in json.loads(manifest_path.read_text())['files']}
    for name in ['guard.py', 'build_mathlib_serial.py', 'build_lean.py']:
        if digest(PREVIOUS / name) != pins[name]:
            raise ValueError('frozen runner changed: ' + name)
    build_runner = HERE / 'build_support.py'
    build_sha = digest(build_runner)
    record = dict(schema='astra_provider_batch_orchestration_v1',
                  runner_sha256=digest(Path(__file__)), build_runner_sha256=build_sha,
                  capture_runner_sha256=CAPTURE_SHA, first_batch=args.first_batch,
                  requested_batches=args.batches, batch_size=args.batch_size,
                  source_root=str(args.source_root), external_state=str(args.external_state),
                  owned_state=str(args.owned_state),
                  external_plan_sha256=digest(HERE / 'EXTERNAL-PLAN.json'), batches=[])
    record_path = HERE / 'evidence' / f'PROVIDER-ORCHESTRATOR-{args.first_batch:03d}.json'
    exclusive_json(record_path, record)
    for number in range(args.first_batch, args.first_batch + args.batches):
        if (HERE / 'PAUSE-BUILDS').exists():
            print(json.dumps(dict(status='PAUSED_BEFORE_NEXT_PROVIDER_BATCH', next_batch=number)), flush=True)
            break
        if digest(build_runner) != build_sha:
            raise ValueError('provider runner changed during orchestration')
        output = HERE / 'evidence' / f'provider-batch-{number:03d}'
        if output.exists():
            raise ValueError('provider evidence directory already exists: ' + str(output))
        before = inventory(args.owned_state)
        before_sources = source_inventory(args.owned_state)
        record['pending_batch'] = dict(number=number, prebatch_state=before,
                                       prebatch_sources=before_sources)
        record_path.write_text(json.dumps(record, indent=2) + '\n')
        command = [sys.executable, str(PREVIOUS / 'guard.py'), '--out', str(output),
                   '--cwd', str(ROOT), '--wall', '900', '--cpu', '600',
                   '--memory-mib', '5120', '--file-mib', '1024', '--',
                   sys.executable, '-B', str(build_runner),
                   '--source-root', str(args.source_root),
                   '--external-state', str(args.external_state),
                   '--state', str(args.owned_state),
                   '--mathlib-root', str(args.mathlib_root), '--lean-bin', str(args.lean_bin),
                   '--prepare-provider', '--batch', str(args.batch_size)]
        result = subprocess.run(command, cwd=ROOT)
        exclusive_json(output / 'PRE-BATCH-STATE.json', before)
        delta_sha = preserve_delta(args.owned_state, output, before, before_sources)
        entry = dict(number=number, command=command, exit_code=result.returncode,
                     receipt_sha256=digest(output / 'RECEIPT.json'), owned_delta_sha256=delta_sha)
        record['batches'].append(entry)
        del record['pending_batch']
        record_path.write_text(json.dumps(record, indent=2) + '\n')
        scope = dict(schema='astra_provider_batch_scope_v1',
                     operation='prepare_exact_accepted_provider_and_reused_kernel_certificates',
                     generic_capture_schema='astra_exact_external_batch_v2',
                     generic_capture_note='Invocation format reused unchanged; external-specific labels are not owned module counts or provider completion claims.',
                     owned_delta_sha256=delta_sha, provider_preparation_complete=False,
                     new_adapter_compilation_requested=False,
                     full1613_aggregate_compilation_claimed=False,
                     physical_representative_claimed=False)
        try:
            scope['invocation_capture'] = capture(args.owned_state, output)
            if result.returncode == 0:
                scope['provider_preparation_complete'] = provider_ready(args.owned_state)
        except Exception as error:
            scope['capture_or_scope_error'] = dict(type=type(error).__name__, message=str(error))
            exclusive_json(output / 'PROVIDER-SCOPE.json', scope)
            raise
        exclusive_json(output / 'PROVIDER-SCOPE.json', scope)
        if result.returncode:
            print(json.dumps(dict(status='STOPPED_ON_FAILED_PROVIDER_BATCH', batch=number)), flush=True)
            return result.returncode
        print(json.dumps(dict(status='PROVIDER_BATCH_CHECKPOINT', batch=number,
                              provider_preparation_complete=scope['provider_preparation_complete'],
                              new_adapter_compilation_claimed=False)), flush=True)
        if scope['provider_preparation_complete']:
            break
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
