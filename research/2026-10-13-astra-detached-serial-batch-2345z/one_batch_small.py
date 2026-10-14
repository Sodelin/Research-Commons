#!/usr/bin/env python3
"""Smaller-budget successor; same fixed builders, paths and resource profile.

Only adds budgets4 and8 to the preserved predecessor selection; no automatic
next job or resource-limit change."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PREDECESSOR = HERE.parent / '2026-10-13-astra-bounded-detached-guard-2320z'
OLD_LAUNCHER_SHA = '71e353bd20c877248580e0bed8a9b4b0bb312cae08d7b7854260c4293cbc50eb'
TRANSPORT_SHA = '4c396546825b108f48fe9633a0df576f78fb8af77830233c77751db1e9e56db1'


def providers():
    import hashlib
    for name, pin in [('one_guard.py', OLD_LAUNCHER_SHA), ('detached_transport.py', TRANSPORT_SHA)]:
        if hashlib.sha256((PREDECESSOR / name).read_bytes()).hexdigest() != pin:
            raise ValueError('reviewed predecessor changed: ' + name)
    sys.path.insert(0, str(PREDECESSOR))
    try:
        import detached_transport as transport
        spec = importlib.util.spec_from_file_location('astra_fixed_predecessor', PREDECESSOR / 'one_guard.py')
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
    finally:
        sys.path.pop(0)
    if Path(transport.__file__).resolve() != PREDECESSOR / 'detached_transport.py' or transport.LOADED_SHA != TRANSPORT_SHA:
        raise ValueError('loaded transport origin or bytes differ')
    return old, transport


def configured(old, transport, batch_id, start, budget):
    if not 63 <= batch_id <= 999 or not 0 <= start < 3591 or budget not in (1, 4, 8, 16, 32, 64):
        raise ValueError('unsupported explicit batch selection')
    profile, capture = old.configured()
    output = old.SUPPORT / 'evidence' / f'external-batch-{batch_id:03d}'
    directory = HERE / 'evidence' / f'production-{batch_id:03d}'
    command = profile['command'][:]
    command[command.index('--out') + 1] = str(output)
    command[-1] = str(budget)
    delimiter = command.index('--')
    profile.update(name='explicit_detached_serial_batch_smaller_budgets_v1', command=command,
        child_command=command[delimiter + 1:], batch_output=str(output),
        expected_start_index=start, fresh_budget=budget, expected_fresh_count=min(budget, 3591 - start),
        launcher_sha256=transport.digest(__file__), predecessor_launcher_sha256=OLD_LAUNCHER_SHA,
        transport_sha256=TRANSPORT_SHA, batch_id=batch_id)
    return profile, capture, output, directory


def preflight(old, transport, output, start):
    if (old.SUPPORT / 'PAUSE-BUILDS').exists() or output.exists():
        raise transport.Refused('paused or selected output already exists')
    names = {'lean', 'lake', 'guard.py', 'build_external_serial.py', 'build_support.py',
        'run_external_batches.py', 'run_external_batches_6g.py', 'run_provider_batches.py',
        'diagnose_module.py', 'diagnose_thread_failure.py', 'one_guard.py', 'one_batch.py', 'one_batch_small.py'}
    import os
    for path in Path('/proc').iterdir():
        if not path.name.isdigit() or int(path.name) == os.getpid():
            continue
        try:
            state = (path / 'stat').read_text().rsplit(') ', 1)[1].split()[0]
            argv = (path / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
        except (FileNotFoundError, ProcessLookupError):
            continue
        if state not in ('Z', 'X') and any(Path(arg).name in names for arg in argv):
            raise transport.Refused('compiler/guard/launcher lane is occupied; no launch')
    indices = sorted(int(path.stem) for path in old.STATE.glob('[0-9][0-9][0-9][0-9].json'))
    if indices != list(range(start)):
        raise transport.Refused('actual receipt prefix differs from explicit starting index')
    # The pinned builder independently authenticates every existing source/log/object.


def finish(old, transport, profile, capture, output, directory):
    terminal = transport.read_receipt(profile, directory)
    intent = json.loads((directory / 'INTENT.json').read_text())
    before = directory / 'PRE-BATCH-STATE.json'
    if transport.digest(before) != intent['prebatch_sha256']:
        raise transport.Refused('prelaunch inventory changed')
    target = output / 'PRE-BATCH-STATE.json'
    if target.exists():
        if target.read_bytes() != before.read_bytes():
            raise transport.Refused('existing capture inventory differs')
    else:
        with target.open('xb') as stream:
            stream.write(before.read_bytes())
    if terminal['guard_error'] or terminal['requested_stop']:
        import base64
        previous = json.loads(before.read_text())
        changed = {}
        for name, pin in capture.inventory(old.STATE).items():
            if previous.get(name) != pin:
                data = (old.STATE / name).read_bytes()
                changed[name] = dict(bytes=len(data), sha256=pin,
                    exact_bytes_base64=base64.b64encode(data).decode())
        capture_path = directory / 'INTERRUPTED-UNVERIFIED.json'
        checked = dict(status='UNVERIFIED_CHANGED_BYTES_NO_COMPLETION_CLAIM',
            guard_receipt_sha256=terminal['guard_receipt_sha256'], changed=changed)
        transport.write_new(capture_path, checked)
    else:
        checked = capture.capture(old.STATE, output, check_existing=(output / 'MODULE-RECEIPTS.json').exists())
        capture_path = output / 'MODULE-RECEIPTS.json'
        actual = json.loads(capture_path.read_text())
        if actual['prebatch_inventory_sha256'] != transport.digest(before) or actual['capture_runner_sha256'] != old.PINS[str(old.SUPPORT / 'capture_batch.py')]:
            raise transport.Refused('capture source/inventory binding differs')
        if terminal['status'] == 'GUARD_RECEIPT_SUCCESS':
            rows = actual['completed_compiler_invocations']
            expected = list(range(profile['expected_start_index'],
                profile['expected_start_index'] + profile['expected_fresh_count']))
            if [row['index'] for row in rows] != expected or any(row['receipt']['exit_code'] for row in rows):
                raise transport.Refused('actual completed invocations differ from explicit contiguous batch')
    result = dict(schema='astra_explicit_serial_finish_v1', observed_utc=transport.utc(), **terminal,
        launch_sha256=transport.digest(directory / 'LAUNCH.json'),
        prebatch_sha256=transport.digest(before), capture=checked,
        capture_sha256=transport.digest(capture_path), capture_path=str(capture_path),
        no_automatic_next_batch=True, compiler_objects_independently_reaudited=False)
    transport.write_new(directory / 'FINISH.json', result)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['launch', 'status', 'stop', 'finish'])
    parser.add_argument('--batch-id', type=int, required=True)
    parser.add_argument('--start-index', type=int, required=True)
    parser.add_argument('--fresh-budget', type=int, choices=[1, 4, 8, 16, 32, 64], required=True)
    args = parser.parse_args()
    try:
        old, transport = providers()
        profile, capture, output, directory = configured(old, transport, args.batch_id, args.start_index, args.fresh_budget)
        if args.action == 'launch':
            preflight(old, transport, output, args.start_index)
            result = transport.launch(profile, directory, capture.inventory(old.STATE),
                lambda: preflight(old, transport, output, args.start_index))
        elif args.action == 'status':
            result = transport.status(profile, directory)
        elif args.action == 'stop':
            result = transport.stop(profile, directory)
        else:
            result = finish(old, transport, profile, capture, output, directory)
        print(json.dumps(result, indent=2))
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        print(json.dumps(dict(status='REFUSED_OR_UNVERIFIED', error=type(error).__name__,
            message=str(error), completion_verified=False)), file=sys.stderr)
        raise SystemExit(2)
