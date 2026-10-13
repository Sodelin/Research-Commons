#!/usr/bin/env python3
"""Fixed one-module external batch062 launcher. No arbitrary exec/kill interface."""
import argparse
import base64
import importlib.util
import json
from pathlib import Path
import sys

from detached_transport import Refused, digest, launch, status, stop, read_receipt, write_new, utc

HERE = Path(__file__).resolve().parent
ROOT = Path('/workspace/Research-Commons')
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
PREVIOUS = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
STATE = Path('/workspace/scratch/astra-support-external-0840')
OUTPUT = SUPPORT / 'evidence/external-batch-062'
DIRECTORY = HERE / 'evidence/production-062'
PYTHON = '/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3'
EXPECTED_INDEX = 2992
PINS = {
    str(PREVIOUS / 'guard.py'): 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3',
    str(PREVIOUS / 'PACKET-MANIFEST.json'): '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5',
    str(SUPPORT / 'build_external_serial.py'): '00c9c98b2490f8bd35c9ea644aba78171d3bddbfc8735a30b2a855c55285df8f',
    str(SUPPORT / 'serial_compile.py'): 'd47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28',
    str(SUPPORT / 'capture_batch.py'): 'c748a27508cec46ee243ebc77ab256f515f87fbbb0e5c8c2b28d654d22febad4',
    str(SUPPORT / 'run_external_batches_6g.py'): '11e3fd84ca11692760ecd428801e176b666e4b19f7fb2bcbd04169de7970713c',
    str(SUPPORT / 'EXTERNAL-PLAN.json'): 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10',
    str(SUPPORT / 'evidence/ORCHESTRATOR-060.json'): 'd8eefd80c7e6affb6c35c6e0316f06ba69947c90fd3175c3f4407bcc5a0ec022',
    str(Path(PYTHON).with_name('python3.12')): 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7',
    '/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin/lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    '/workspace/scratch/astra-mathlib-0645/lakefile.lean': '9618b4491ba2a0ce2edde2cd29a6ff12974ccec5b331773ad0ae679cbebbc857',
}


def configured():
    if HERE != ROOT / 'research/2026-10-13-astra-bounded-detached-guard-2320z':
        raise Refused('production path differs from frozen reviewed profile')
    for path, expected in PINS.items():
        if digest(path) != expected:
            raise Refused('pinned source/executable changed: ' + path)
    if digest(PYTHON) != PINS[str(Path(PYTHON).with_name('python3.12'))]:
        raise Refused('python3 invocation symlink differs from the pinned executable')
    manifest = json.loads((PREVIOUS / 'PACKET-MANIFEST.json').read_text())
    helper = next(row['sha256'] for row in manifest['files'] if row['path'] == 'build_mathlib_serial.py')
    if digest(PREVIOUS / 'build_mathlib_serial.py') != helper:
        raise Refused('frozen external authenticator changed')
    if (STATE / 'PLAN.json').read_bytes() != (SUPPORT / 'EXTERNAL-PLAN.json').read_bytes():
        raise Refused('state plan differs from selected source plan')
    previous = json.loads((SUPPORT / 'evidence/ORCHESTRATOR-060.json').read_text())
    command = previous['batches'][0]['command'][:]
    if previous['batches'][0]['exit_code'] != 0 or command[-2:] != ['--batch', '1']:
        raise Refused('reference command is not the successful one-module profile')
    command[command.index('--out') + 1] = str(OUTPUT)
    delimiter = command.index('--')
    limits = dict(cpu_seconds=600, wall_seconds=900, address_space_bytes=6144 * 1024**2,
                  file_bytes=1024**3, disk_floor=8 * 1024**3, ram_floor=1024**3, cgroup_stop=4 * 1024**3)
    profile = dict(name='external062_one_fresh_v1', command=command,
                   child_command=command[delimiter + 1:], cwd=str(ROOT), batch_output=str(OUTPUT),
                   python_exe=str(Path(PYTHON).resolve()), guard_sha256=PINS[str(PREVIOUS / 'guard.py')],
                   limits=limits, source_pins=PINS, frozen_helpers_sha256=helper,
                   expected_start_index=EXPECTED_INDEX, fresh_budget=1,
                   launcher_sha256=digest(__file__),
                   environment={'PATH': '/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
                                'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'PYTHONDONTWRITEBYTECODE': '1'})
    spec = importlib.util.spec_from_file_location('frozen_capture_batch', SUPPORT / 'capture_batch.py')
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    if capture.LOADED_SHA != PINS[str(SUPPORT / 'capture_batch.py')]:
        raise Refused('loaded capture bytes differ')
    return profile, capture


def preflight():
    if (SUPPORT / 'PAUSE-BUILDS').exists():
        raise Refused('PAUSE-BUILDS is present')
    names = {'lean', 'lake', 'build_external_serial.py', 'build_support.py',
             'run_external_batches.py', 'run_external_batches_6g.py', 'run_provider_batches.py',
             'diagnose_module.py', 'diagnose_thread_failure.py', 'guard.py'}
    active = []
    for path in Path('/proc').iterdir():
        if not path.name.isdigit():
            continue
        try:
            state = (path / 'stat').read_text().rsplit(') ', 1)[1].split()[0]
            argv = (path / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
            if state not in ('Z', 'X') and any(Path(arg).name in names for arg in argv):
                active.append(dict(pid=int(path.name), argv=argv, state=state))
        except (FileNotFoundError, ProcessLookupError):
            continue
    if active:
        raise Refused('compiler/guard lane is not idle: ' + json.dumps(active))
    indices = sorted(int(path.stem) for path in STATE.glob('[0-9][0-9][0-9][0-9].json'))
    if indices != list(range(EXPECTED_INDEX)):
        raise Refused('receipt prefix differs from reserved starting index2992')
    # This is an index preflight, not a claim of full dependency authentication.
    # The pinned builder reauthenticates every source/log/object before compiling.
    if OUTPUT.exists():
        raise Refused('reserved output already exists')


def finish(profile, capture):
    terminal = read_receipt(profile, DIRECTORY)
    intent = json.loads((DIRECTORY / 'INTENT.json').read_text())
    before = DIRECTORY / 'PRE-BATCH-STATE.json'
    if digest(before) != intent['prebatch_sha256']:
        raise Refused('prelaunch inventory changed')
    target = OUTPUT / 'PRE-BATCH-STATE.json'
    if target.exists():
        if target.read_bytes() != before.read_bytes():
            raise Refused('existing capture preinventory differs')
    else:
        with target.open('xb') as stream:
            stream.write(before.read_bytes())
            stream.flush()
            import os
            os.fsync(stream.fileno())
    if terminal['guard_error'] or terminal['requested_stop']:
        # Frozen capture treats exit0/no-stop as successful even if a guard
        # exception occurred after child exit. Never rewrite that receipt to
        # force a branch. Preserve every changed indexed file as unverified.
        previous = json.loads(before.read_text())
        changed = {}
        for name, sha in capture.inventory(STATE).items():
            if previous.get(name) != sha:
                data = (STATE / name).read_bytes()
                changed[name] = dict(sha256=sha, bytes=len(data),
                                     exact_bytes_base64=base64.b64encode(data).decode())
        captured_path = DIRECTORY / 'INTERRUPTED-UNVERIFIED.json'
        checked = dict(schema='astra_guard_interruption_preservation_v1',
                       status='UNVERIFIED_CHANGED_BYTES_NO_COMPILER_COMPLETION_CLAIM',
                       guard_receipt_sha256=terminal['guard_receipt_sha256'],
                       prebatch_sha256=digest(before), changed=changed)
        write_new(captured_path, checked)
    else:
        checked = capture.capture(STATE, OUTPUT, check_existing=(OUTPUT / 'MODULE-RECEIPTS.json').exists())
        captured_path = OUTPUT / 'MODULE-RECEIPTS.json'
        actual = json.loads(captured_path.read_text())
        if (actual['capture_runner_sha256'] != PINS[str(SUPPORT / 'capture_batch.py')]
                or actual['prebatch_inventory_sha256'] != digest(before)):
            raise Refused('capture source/preinventory binding differs')
        completed = actual['completed_compiler_invocations']
        if terminal['status'] == 'GUARD_RECEIPT_SUCCESS':
            if len(completed) != 1 or completed[0]['index'] != EXPECTED_INDEX or completed[0]['receipt']['exit_code']:
                raise Refused('successful receipt did not complete the one reserved module')
    result = dict(schema='astra_one_guard_finish_v1', observed_utc=utc(), **terminal,
                  launch_sha256=digest(DIRECTORY / 'LAUNCH.json'),
                  prebatch_sha256=digest(before), capture=checked,
                  capture_sha256=digest(captured_path), capture_path=str(captured_path),
                  no_automatic_next_batch=True, compiler_objects_independently_reaudited=False)
    write_new(DIRECTORY / 'FINISH.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['launch', 'status', 'stop', 'finish'])
    action = parser.parse_args().action
    profile, capture = configured()
    if action == 'launch':
        preflight()
        result = launch(profile, DIRECTORY, capture.inventory(STATE), preflight)
    elif action == 'stop':
        result = stop(profile, DIRECTORY)
    elif action == 'status':
        result = status(profile, DIRECTORY)
    else:
        result = finish(profile, capture)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (Refused, OSError, ValueError, KeyError) as error:
        print(json.dumps(dict(status='REFUSED_OR_UNVERIFIED', error=type(error).__name__,
                              message=str(error), completion_verified=False)), file=sys.stderr)
        raise SystemExit(2)
