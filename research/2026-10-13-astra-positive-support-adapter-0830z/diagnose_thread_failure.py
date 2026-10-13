#!/usr/bin/env python3
"""One exact failed invocation, shared compiler controls, read-only /proc samples.

The outer guard selects the explicitly recorded diagnostic limits. This runner
does not change limits, sources, the failed receipt, or the shared helper. It
never adopts successful objects into the external receipt ledger automatically.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import threading
import time

import build_external_serial as external
import serial_compile

HERE = Path(__file__).resolve().parent
INDEX = 2860
FAILED_SHA = '05d682973501c3af2a74bd4d6b8b3015741d7ca32d58cbcb258b273992dd456d'
HELPER_SHA = 'd47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28'
EXTERNAL_SHA = '00c9c98b2490f8bd35c9ea644aba78171d3bddbfc8735a30b2a855c55285df8f'


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ['state', 'mathlib-root', 'lean-bin', 'out']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    for name in ['state', 'mathlib_root', 'lean_bin', 'out']:
        setattr(args, name, getattr(args, name).resolve())
    if (args.state / 'PLAN.json').read_bytes() != (HERE / 'EXTERNAL-PLAN.json').read_bytes():
        raise ValueError('exact external selection changed')
    if (external.sha(HERE / 'serial_compile.py') != HELPER_SHA
            or serial_compile.LOADED_SHA != HELPER_SHA):
        raise ValueError('reviewed shared helper changed')
    if external.LOADED_SHA != EXTERNAL_SHA or external.sha(HERE / 'build_external_serial.py') != EXTERNAL_SHA:
        raise ValueError('reviewed external authenticator changed')
    failed_path = args.state / f'{INDEX:04d}.json'
    if external.sha(failed_path) != FAILED_SHA:
        raise ValueError('original failed receipt differs')
    failed = json.loads(failed_path.read_text())
    plan = json.loads((args.state / 'PLAN.json').read_text())
    row = plan['modules'][INDEX]
    _, dependencies, env = external.setup(args.mathlib_root, args.lean_bin)
    if (plan['compiler_sha256'] != external.LEAN_SHA or plan['mathlib_pin'] != external.PIN
            or plan['dependencies'] != dependencies
            or external.sha(args.mathlib_root / 'lakefile.lean') != external.MATHLIB_LAKEFILE_SHA):
        raise ValueError('compiler, dependencies or Mathlib options changed')
    if any(failed[key] != value for key, value in row.items()):
        raise ValueError('failed source/import selection differs')
    if external.sha(Path(row['source'])) != row['source_sha256']:
        raise ValueError('selected source differs')
    for suffix in ['stdout', 'stderr']:
        if external.sha(args.state / f'{INDEX:04d}.{suffix}') != failed[suffix + '_sha256']:
            raise ValueError('original failed log changed')
    target = Path(row['target'])
    if external.artifacts(target):
        raise ValueError('preserve existing target artifacts before diagnostic')
    inputs = serial_compile.toolchain_inputs(args.lean_bin)
    ledger = []
    for index, selected in enumerate(plan['modules'][:INDEX]):
        path = args.state / f'{index:04d}.json'
        receipt = json.loads(path.read_text())
        if receipt['exit_code'] or any(receipt[key] != value for key, value in selected.items()):
            raise ValueError('earlier receipt selection differs')
        if external.sha(Path(selected['source'])) != selected['source_sha256']:
            raise ValueError('earlier source changed')
        objects = external.artifacts(Path(selected['target']))
        if str(Path(selected['target'])) not in objects or objects != receipt['artifacts']:
            raise ValueError('earlier artifact identity differs')
        for suffix in ['stdout', 'stderr']:
            if external.sha(args.state / f'{index:04d}.{suffix}') != receipt[suffix + '_sha256']:
                raise ValueError('earlier compiler log changed')
        inputs.update(objects)
        ledger.append(dict(index=index, receipt_sha256=external.sha(path)))
    command = [str(args.lean_bin / 'lean'), *external.MATHLIB_OPTIONS,
               '-j', '1', '-s', '8192', '-R', row['repo'], '-o', str(target), row['source']]
    if command != failed['command']:
        raise ValueError('compiler command differs from original failed invocation')
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / 'source.lean').write_bytes(Path(row['source']).read_bytes())
    save(args.out / 'AUTHENTICATED-PREFIX.json', ledger)
    save(args.out / 'CACHE-INPUTS.json', sorted(inputs))
    base = dict(selected=row, command=command, compiler_sha256=external.LEAN_SHA,
                runner_sha256=external.sha(Path(__file__)), helper_sha256=HELPER_SHA,
                external_runner_sha256=EXTERNAL_SHA,
                external_plan_sha256=external.sha(HERE / 'EXTERNAL-PLAN.json'),
                mathlib_lakefile_sha256=external.MATHLIB_LAKEFILE_SHA,
                failed_receipt_sha256=FAILED_SHA,
                authenticated_prefix_sha256=external.sha(args.out / 'AUTHENTICATED-PREFIX.json'),
                environment={key: env[key] for key in ['LEAN_PATH', 'LEAN_SRC_PATH',
                    'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB', 'LEAN_IMPORT_WORKERS',
                    'MIMALLOC_ARENA_RESERVE', 'RAYON_NUM_THREADS', 'LEAN_MAIN_USE_THREAD',
                    'GLIBC_TUNABLES', 'MIMALLOC_VERBOSE'] if key in env},
                helper_child_environment={'MALLOC_ARENA_MAX': '1'},
                runner_limits={name: resource.getrlimit(getattr(resource, name)) for name in
                               ['RLIMIT_AS', 'RLIMIT_CPU', 'RLIMIT_STACK', 'RLIMIT_NPROC', 'RLIMIT_FSIZE']},
                original_receipt_unchanged=True, automatic_adoption=False,
                cgroup_events_before=Path('/sys/fs/cgroup/memory.events').read_text())
    save(args.out / 'INVOCATION.json', base)
    done = threading.Event()
    errors = []
    sample_count = [0]
    parent = os.getpid()
    started = time.monotonic()

    def monitor():
        try:
            peak = 0
            saved = 0
            with (args.out / 'process-samples.jsonl').open('x') as stream:
                while not done.is_set():
                    children = (Path('/proc') / str(parent) / 'task' / str(parent) / 'children').read_text().split()
                    for number in children:
                        directory = Path('/proc') / number
                        try:
                            status_text = (directory / 'status').read_text()
                            status = dict(line.split(':', 1) for line in status_text.splitlines() if ':' in line)
                            command_line = (directory / 'cmdline').read_bytes().split(b'\0')
                            if (status['PPid'].strip() != str(parent)
                                    or command_line[0] != str(args.lean_bin / 'lean').encode()):
                                continue
                            sample = dict(seconds=time.monotonic() - started, pid=int(number),
                                          cgroup_bytes=int(Path('/sys/fs/cgroup/memory.current').read_text()),
                                          threads=int(status['Threads']))
                            for key in ['VmPeak', 'VmSize', 'VmRSS', 'VmHWM']:
                                if key in status:
                                    sample[key + '_bytes'] = int(status[key].split()[0]) * 1024
                            size = sample.get('VmSize_bytes', 0)
                            if saved == 0 or size > peak + 128 * 1024**2:
                                snapshot = args.out / f'process-{saved:03d}'
                                snapshot.mkdir()
                                for name in ['status', 'limits', 'maps', 'smaps_rollup']:
                                    try:
                                        (snapshot / name).write_text((directory / name).read_text())
                                    except OSError as error:
                                        (snapshot / (name + '.error')).write_text(repr(error) + '\n')
                                calls = []
                                for task in (directory / 'task').iterdir():
                                    try:
                                        calls.append(dict(tid=task.name, syscall=(task / 'syscall').read_text()))
                                    except OSError as error:
                                        calls.append(dict(tid=task.name, error=repr(error)))
                                save(snapshot / 'thread-syscalls.json', calls)
                                sample['snapshot'] = snapshot.name
                                peak = max(size, peak)
                                saved += 1
                            stream.write(json.dumps(sample) + '\n')
                            stream.flush()
                            sample_count[0] += 1
                        except (FileNotFoundError, ProcessLookupError):
                            pass
                    done.wait(0.05)
        except BaseException as error:
            errors.append(dict(type=type(error).__name__, message=str(error)))

    thread = threading.Thread(target=monitor, daemon=True)
    thread.start()
    try:
        code, controls = serial_compile.compile_one(command, cwd=row['repo'], env=env,
            stdout=args.out / 'stdout', stderr=args.out / 'stderr', input_files=inputs,
            target=target, index=INDEX, module=row['module'])
    finally:
        done.set()
        thread.join(timeout=2)
    if thread.is_alive():
        errors.append(dict(type='MonitorJoinTimeout', message='monitor did not terminate within two seconds'))
    if sample_count[0] == 0 or not any(args.out.glob('process-*/limits')):
        errors.append(dict(type='MissingChildObservation', message='no actual child sample and limits snapshot'))
    if not code and (not target.is_file() or target.stat().st_size == 0):
        errors.append(dict(type='MissingPrimaryArtifact', message='compiler returned zero without a nonempty target'))
    if external.sha(Path(row['source'])) != row['source_sha256']:
        errors.append(dict(type='SourceChanged', message='selected source changed during diagnostic'))
    result = dict(base, compiler_exit_code=code, exit_code=code if code else (2 if errors else 0),
                  seconds=time.monotonic() - started, resource_control=controls,
                  monitor_errors=errors, monitor_samples=sample_count[0], artifacts=external.artifacts(target),
                  stdout_sha256=external.sha(args.out / 'stdout'),
                  stderr_sha256=external.sha(args.out / 'stderr'),
                  cgroup_events_after=Path('/sys/fs/cgroup/memory.events').read_text())
    if external.sha(failed_path) != FAILED_SHA:
        raise ValueError('original failed receipt was unexpectedly changed')
    save(args.out / 'RESULT.json', result)
    print(json.dumps(dict(status='SINGLE_MODULE_DIAGNOSTIC', exit_code=result['exit_code'],
                          compiler_exit_code=code, module=row['module'], seconds=result['seconds'],
                          sampled_peaks=controls['sampled_peaks'])), flush=True)
    raise SystemExit(result['exit_code'])


if __name__ == '__main__':
    main()
