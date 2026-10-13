"""Internal process transport; production CLI supplies its fixed authenticated profile.

This module is not an arbitrary-command command-line interface. Tests exercise
the same transport with separately identified stdlib-only dummy commands.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

LOADED_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


class Refused(RuntimeError):
    pass


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_new(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())


def boot_id():
    return Path('/proc/sys/kernel/random/boot_id').read_text().strip()


def identity(pid):
    """Read identity twice; a vanished or changing /proc entry is not authority."""
    base = Path('/proc') / str(pid)
    first = (base / 'stat').read_text().rsplit(') ', 1)[1].split()
    result = dict(pid=pid, starttime_ticks=int(first[19]), state=first[0],
                  session=int(first[3]), process_group=int(first[2]),
                  exe=os.readlink(base / 'exe'),
                  argv=(base / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0'))
    second = (base / 'stat').read_text().rsplit(') ', 1)[1].split()
    if first[19] != second[19]:
        raise Refused('process identity changed during observation')
    return result


def same_identity(actual, expected):
    return all(actual[k] == expected[k] for k in
               ('pid', 'starttime_ticks', 'exe', 'argv', 'session', 'process_group'))


def monitor_sleep(pid):
    """Only the pinned guard's post-Popen monitor sleep is accepted as ready.

stdout/stderr already exist while Popen is starting. In that window its child
may exist before guard.child is assigned. Sending SIGINT there could bypass
the frozen guard's child cleanup. Its sole time.sleep(0.5) is after assignment,
and the guard never creates a second child after reaching that monitor loop.
Kernel/procfs platforms that cannot expose this exact wait channel are refused.
"""
    channel = (Path('/proc') / str(pid) / 'wchan').read_text().strip()
    if channel != 'hrtimer_nanosleep':
        raise Refused('guard has not been observed in its post-Popen monitor sleep: ' + channel)
    return dict(wchan=channel, observed_utc=utc(),
                meaning='pinned guard reached monitor after assigning its only child')


def alive(record):
    if boot_id() != record['boot_id']:
        raise Refused('boot identity differs; no environment-replacement authority')
    try:
        current = identity(record['identity']['pid'])
    except FileNotFoundError:
        return False
    if not same_identity(current, record['identity']):
        raise Refused('recorded PID now has a different identity; no completion inference')
    return current['state'] not in ('Z', 'X')


def _load(profile, directory):
    directory = Path(directory)
    intent = json.loads((directory / 'INTENT.json').read_text())
    record = json.loads((directory / 'LAUNCH.json').read_text())
    if (intent['profile'] != profile or record['intent_sha256'] != digest(directory / 'INTENT.json')
            or record['transport_sha256'] != LOADED_SHA
            or digest(__file__) != LOADED_SHA
            or record['identity']['argv'] != profile['command']
            or record['identity']['exe'] != profile['python_exe']
            or record['identity']['session'] != record['identity']['pid']
            or record['identity']['process_group'] != record['identity']['pid']):
        raise Refused('launch record does not bind the supplied fixed profile')
    return record


def launch(profile, directory, before, last_preflight=lambda: None):
    """Launch ONE guard, never a detached orchestrator. Caller owns compiler slot."""
    if not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
        raise Refused('Linux pidfd stop support is required before launch')
    if signal.getsignal(signal.SIGINT) == signal.SIG_IGN:
        raise Refused('inherited ignored SIGINT would disable guard cleanup')
    if Path(profile['batch_output']).exists():
        raise Refused('guard output must not already exist')
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    write_new(directory / 'PRE-BATCH-STATE.json', before)
    write_new(directory / 'INTENT.json', dict(schema='astra_one_guard_intent_v1',
              created_utc=utc(), profile=profile, transport_sha256=LOADED_SHA,
              prebatch_sha256=digest(directory / 'PRE-BATCH-STATE.json'),
              launch_is_completion=False))
    # No live child exists before the exclusive intent and preinventory persist.
    last_preflight()
    with (directory / 'guard.stdout').open('xb') as out, (directory / 'guard.stderr').open('xb') as err:
        child = subprocess.Popen(profile['command'], cwd=profile['cwd'], stdin=subprocess.DEVNULL,
                                 stdout=out, stderr=err, start_new_session=True, close_fds=True,
                                 env=profile['environment'])
    # Popen has returned after exec; regular files survive this bootstrap's exit.
    # A crash before LAUNCH.json leaves an intent-only UNKNOWN outcome, not
    # permission to signal a guessed PID. No automatic recovery/relaunch exists.
    observed = identity(child.pid)
    if (observed['argv'] != profile['command'] or observed['exe'] != profile['python_exe']
            or observed['session'] != child.pid or observed['process_group'] != child.pid):
        raise Refused('spawned process identity differs; retain intent and inspect manually')
    record = dict(schema='astra_one_guard_launch_v1', observed_utc=utc(), boot_id=boot_id(),
                  identity=observed, intent_sha256=digest(directory / 'INTENT.json'),
                  transport_sha256=LOADED_SHA, status='LAUNCHED_OUTCOME_UNKNOWN',
                  guard_process_exit_code=None, launch_is_completion=False)
    write_new(directory / 'LAUNCH.json', record)
    return record


def status(profile, directory):
    record = _load(profile, directory)
    return dict(status='RUNNING' if alive(record) else 'ORIGINAL_PROCESS_NOT_RUNNING',
                actual_receipt_present=(Path(profile['batch_output']) / 'RECEIPT.json').exists(),
                completion_verified=False, guard_process_exit_code=None)


def stop(profile, directory):
    """One pidfd SIGINT to the exact live guard; no PID/PGID signalling fallback."""
    record = _load(profile, directory)
    if boot_id() != record['boot_id']:
        raise Refused('boot identity differs')
    if not hasattr(os, 'pidfd_open') or not hasattr(signal, 'pidfd_send_signal'):
        raise Refused('pidfd signalling unsupported')
    batch = Path(profile['batch_output'])
    if not all((batch / name).is_file() for name in ('stdout', 'stderr')):
        raise Refused('guard has not entered its output/cleanup region; retry read-only status')
    fd = os.pidfd_open(record['identity']['pid'])
    try:
        current = identity(record['identity']['pid'])
        if current['state'] in ('Z', 'X') or not same_identity(current, record['identity']):
            raise Refused('stale or differing guard identity')
        ready = monitor_sleep(current['pid'])
        current = identity(current['pid'])
        if current['state'] in ('Z', 'X') or not same_identity(current, record['identity']):
            raise Refused('guard identity changed after monitor readiness observation')
        signal.pidfd_send_signal(fd, 0)
        request = dict(schema='astra_pidfd_stop_request_v1', requested_utc=utc(),
                       launch_sha256=digest(Path(directory) / 'LAUNCH.json'), identity=current,
                       signal='SIGINT', readiness=ready,
                       receipt_outcome='UNKNOWN_UNTIL_FINISH')
        write_new(Path(directory) / 'STOP-REQUEST.json', request)
        signal.pidfd_send_signal(fd, signal.SIGINT)
        write_new(Path(directory) / 'STOP-SENT.json', dict(sent_utc=utc(), signal='SIGINT',
                  request_sha256=digest(Path(directory) / 'STOP-REQUEST.json'),
                  completion_verified=False))
    finally:
        os.close(fd)
    return dict(status='SIGINT_SENT_COMPLETION_UNKNOWN')


def read_receipt(profile, directory):
    """Authenticate actual receipt after original guard is no longer executing."""
    record = _load(profile, directory)
    if alive(record):
        raise Refused('guard remains active; no terminal capture')
    batch = Path(profile['batch_output'])
    receipt = json.loads((batch / 'RECEIPT.json').read_text())
    if (receipt['runner_sha256'] != profile['guard_sha256']
            or receipt['command'] != profile['child_command']
            or receipt['cwd'] != profile['cwd'] or receipt['limits'] != profile['limits']):
        raise Refused('actual guard receipt differs from fixed command/source/limits')
    for name in ('stdout', 'stderr'):
        output = batch / name
        if receipt['outputs'][name] != dict(bytes=output.stat().st_size, sha256=digest(output)):
            raise Refused('actual guard output hash differs')
    # The guard's receipt records its builder's return code, not its own exit.
    # An exception after builder exit0 still cannot become a successful receipt.
    requested_stop = (Path(directory) / 'STOP-REQUEST.json').exists()
    successful = (receipt['exit_code'] == 0 and receipt['stop'] is None
                  and not receipt.get('error') and not requested_stop)
    return dict(status='GUARD_RECEIPT_SUCCESS' if successful else 'GUARD_RECEIPT_NOT_SUCCESS',
                guard_process_exit_code=None, builder_exit_code=receipt['exit_code'],
                guard_error=receipt.get('error'), guard_stop=receipt['stop'],
                requested_stop=requested_stop,
                guard_receipt_sha256=digest(batch / 'RECEIPT.json'),
                guard_log_pins={name: dict(bytes=(Path(directory) / name).stat().st_size,
                                        sha256=digest(Path(directory) / name))
                                for name in ('guard.stdout', 'guard.stderr')})
