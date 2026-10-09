#!/usr/bin/env python3
"""Capture independent replay commands, hashes, output and bounded failures."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent / 'replays'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--label', required=True)
    p.add_argument('--source', action='append', default=[])
    p.add_argument('--timeout', type=int, default=60)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    command = a.command[1:] if a.command[:1] == ['--'] else a.command
    if not command or not a.label.replace('-', '').isalnum():
        p.error('A command and simple unique label are required')
    OUT.mkdir(exist_ok=True)
    paths = [ROOT / value for value in a.source]
    hashes = {str(path.relative_to(ROOT)): sha(path) for path in paths}
    start = time.monotonic()
    timed = False
    try:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=a.timeout)
        stdout, stderr, code = result.stdout, result.stderr, result.returncode
    except subprocess.TimeoutExpired as error:
        stdout, stderr, code, timed = error.stdout or b'', error.stderr or b'', None, True
    for suffix, raw in [('stdout', stdout), ('stderr', stderr)]:
        with (OUT / (a.label + '.' + suffix)).open('xb') as stream:
            stream.write(raw)
    receipt = {'reviewer': 'Codex independent validation lane', 'evidence_tier': 'INDEPENDENT_REPLAY',
               'command': command, 'working_directory': str(ROOT), 'source_hashes': hashes,
               'sources_unchanged': all(sha(path) == hashes[str(path.relative_to(ROOT))] for path in paths),
               'timeout_seconds': a.timeout, 'timeout': timed, 'exit_code': code,
               'wall_seconds': time.monotonic() - start,
               'stdout_sha256': hashlib.sha256(stdout).hexdigest(), 'stderr_sha256': hashlib.sha256(stderr).hexdigest()}
    with (OUT / (a.label + '.json')).open('x') as stream:
        json.dump(receipt, stream, indent=2); stream.write('\n')
    print(json.dumps({'label': a.label, 'exit_code': code, 'timeout': timed, 'sources_unchanged': receipt['sources_unchanged']}))
    return 0 if code == 0 and not timed and receipt['sources_unchanged'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
