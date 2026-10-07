"""Bounded serial test execution with immutable attempt directories."""
from pathlib import Path
import argparse
import hashlib
import json
import resource
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))


parser = argparse.ArgumentParser()
parser.add_argument('attempt', choices=('attempt1', 'attempt2', 'attempt3'))
args = parser.parse_args()
out = BASE / args.attempt
out.mkdir(exist_ok=False)
names = ('joint_betting.py', 'test_joint_betting.py', 'run_controls.py', 'PROOF.md')
sources = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest() for name in names}
started = time.time()
try:
    result = subprocess.run([sys.executable, '-B', '-m', 'unittest', '-v', 'test_joint_betting'],
                            cwd=BASE, capture_output=True, timeout=10, preexec_fn=limits)
    stdout, stderr, code, timeout = result.stdout, result.stderr, result.returncode, False
except subprocess.TimeoutExpired as error:
    stdout, stderr, code, timeout = error.stdout or b'', error.stderr or b'', None, True
(out / 'stdout.log').write_bytes(stdout)
(out / 'stderr.log').write_bytes(stderr)
receipt = {'schema': 'bounded-deterministic-controls-receipt-v1',
           'attempt': args.attempt, 'started_unix': started, 'ended_unix': time.time(),
           'command': [sys.executable, '-B', '-m', 'unittest', '-v', 'test_joint_betting'],
           'exit_code': code, 'timeout': timeout,
           'cpu_seconds_cap': 5, 'wall_seconds_cap': 10, 'address_space_bytes_cap': 256 * 1024**2,
           'source_sha256': sources,
           'stdout_sha256': hashlib.sha256(stdout).hexdigest(),
           'stderr_sha256': hashlib.sha256(stderr).hexdigest(),
           'new_source_observations_generated': False,
           'simulation_or_inverse_run': False, 'lean_kernel_checked': False}
(out / 'RECEIPT.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(json.dumps(receipt, sort_keys=True))
sys.exit(0 if code == 0 and not timeout else 1)
