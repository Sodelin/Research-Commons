"""Bounded runner for this new local exact check."""
import datetime
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

folder = Path('g3-semialgebraic-source-certificates-20261006-2156z/instantiation')
argv = ['python', str(folder/'instantiate.py')]
def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
    resource.setrlimit(resource.RLIMIT_AS, (512*1024*1024, 512*1024*1024))

start = datetime.datetime.now(datetime.timezone.utc).isoformat()
tic = time.perf_counter()
timed_out = False
with (folder/'stdout.txt').open('wb') as out, (folder/'stderr.txt').open('wb') as err:
    try:
        process = subprocess.run(argv, stdout=out, stderr=err, timeout=30, preexec_fn=limits)
        code = process.returncode
    except subprocess.TimeoutExpired:
        timed_out = True
        code = None
end = datetime.datetime.now(datetime.timezone.utc).isoformat()
record = {
    'argv': argv, 'working_directory': 'task workspace root',
    'cpu_seconds': 20, 'wall_seconds': 30, 'address_space_bytes': 512*1024*1024,
    'started_utc': start, 'ended_utc': end, 'elapsed_seconds': time.perf_counter()-tic,
    'exit_code': code, 'timed_out': timed_out,
    'stdout_sha256': hashlib.sha256((folder/'stdout.txt').read_bytes()).hexdigest(),
    'stderr_sha256': hashlib.sha256((folder/'stderr.txt').read_bytes()).hexdigest(),
    'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
(folder/'execution.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps(record))
print((folder/'stdout.txt').read_text())
if code != 0:
    print((folder/'stderr.txt').read_text())
