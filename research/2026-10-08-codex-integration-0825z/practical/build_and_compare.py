"""Execute bounded offline locked Cargo checks and exact signed-nine comparison."""
from pathlib import Path
import hashlib
import json
import os
import resource
import subprocess
import sys
import time

PACKET = Path(__file__).resolve().parent
SCRATCH = Path('/workspace/scratch/integration-practical')
RECOVERED = PACKET / 'recovered'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def state():
    manifest = json.loads((PACKET / 'RECOVERY.json').read_text())
    result = {}
    for original, row in manifest['files'].items():
        data = (PACKET / row['isolated_copy']).read_bytes()
        identity = {'sha256': sha(data), 'bytes': len(data)}
        if identity != {k: row[k] for k in identity}:
            raise RuntimeError('recovered source identity: ' + original)
        result[original] = identity
    return result


def invoke(name, args, cwd, environment, cpu=60, wall=90, memory=2*2**30):
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu))
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    start = time.monotonic()
    with (PACKET / 'logs' / (name + '.stdout')).open('xb') as out, (PACKET / 'logs' / (name + '.stderr')).open('xb') as err:
        process = subprocess.Popen(args, cwd=cwd, env=environment, stdout=out, stderr=err, preexec_fn=limits)
        timeout = False
        try:
            process.wait(timeout=wall)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            timeout = True
    result = {'command': args, 'cwd': str(cwd), 'exit_code': process.returncode, 'timeout': timeout,
              'wall_seconds': time.monotonic()-start, 'cpu_seconds_limit': cpu, 'wall_seconds_limit': wall,
              'address_space_bytes_limit': memory,
              'stdout_sha256': sha((PACKET/'logs'/(name+'.stdout')).read_bytes()),
              'stderr_sha256': sha((PACKET/'logs'/(name+'.stderr')).read_bytes())}
    (PACKET/'logs'/(name+'.execution.json')).write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    if process.returncode or timeout:
        raise RuntimeError(name + ': execution failed; exact first output preserved')
    return result


def main():
    before = state()
    (PACKET/'logs/BUILD-BEFORE.json').write_text(json.dumps(before, indent=2, sort_keys=True)+'\n')
    bin_dir = SCRATCH/'toolchain/bin'
    environment = dict(os.environ, CARGO_HOME=str(SCRATCH/'cargo-home'),
                       CARGO_TARGET_DIR=str(SCRATCH/'signed-target'), RUSTC=str(bin_dir/'rustc'),
                       RUSTDOC=str(bin_dir/'rustdoc'), CARGO_BUILD_JOBS='1',
                       PYTHONDONTWRITEBYTECODE='1', PYTHONNOUSERSITE='1', PYTHONHASHSEED='0')
    core = RECOVERED/'research/2026-10-08-cloud-rust-interval-root-0000z'
    probe = RECOVERED/'research/2026-10-08-cloud-rust-signed-probe-0122z'
    runs=[]
    runs.append(invoke('core-test', [str(bin_dir/'cargo'), 'test', '--offline', '--locked', '-j1'], core, environment))
    runs.append(invoke('signed-release', [str(bin_dir/'cargo'), 'build', '--offline', '--locked', '--release', '-j1'], probe, environment))
    binary=SCRATCH/'signed-target/release/signed-nine-probe'
    identity={'sha256':sha(binary.read_bytes()),'bytes':binary.stat().st_size}
    (PACKET/'logs/SIGNED-BINARY.json').write_text(json.dumps(identity,indent=2)+'\n')
    runs.append(invoke('signed-comparison', [sys.executable, '-B', str(probe/'compare_signed.py'), str(RECOVERED),
                       str(binary), str(PACKET/'signed-differential')], PACKET, environment,
                       cpu=60, wall=90, memory=512*2**20))
    after=state()
    (PACKET/'logs/BUILD-AFTER.json').write_text(json.dumps(after,indent=2,sort_keys=True)+'\n')
    if before!=after:
        raise RuntimeError('recovered source bytes changed')
    result={'schema':'integration_practical_locked_offline_signed_build_v1','status':'PASS',
            'commands':runs,'source_bytes_unchanged':True,'binary':identity,
            'provisioning_used_network':True,'cargo_commands_offline_locked':True,
            'rust_version':'1.90.0','frozen_historical_library_probe_comparator_unchanged':True}
    (PACKET/'logs/BUILD-RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','signed_comparator':str(PACKET/'signed-differential/RESULT.json')}))


if __name__=='__main__':
    main()
