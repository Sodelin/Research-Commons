"""Cloud locked/offline rebuild; keeps every transferred historical byte intact."""
import argparse
import datetime
import hashlib
import json
import os
import resource
import subprocess
import sys
import time
import tomllib
from pathlib import Path

TOOLCHAIN = Path('/workspace/cloud-practical-runtime/rustup/toolchains/1.90.0-x86_64-unknown-linux-gnu/bin')
CARGO_HOME = Path('/workspace/cloud-practical-runtime/cargo')
RUSTUP_HOME = Path('/workspace/cloud-practical-runtime/rustup')
EXPECTED_COMMIT = '1159e78c4747b02ef996e55082b704c09b970588'
EXPECTED_CORPUS = '5d70e84d9912694e959e44df44d18d1c7b4afa8caad62f462d19309016580783'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def authenticate(pilot, transfer):
    for row in transfer['files']:
        raw = (pilot / row['path']).read_bytes()
        if len(raw) != row['bytes'] or sha(raw) != row['sha256']:
            raise ValueError('transferred historical file changed: ' + row['path'])


def build_limits():
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))


def build_command(attempt, name, command, pilot, environment):
    start = time.monotonic()
    with (attempt / (name + '.stdout')).open('x') as out, (attempt / (name + '.stderr')).open('x') as err:
        process = subprocess.Popen(command, cwd=pilot, env=environment,
                                   stdout=out, stderr=err, preexec_fn=build_limits)
        failure = None
        try:
            process.wait(timeout=45)
        except subprocess.TimeoutExpired:
            process.kill(); process.wait(); failure = 'EXTERNAL_WALL_LIMIT'
    result = {'name': name, 'command': command, 'exit': process.returncode,
              'wall_seconds': time.monotonic() - start, 'external_failure': failure,
              'cpu_seconds_limit': 30, 'wall_seconds_limit': 45,
              'address_space_bytes_limit': 2 * 1024**3,
              'stdout_sha256': sha((attempt / (name + '.stdout')).read_bytes()),
              'stderr_sha256': sha((attempt / (name + '.stderr')).read_bytes())}
    (attempt / (name + '-EXECUTION.json')).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if process.returncode or failure:
        raise RuntimeError(name + ' failed; first output/receipt preserved')
    return result


def corpus_replay(binary, pilot):
    raw = (pilot / 'evidence/corpus.jsonl').read_bytes()
    if sha(raw) != EXPECTED_CORPUS:
        raise ValueError('frozen historical corpus identity')
    cases = [json.loads(line) for line in raw.decode().splitlines()]
    if len(cases) != 1693:
        raise ValueError('corpus length')
    start = time.monotonic()
    for index, case in enumerate(cases):
        args = [str(binary), case['a'], case['epsilon']]
        if case['max_steps'] is not None:
            args += ['--max-steps', str(case['max_steps'])]
        if case['weights']:
            args += ['--weights']
        run = subprocess.run(args, capture_output=True, timeout=3)
        expected = (json.dumps(case['expected'], sort_keys=True) + '\n').encode()
        if run.returncode or run.stderr or run.stdout != expected:
            raise AssertionError({'first_failed_case': index, 'arguments': args[1:],
                                  'exit': run.returncode, 'stderr': run.stderr.decode(errors='replace')})
    invalid = [[], ['1'], ['1', '1/2', 'extra'], ['-1', '1/2'], ['0', '0'], ['0', '1'], ['0', '2'],
               ['nan', '1/2'], ['1/0', '1/2'], ['--unknown'], ['1', '1/2', '--max-steps'],
               ['1', '1/2', '--max-steps', '-1'], ['1', '1/2', '--max-steps', '1.0'],
               ['1', '1/2', '--weights', '--weights'], ['1', '1/2', '--max-steps=1', '--max-steps=2'],
               ['1e4097', '1/2'], ['1e-4097', '1/2'], ['1_000', '1/2'], ['١', '1/2'],
               ['1'*4097, '1/2'], ['1 / 2', '1/2'], ['1', '1/2', '--max-steps', '-0']]
    for args in invalid:
        run = subprocess.run([str(binary), *args], capture_output=True, timeout=3)
        if run.returncode != 2 or run.stdout or not run.stderr:
            raise AssertionError('invalid CLI control failed')
    run = subprocess.run([os.fsencode(binary), b'\xff', b'1/2'], capture_output=True, timeout=3)
    assert run.returncode == 2 and not run.stdout and run.stderr
    for a in ('1e4096', '1e-4096', '1'*4096):
        run = subprocess.run([str(binary), a, '1/2', '--max-steps', '0'], capture_output=True, timeout=3)
        assert run.returncode == 0 and not run.stderr and json.loads(run.stdout)['status'] == 'RESOURCE_LIMIT'
    run = subprocess.run([str(binary), '0', '1/2', '--max-steps', '1'+'0'*100], capture_output=True, timeout=3)
    assert run.returncode == 0 and not run.stderr and json.loads(run.stdout)['K'] == 0
    return {'status': 'PASS', 'saved_complete_byte_exact_cases': len(cases),
            'invalid_cli_cases': len(invalid), 'additional_boundaries': 5,
            'corpus_sha256': EXPECTED_CORPUS, 'wall_seconds': time.monotonic() - start,
            'scope': 'new Cloud executable compared with immutable Dot golden corpus; no new universal theorem or benchmark'}


def rebuild(root, attempt, target):
    packet = Path(__file__).resolve().parent
    transfer = json.loads((packet / 'TRANSFER.json').read_text())
    pilot = root / transfer['prefix']
    if target.exists():
        raise ValueError('fresh target required')
    attempt.mkdir(parents=True, exist_ok=False)
    authenticate(pilot, transfer)
    environment = {'PATH': str(TOOLCHAIN) + os.pathsep + os.defpath,
                   'CARGO_HOME': str(CARGO_HOME), 'RUSTUP_HOME': str(RUSTUP_HOME),
                   'CARGO_TARGET_DIR': str(target), 'RUSTC': str(TOOLCHAIN / 'rustc'),
                   'RUSTFLAGS': '', 'CARGO_NET_OFFLINE': 'true', 'LANG': 'C.UTF-8'}
    rustc = subprocess.check_output([str(TOOLCHAIN / 'rustc'), '--version', '--verbose'], env=environment).decode()
    cargo = subprocess.check_output([str(TOOLCHAIN / 'cargo'), '--version'], env=environment).decode()
    if EXPECTED_COMMIT not in rustc:
        raise ValueError('pinned compiler commit')
    (attempt / 'rustc-version.txt').write_text(rustc)
    (attempt / 'cargo-version.txt').write_text(cargo)
    lock = tomllib.loads((pilot / 'Cargo.lock').read_text())
    cache = []
    for package in lock['package']:
        if 'checksum' not in package:
            continue
        matches = list((CARGO_HOME / 'registry/cache').glob('*/' + package['name'] + '-' + package['version'] + '.crate'))
        if len(matches) != 1 or sha(matches[0].read_bytes()) != package['checksum']:
            raise ValueError('pinned cached crate missing/mismatched: ' + package['name'])
        cache.append({'name': package['name'], 'version': package['version'], 'checksum': package['checksum']})
    (attempt / 'CACHE.json').write_text(json.dumps(cache, indent=2, sort_keys=True) + '\n')
    cargo_path = str(TOOLCHAIN / 'cargo')
    records = [build_command(attempt, 'unit_tests', [cargo_path, 'test', '--offline', '--locked',
                             '--all-targets', '-j', '1'], pilot, environment),
               build_command(attempt, 'release_build', [cargo_path, 'build', '--offline', '--locked',
                             '--release', '-j', '1'], pilot, environment)]
    binary = target / 'release/count-certificate'
    # Separate bounded corpus worker keeps the producer, original evidence and
    #test runner bytes unchanged. It receives no toolchain or network action.
    def replay_limits():
        resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
        resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
    with (attempt / 'replay.stdout').open('x') as out, (attempt / 'replay.stderr').open('x') as err:
        run = subprocess.run([sys.executable, '-B', str(packet / 'rebuild_native.py'), '--replay',
                              '--pilot', str(pilot), '--binary', str(binary)], stdout=out, stderr=err,
                             timeout=30, preexec_fn=replay_limits)
    if run.returncode:
        raise RuntimeError('corpus replay failed; first output preserved')
    replay = json.loads((attempt / 'replay.stdout').read_text())
    authenticate(pilot, transfer)
    test_text = (attempt / 'unit_tests.stdout').read_text()
    if '10 passed; 0 failed' not in test_text:
        raise ValueError('expected ten actual unit tests not observed')
    original = json.loads((pilot / 'evidence/root-rebuild/REBUILD-RECEIPT.json').read_text())
    result = {'schema': 'cloud_dot_native_rust_rebuild_v1',
              'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'publisher_executor': 'Codex Cloud practical lane',
              'source_publication_commit': 'd3b0821f33a1144ff1c50478fdaa8289e890abcd',
              'script_sha256': sha(Path(__file__).read_bytes()), 'toolchain_rustc': rustc.strip(),
              'toolchain_cargo': cargo.strip(), 'cached_pinned_dependencies': cache,
              'mode': 'actual --offline --locked; fresh isolated target; -j1; no installation',
              'executions': records, 'unit_tests_passed': 10, 'replay': replay,
              'all34_transferred_payloads_unchanged_before_after': True,
              'binary_sha256': sha(binary.read_bytes()), 'binary_bytes': binary.stat().st_size,
              'matches_reported_dot_root_binary': sha(binary.read_bytes()) == original['binary_sha256'],
              'binary_published': False, 'benchmark_run': False,
              'limits': ['Linux x86_64/Rust1.90 only; Rust1.74 minimum not tested',
                         'finite golden comparison, not universal equivalence or formal executable proof',
                         'no full solver/statistical confidence/production/license gate closure']}
    (attempt / 'RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--commons-root', type=Path)
    parser.add_argument('--attempt', type=Path)
    parser.add_argument('--target', type=Path)
    parser.add_argument('--replay', action='store_true')
    parser.add_argument('--pilot', type=Path)
    parser.add_argument('--binary', type=Path)
    args = parser.parse_args()
    if args.replay:
        print(json.dumps(corpus_replay(args.binary, args.pilot), indent=2, sort_keys=True))
    else:
        result = rebuild(args.commons_root.resolve(), args.attempt.absolute(), args.target.absolute())
        print(json.dumps({'status': 'CLOUD_REBUILD_PASS', 'unit_tests': result['unit_tests_passed'],
                          'corpus_cases': result['replay']['saved_complete_byte_exact_cases'],
                          'invalid_cli_cases': result['replay']['invalid_cli_cases'],
                          'binary_sha256': result['binary_sha256'],
                          'matches_dot_binary': result['matches_reported_dot_root_binary']}, sort_keys=True))
