"""One external-budgeted original-D root refinement and separate full checker."""
import argparse
import hashlib
import json
import os
import resource
import subprocess
import sys
import time
from pathlib import Path


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))


def command(attempt, name, args):
    start = time.monotonic()
    environment = {'PATH': os.defpath, 'LANG': 'C.UTF-8', 'PYTHONNOUSERSITE': '1',
                   'PYTHONDONTWRITEBYTECODE': '1', 'PYTHONHASHSEED': '0'}
    with (attempt / (name + '.stdout')).open('x') as out, (attempt / (name + '.stderr')).open('x') as err:
        process = subprocess.Popen(args, stdout=out, stderr=err, env=environment, preexec_fn=limits)
        failure = None
        try:
            process.wait(timeout=20)
        except subprocess.TimeoutExpired:
            process.kill(); process.wait(); failure = 'EXTERNAL_WALL_LIMIT'
    result = {'name': name, 'command': args, 'exit': process.returncode,
              'wall_seconds': time.monotonic() - start, 'external_failure': failure,
              'cpu_seconds_limit': 10, 'wall_seconds_limit': 20,
              'address_space_bytes_limit': 256 * 1024**2,
              'stdout_sha256': sha((attempt / (name + '.stdout')).read_bytes()),
              'stderr_sha256': sha((attempt / (name + '.stderr')).read_bytes()),
              'stderr_empty': (attempt / (name + '.stderr')).stat().st_size == 0}
    (attempt / (name + '-EXECUTION.json')).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if process.returncode or failure:
        raise RuntimeError(name + ' failed; exact first output/metadata preserved')
    return result


def authenticate_runtime(staging, runtime):
    for row in staging['selected_unchanged_runtime_files']:
        path = runtime / row['runtime_relative']
        if path.is_symlink() or sha(path.read_bytes()) != row['sha256']:
            raise ValueError('staged source changed: ' + str(path))
    if list(runtime.rglob('*.pyc')):
        raise ValueError('unexpected runtime bytecode cache')


def execute(commons, runtime, attempt):
    commons, runtime, attempt = commons.resolve(), runtime.absolute(), attempt.absolute()
    attempt.mkdir(parents=True, exist_ok=False)
    packet = Path(__file__).resolve().parent
    freeze = subprocess.check_output(['git', '-C', str(commons), 'rev-parse', 'HEAD'], text=True).strip()
    scripts = {name: sha((packet / name).read_bytes()) for name in ('stage_original_jc.py', 'execute_smoke.py')}
    records = [command(attempt, 'stage', [sys.executable, '-B', str(packet / 'stage_original_jc.py'),
                       '--commons-root', str(commons), '--runtime-root', str(runtime),
                       '--receipt', str(attempt / 'STAGING.json')])]
    staging = json.loads((attempt / 'STAGING.json').read_text())
    authenticate_runtime(staging, runtime)
    for name in ('REQUEST.json', 'CHECKER-PINS.json'):
        (attempt / name).write_bytes((runtime / name).read_bytes())
    request, pins = runtime / 'REQUEST.json', runtime / 'CHECKER-PINS.json'
    engine = runtime / staging['engine_directory']
    journal = attempt / 'journal'
    common = ['--request', str(request), '--request-sha256', staging['request_sha256'],
              '--checkpoints', str(journal)]
    records.append(command(attempt, 'producer', [sys.executable, '-B', str(engine / 'global_engine.py'), *common]))
    authenticate_runtime(staging, runtime)
    records.append(command(attempt, 'checker', [sys.executable, '-B', str(engine / 'global_check.py'),
                   *common, '--source-pins', str(pins), '--source-pins-sha256', staging['checker_pins_sha256'], '--normal']))
    authenticate_runtime(staging, runtime)
    producer = json.loads((attempt / 'producer.stdout').read_text())
    checker = json.loads((attempt / 'checker.stdout').read_text())
    frames = sorted(journal.glob('state-*.json'))
    identities = [{'path': str(f.relative_to(attempt)), 'sha256': sha(f.read_bytes()), 'bytes': f.stat().st_size}
                  for f in frames]
    result = {'schema': 'cloud_original_jc_one_stage_result_v1', 'source_freeze': freeze,
              'new_script_sha256': scripts, 'executions': records,
              'staged_runtime_pre_interprocess_and_post_hashes_match': True,
              'runtime_bytecode_cache_absent': True, 'complete_new_journal': identities,
              'producer': producer, 'checker': checker,
              'original_full_domain': True, 'new_biological_data': False,
              'observed_confidence_admitted': False, 'parameter_accuracy_released': False,
              'scope': 'one supplied arithmetic root-stage assembly and separate full numerical checker'}
    # This control requires complete checker processing; retain actual outputs
    # before reporting a failure of this assembly expectation.
    (attempt / 'RESULT.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    if not checker['details'].get('complete_numeric_replay'):
        raise RuntimeError('control did not complete journal replay; result retained UNKNOWN')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--commons-root', type=Path, required=True)
    parser.add_argument('--runtime-root', type=Path, required=True)
    parser.add_argument('--attempt', type=Path, required=True)
    args = parser.parse_args()
    result = execute(args.commons_root, args.runtime_root, args.attempt)
    print(json.dumps({'status': result['checker']['status'], 'stages': result['producer']['stages_started'],
                      'complete_numeric_replay': result['checker']['details']['complete_numeric_replay'],
                      'journal_frames': len(result['complete_new_journal']),
                      'whole_union_width_target_met': result['checker']['whole_union_width_target_met'],
                      'statistical_coverage_verified': result['checker']['statistical_coverage_verified']}, sort_keys=True))
