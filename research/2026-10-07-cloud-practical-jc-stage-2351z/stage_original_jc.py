"""Authenticate immutable public dependencies; stage unchanged JC runtime once."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path, PurePosixPath

DEPENDENCIES = 'research/2026-10-07-dot-typed-jc-source-supplement-0803z/PUBLIC-DEPENDENCIES.json'
DEPENDENCIES_SHA = '126b6f4942f0ee7298a2e3383351ca8318cf27643e4fe5893022720f4364d995'
RUNTIME_PREFIX = 'practical-synthetic-continuation-20261007-0302z/runtime-layout/'
ENGINE_DIRECTORY = 'msci-ab-profile-implementation-20261005-1612z'
CHECKER_FILES = ('interval_math.py', 'base_contractors.py', 'interval_ad.py',
                 'joint_contractor.py', 'global_contractors.py', 'global_engine.py',
                 'global_check.py')
REQUEST = 'research/2026-10-05-dot-msci-original-domain-profile-localization-1621z/declared-requests/distinct.json'
REQUEST_SHA = 'a73fc025632555e058b8dc6f2c1440e6f625409caefd36ae56b660f0ba79cedb'
REQUEST_COMMIT = '52f22ffa9d3ca9b1fc67aa252b3fd3c5ce5c4490'
BUDGET = {'scalar_steps': 4, 'max_stages': 1, 'max_splits': 0, 'max_states': 1,
          'max_depth': 0, 'wall_ms': 3000, 'recovery_wall_ms': 3000,
          'recovery_max_stages': 1}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n').encode()


def safe_relative(value):
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(p in ('.', '..') for p in path.parts):
        raise ValueError('unsafe public relative path')
    return path


def archived(root, commit, path):
    return subprocess.check_output(['git', '-C', str(root), 'show', commit + ':' + path])


def stage(commons, runtime, receipt):
    commons, runtime, receipt = commons.resolve(), runtime.absolute(), receipt.absolute()
    if runtime.exists() or runtime.is_symlink():
        raise ValueError('refuse existing runtime; preserve every failed/earlier stage')
    if receipt.exists() or receipt.is_symlink():
        raise ValueError('refuse existing staging receipt')
    raw = (commons / DEPENDENCIES).read_bytes()
    if sha(raw) != DEPENDENCIES_SHA:
        raise ValueError('dependency manifest identity')
    manifest = json.loads(raw)
    if manifest['schema'] != 'public_scientific_dependency_layout_v1' or len(manifest['files']) != 32:
        raise ValueError('dependency manifest schema/count')
    authenticated, selected = [], []
    for row in manifest['files']:
        if row['repository'] != 'Sodelin/Research-Commons':
            raise ValueError('unexpected dependency repository')
        source = safe_relative(row['public_path'])
        current_path = commons / str(source)
        if current_path.is_symlink():
            raise ValueError('source symlink')
        current = current_path.read_bytes()
        frozen = archived(commons, row['commit'], row['public_path'])
        blob = subprocess.check_output(['git', '-C', str(commons), 'rev-parse',
                                       row['commit'] + ':' + row['public_path']], text=True).strip()
        if current != frozen or sha(frozen) != row['sha256'] or len(frozen) != row['bytes'] or blob != row['git_blob']:
            raise ValueError('source/commit/blob/SHA/length mismatch: ' + row['public_path'])
        authenticated.append({k: row[k] for k in ('public_path', 'commit', 'git_blob', 'sha256', 'bytes', 'destination')})
        if row['destination'].startswith(RUNTIME_PREFIX):
            relative = safe_relative(row['destination'][len(RUNTIME_PREFIX):])
            selected.append((relative, frozen, row))
    if len(selected) != 9 or len({str(p) for p, _, _ in selected}) != 9:
        raise ValueError('exact nine-file numerical runtime selection')
    original = archived(commons, REQUEST_COMMIT, REQUEST)
    if sha(original) != REQUEST_SHA or original != (commons / REQUEST).read_bytes():
        raise ValueError('archived arithmetic request identity')
    request = json.loads(original)
    expected_domain = {key: (['1/32', '1/8'] if key in ('h', 'u', 'v') else
                            ['1/6', '2/3'] if key == 'g' else ['1/2', '6'])
                       for key in ('h', 'u', 'v', 'rA', 'rB', 'rC', 'rAB', 'rR', 'g')}
    if request['box'] != expected_domain or any(x != '1/20' for x in request['normalized_width_targets'].values()):
        raise ValueError('original D/target mismatch')
    request['budget'] = dict(BUDGET)
    request['provenance'].update(cloud_control='one_root_stage_clean_unchanged_runtime',
                                 inherited_arithmetic_request_sha256=REQUEST_SHA,
                                 fresh_biological_data=False, statistical_coverage_claimed=False)
    runtime.mkdir(parents=True, exist_ok=False)
    staged = []
    for relative, body, row in selected:
        target = runtime / str(relative); target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(body)
        target.chmod(0o444)
        if target.read_bytes() != body:
            raise ValueError('destination readback mismatch')
        staged.append({'runtime_relative': str(relative), 'destination': str(target),
                       'public_path': row['public_path'], 'sha256': row['sha256'],
                       'bytes': row['bytes'], 'unchanged': True})
    pins = {name: sha((runtime / ENGINE_DIRECTORY / name).read_bytes()) for name in CHECKER_FILES}
    request_raw, pins_raw = canonical(request), canonical(pins)
    for name, body in [('REQUEST.json', request_raw), ('CHECKER-PINS.json', pins_raw)]:
        with (runtime / name).open('xb') as out:
            out.write(body)
        (runtime / name).chmod(0o444)
    result = {'schema': 'cloud_original_jc_staging_v1', 'dependency_manifest': DEPENDENCIES,
              'dependency_manifest_sha256': DEPENDENCIES_SHA, 'authenticated_public_sources': authenticated,
              'all32_current_and_committed_blobs_identical': True, 'runtime_root': str(runtime),
              'selected_unchanged_runtime_files': staged, 'engine_directory': ENGINE_DIRECTORY,
              'request_sha256': sha(request_raw), 'checker_pins_sha256': sha(pins_raw),
              'original_arithmetic_request_sha256': REQUEST_SHA, 'request_budget': BUDGET,
              'original_full_domain_and_targets_preserved': True,
              'mean_inputs': 'unchanged archived deterministic arithmetic intervals, not observations',
              'fresh_biological_data': False, 'statistical_coverage_claimed': False,
              'bytecode_files_present': [str(f) for f in runtime.rglob('*.pyc')]}
    with receipt.open('x') as out:
        json.dump(result, out, indent=2, sort_keys=True); out.write('\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--commons-root', type=Path, required=True)
    parser.add_argument('--runtime-root', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    result = stage(args.commons_root, args.runtime_root, args.receipt)
    print(json.dumps({'status': 'STAGED_UNCHANGED', 'files': len(result['selected_unchanged_runtime_files']),
                      'request_sha256': result['request_sha256'], 'runtime_root': result['runtime_root']}, sort_keys=True))
