#!/usr/bin/env python3
"""Hash the actual Lake setup's transitive artifacts for one matching snapshot."""
from pathlib import Path
import fcntl, hashlib, json, subprocess, sys
from toolchain import binary_dir

ROOT = Path(__file__).resolve().parents[1]
version = sys.argv[1]
snapshot = ROOT / 'snapshots' / version
freeze = json.loads((snapshot / 'FREEZE.json').read_text())

def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            result.update(chunk)
    return result.hexdigest()

with (ROOT / '.build.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    assert all(digest(ROOT / path) == value
               for path, value in freeze['source_and_config_sha256'].items())
    assert all(digest(ROOT / '.lake/build/lib/lean' /
                      Path(*name.split('.')).with_suffix('.olean')) == value
               for name, value in freeze['artifact_sha256'].items())
    setup = ROOT / '.lake/build/ir/UnifiedLean.setup.json'
    setup_hash = digest(setup)
    data = json.loads(setup.read_text())
    rows = []
    missing = []
    for module, groups in sorted(data['importArts'].items()):
        for group_index, group in enumerate(groups):
            for artifact in group:
                path = Path(artifact)
                if not path.is_absolute():
                    path = ROOT / path
                if not path.is_file():
                    missing.append(str(path))
                else:
                    rows.append({'module': module, 'artifact_group': group_index,
                                 'evidence_path': str(path), 'sha256': digest(path),
                                 'bytes': path.stat().st_size})
    assert not missing, missing
    assert digest(setup) == setup_hash, 'Lake setup changed during hash collection'
    tool = binary_dir()
    mathlib_commit = subprocess.check_output(
        ['git', '-C', str(ROOT / 'deps/mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
    assert mathlib_commit == '0df444a360eaa60ab8c11dca51a86af692955474'
    result = {'version': version, 'selected_modules': freeze['modules'],
              'frozen_snapshot': str(snapshot.relative_to(ROOT)),
              'setup_sha256': setup_hash, 'setup_stable': True,
              'imported_module_entries': len(data['importArts']),
              'artifact_count': len(rows), 'missing_artifacts': missing,
              'mathlib_checkout_commit': mathlib_commit,
              'compiler_binary_sha256': digest(tool / 'lean'),
              'lake_binary_sha256': digest(tool / 'lake'),
              'absolute_paths_are_machine_specific_evidence_not_portable_requirements': True,
              'artifact_rows': rows}
    destination = ROOT / 'catalog' / (str(freeze['modules']) + '-TRANSITIVE-IMPORT-ARTIFACTS.json')
    assert not destination.exists(), 'Existing certificate is preserved; choose a new version file'
    destination.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'path': str(destination.relative_to(ROOT)),
                      'sha256': digest(destination),
                      'imported_module_entries': result['imported_module_entries'],
                      'artifact_count': len(rows), 'missing_artifacts': missing}))
