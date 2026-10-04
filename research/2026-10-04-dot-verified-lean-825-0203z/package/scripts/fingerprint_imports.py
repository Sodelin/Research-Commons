#!/usr/bin/env python3
"""Fingerprint resolved transitive artifacts of each actual compiled profile."""
from pathlib import Path
import argparse, datetime, json, os, subprocess, time
from build_profiles import Builder, ROOT, OUT, digest, save, COMPILER, MATHLIB, AUDITED_PROFILES, AGGREGATE_NAMES

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('profile', choices=AUDITED_PROFILES)
    args = parser.parse_args()
    b = Builder()
    profile = args.profile
    aggregate = AGGREGATE_NAMES[profile]
    destination = OUT / 'receipts' / profile / ('transitive-imports-' + str(time.time_ns()))
    destination.mkdir(parents=True)
    source = destination / 'ImportInventory.lean'
    source.write_text('import ' + aggregate + '\nimport Lean.Elab.Command\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let names := env.header.moduleNames.map Name.toString\n  liftIO <| IO.FS.writeFile "modules.json" (toJson names).pretty\n')
    before_source = digest(source)
    before_objects = {str(p): digest(p) for root in b.paths(profile)[:len(b.paths(profile)) - len(b.external)]
                      for p in root.rglob('*.olean')}
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join(str(p) for p in b.paths(profile))
    env['LEAN_NUM_THREADS'] = '1'
    command = ['timeout', '180', str(b.bin / 'lean'), '-j1', '-M6144', source.name]
    start = time.monotonic()
    with (destination / 'build.log').open('w') as log:
        result = subprocess.run(command, cwd=destination, env=env, stdout=log, stderr=subprocess.STDOUT)
    assert result.returncode == 0, (destination / 'build.log').read_text()
    modules = json.loads((destination / 'modules.json').read_bytes())
    roots = b.paths(profile) + [b.bin.parent / 'lib/lean']
    rows = []
    missing = []
    for module in sorted(set(modules)):
        rel = Path(*module.split('.')).with_suffix('.olean')
        path = next((r / rel for r in roots if (r / rel).is_file()), None)
        if path is None:
            missing.append(module)
            continue
        # Main/private/server are the exact format used by this pinned Lean.
        # IR companions are recorded when present, rather than inferred missing.
        artifacts = [path, Path(str(path) + '.private'), Path(str(path) + '.server'),
                     path.with_suffix('.ir'), path.with_suffix('.ir.sig')]
        for artifact in artifacts:
            if artifact.is_file():
                rows.append({'module': module, 'path': str(artifact),
                             'sha256': digest(artifact), 'bytes': artifact.stat().st_size})
    assert not missing, missing
    assert before_source == digest(source)
    assert all(digest(Path(p)) == sha for p, sha in before_objects.items())
    assert all(digest(Path(row['path'])) == row['sha256'] for row in rows)
    report = {'status': 'PASS_ACTUAL_TRANSITIVE_IMPORT_ARTIFACT_FINGERPRINTS',
              'profile': profile, 'aggregate': aggregate,
              'source_sha256': before_source, 'exit_code': result.returncode,
              'elapsed_seconds': time.monotonic() - start,
              'compiler_commit': COMPILER, 'compiler_binary_sha256': b.compiler_binary_sha256,
              'mathlib_commit': MATHLIB, 'imported_module_entries': len(set(modules)),
              'artifact_count': len(rows), 'missing_modules': missing,
              'selected_objects_stable': True, 'artifact_hashes_stable': True,
              'inspector_dependency_superset_explicit': ['Lean.Elab.Command'],
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'artifact_rows': rows, 'full_master_completion_inferred': False}
    save(destination / 'receipt.json', report)
    save(OUT / ('TRANSITIVE-' + profile + '.json'), report)
    print(json.dumps({k: report[k] for k in ['status', 'profile', 'imported_module_entries',
                                          'artifact_count', 'missing_modules']}, indent=2))

if __name__ == '__main__':
    main()
