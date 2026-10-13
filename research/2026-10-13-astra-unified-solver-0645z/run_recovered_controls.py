#!/usr/bin/env python3
"""Fresh serial decoder/history controls against the authenticated rebuilt core.

Run under guard.py after restore_parity.py and the locked/offline single-job
core build. Restored sources are reauthenticated before and after execution.
No old executable or rlib is imported from a historical receipt.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--restored', type=Path, required=True)
    parser.add_argument('--target', type=Path, required=True)
    parser.add_argument('--rustc', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--binaries', type=Path, required=True)
    args = parser.parse_args()
    source_manifest = args.restored/'RESTORED-SOURCES.json'
    manifest = json.loads(source_manifest.read_bytes())

    def authenticate():
        for row in manifest['files']:
            path = args.restored/row['path']
            if path.stat().st_size != row['bytes'] or sha(path) != row['sha256']:
                raise ValueError('recovered source changed: '+row['path'])

    authenticate()
    dependencies = args.target/'debug/deps'
    libraries = {}
    for name in ['parity_solver', 'num_bigint', 'num_integer', 'num_traits']:
        matches = list(dependencies.glob('lib'+name+'-*.rlib'))
        if len(matches) != 1:
            raise ValueError('exactly one freshly built library required: '+name)
        libraries[name] = matches[0]
    binaries = args.binaries
    binaries.mkdir(exist_ok=False)
    args.out.mkdir(parents=True, exist_ok=False)
    results = []

    def step(name, command, timeout):
        started = time.monotonic()
        result = subprocess.run(command, capture_output=True, timeout=timeout)
        (args.out/(name+'.stdout')).write_bytes(result.stdout)
        (args.out/(name+'.stderr')).write_bytes(result.stderr)
        row = dict(name=name, command=command, exit_code=result.returncode,
                   elapsed_seconds=time.monotonic()-started,
                   stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
                   stderr_sha256=hashlib.sha256(result.stderr).hexdigest())
        results.append(row)
        (args.out/'STEPS.json').write_text(json.dumps(results, indent=2)+'\n')
        if result.returncode:
            raise ValueError('preserved failed execution: '+name)
        return result.stdout.decode()

    controls = [('native_snapshot_decode_tests', 3), ('serial_early_late_history_tests', 1)]
    for name, count in controls:
        source = args.restored/'controls'/(name+'.rs')
        output = binaries/name
        command = [str(args.rustc), '--edition=2024', '--test', str(source),
                   '--crate-name', name, '-C', 'debuginfo=0', '-C', 'opt-level=0',
                   '-C', 'linker=/usr/bin/cc', '-L', 'dependency='+str(dependencies)]
        for lib, path in libraries.items():
            command += ['--extern', lib+'='+str(path)]
        command += ['-o', str(output)]
        step(name+'-compile', command, 45)
        text = step(name+'-tests', [str(output), '--test-threads=1', '--nocapture'], 45)
        if not re.search(r'(?m)^running '+str(count)+(' test$' if count == 1 else ' tests$'), text):
            raise ValueError('unexpected number of tests: '+name)
        if f'test result: ok. {count} passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;' not in text:
            raise ValueError('missing passing exact test summary: '+name)
        results[-1].update(tests_passed=count, binary_sha256=sha(output))
    authenticate()
    report = dict(schema='fresh_recovered_decoder_history_controls_v1',
                  status='PASS_FINITE_NATIVE_CONTROLS', steps=results,
                  restored_manifest_sha256=sha(source_manifest),
                  source_files_authenticated=len(manifest['files']),
                  library_sha256={name: sha(path) for name, path in libraries.items()},
                  rustc_sha256=sha(args.rustc),
                  all_components_freshly_compiled=True, historical_binaries_reused=False,
                  generic_source_admission_proved=False, native_refinement_proved=False,
                  literal_unique_history_claimed=False)
    (args.out/'RESULT.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'steps'}, sort_keys=True))


if __name__ == '__main__':
    main()
