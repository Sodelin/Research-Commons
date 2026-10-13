#!/usr/bin/env python3
"""Authenticate/export the exact four-base-proof Lake run; never compile.

Keeps source generation, finite native controls, actual Lean execution and
the still-uncompiled support wrappers separately scoped. Outputs are exclusive.
"""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / '2026-10-13-astra-unified-solver-0645z'
EMITTED = HERE.parent / '2026-10-13-astra-emitted-support-2110z'
PLAN_SHA = '262b1ed9846ee5684c29155baa5318dedebf0f0d082a10412fef124305075531'
MANIFEST_SHA = '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    require(sha(PREVIOUS / 'PACKET-MANIFEST.json') == MANIFEST_SHA, 'prior manifest changed')
    manifest = json.loads((PREVIOUS / 'PACKET-MANIFEST.json').read_text())
    pins = {row['path']: row['sha256'] for row in manifest['files']}
    for name in ['build_lean.py', 'build_mathlib_serial.py', 'guard.py', 'lakefile.lean']:
        require(sha(PREVIOUS / name) == pins[name], 'prior helper changed: ' + name)
    sys.path.insert(0, str(PREVIOUS))
    import build_lean
    plan_path = HERE / 'evidence/ADDITIVE-BASE-PROOF-PLAN.json'
    require(sha(plan_path) == PLAN_SHA, 'source/execution plan changed')
    plan = json.loads(plan_path.read_text())
    require(sha(EMITTED / 'PACKET-MANIFEST.json') == plan['emission_manifest_sha256'],
            'emission/native corpus manifest changed')
    emission = json.loads((EMITTED / 'PACKET-MANIFEST.json').read_text())
    for row in emission['files']:
        require(sha(EMITTED / row['path']) == row['sha256'], 'emission corpus changed')
    state = Path(plan['fresh_output'])
    guard_dir = HERE / 'evidence/lake-additive-base-v1'
    guard = json.loads((guard_dir / 'RECEIPT.json').read_text())
    require(guard['exit_code'] == 0 and guard['stop'] is None, 'Lake guard did not pass')
    require(guard['runner_sha256'] == pins['guard.py'] and guard['cwd'] == plan['cwd']
            and guard['command'] == plan['command'], 'Lake execution binding differs')
    expected_limits = dict(plan['guard'])
    require(guard['limits'] == expected_limits, 'guard limits differ')
    for name, row in guard['outputs'].items():
        require(sha(guard_dir / name) == row['sha256']
                and (guard_dir / name).stat().st_size == row['bytes'], 'guard log changed')
    result = json.loads((state / 'RESULT.json').read_text())
    compilation = json.loads((state / 'COMPILATION.json').read_text())
    require(result['compiled'] == compilation, 'result/compilation ledger differs')
    require(result['compiler_sha256'] == build_lean.LEAN_SHA, 'compiler identity differs')
    lean_bin = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')
    require(sha(lean_bin / 'lean') == build_lean.LEAN_SHA, 'actual compiler changed')
    require(sha(lean_bin / 'lake') == '60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3',
            'actual Lake changed')
    sources = [PREVIOUS / 'lean/Astra/CommonCertificateKernel.lean', PREVIOUS / 'lean/AstraKernel.lean']
    sources += [Path(row['source']) for row in plan['fresh_sources']]
    require(len(compilation) == len(sources) == 6, 'compiled selection differs')
    audits = {}
    copied = []
    for index, (row, source) in enumerate(zip(compilation, sources)):
        relative = source.relative_to(PREVIOUS / 'lean') if index < 2 else Path(source.name)
        source_root = PREVIOUS / 'lean' if index < 2 else source.parent
        target = state / 'lib/lean' / relative.with_suffix('.olean')
        expected_source = pins['lean/' + str(relative)] if index < 2 else plan['fresh_sources'][index - 2]['sha256']
        require(row['source'] == str(source) and row['source_sha256'] == expected_source
                and sha(source) == expected_source and sha(state / 'source' / relative) == expected_source,
                'compiled source identity differs')
        expected_command = [str(lean_bin / 'lean'), '-j', '1', '-s', '8192', '-R', str(source_root),
                            '-o', str(target), str(source)]
        require(row['command'] == expected_command and row['exit_code'] == 0,
                'compiler command/outcome differs')
        require(target.is_file() and target.stat().st_size > 0
                and row['artifacts'] == build_lean.artifacts(target), 'compiled objects changed')
        for suffix in ['stdout', 'stderr']:
            require(sha(state / f'{index}.{suffix}') == row[suffix + '_sha256'], 'compiler log changed')
            copied.append((state / f'{index}.{suffix}', Path('logs') / f'{index}.{suffix}'))
        audits.update(build_lean.audit((state / f'{index}.stdout').read_text()))
        copied.append((state / 'source' / relative, Path('sources') / relative))
    expected = {'Astra.CommonCertificateKernel.' + name for name in build_lean.EXPECTED_THEOREMS}
    expected.update(name for row in plan['fresh_sources'] for name in row['expected_axiom_heads'])
    require(set(audits) == expected and audits == result['axioms'] and len(audits) == 24,
            'actual full axiom audit differs')
    require(result['owned_axioms'] == 0 and result['placeholder_axioms'] == 0, 'placeholder claim differs')
    dependencies = result['external_execution']['modules']
    require(len(dependencies) == 916, 'external reuse selection differs')
    prior_state = Path('/workspace/scratch/astra-mathlib-serial-0705')
    require(sha(prior_state / 'PLAN.json') == result['external_execution']['plan_sha256'], 'external plan changed')
    for index, row in enumerate(dependencies):
        receipt_path = prior_state / f'{index:04d}.json'
        require(sha(receipt_path) == row['receipt_sha256'], 'external reuse receipt changed')
        receipt = json.loads(receipt_path.read_text())
        require(receipt['exit_code'] == 0 and receipt['source_sha256'] == row['source_sha256']
                and sha(Path(receipt['source'])) == row['source_sha256']
                and receipt['artifacts'] == row['artifacts'], 'external reuse source/artifact binding differs')
        for path, digest in row['artifacts'].items():
            require(sha(Path(path)) == digest, 'external reused object changed')
        for suffix in ['stdout', 'stderr']:
            require(sha(prior_state / f'{index:04d}.{suffix}') == receipt[suffix + '_sha256'],
                    'external historical log changed')
    output = guard_dir / 'authenticated-export'
    output.mkdir(exist_ok=False)
    copied += [(state / name, Path(name)) for name in ['RESULT.json', 'COMPILATION.json']]
    copied += [(plan_path, Path('PLAN.json')), (EMITTED / 'PACKET-MANIFEST.json', Path('EMISSION-MANIFEST.json'))]
    copied += [(PREVIOUS / name, Path('configuration') / name)
               for name in ['lakefile.lean', 'lean-toolchain', 'build_lean.py', 'build_mathlib_serial.py']]
    copied.append((Path(__file__), Path('configuration/capture_additive_base.py')))
    for source, relative in copied:
        destination = output / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as stream:
            stream.write(source.read_bytes())
        require(sha(destination) == sha(source), 'captured copy differs')
    summary = dict(status='FOUR_NEW_LITERAL_BASE_PROOFS_FRESHLY_COMPILED',
                   guard_sha256=sha(guard_dir / 'RECEIPT.json'), result_sha256=sha(state / 'RESULT.json'),
                   plan_sha256=PLAN_SHA, emission_manifest_sha256=plan['emission_manifest_sha256'],
                   source_execution_manifest_files=len(emission['files']), compiled=compilation,
                   actual_axioms=audits, fresh_kernel_and_aggregate=2, fresh_new_literal_proofs=4,
                   authenticated_external_reuse=916, earlier_three_literal_proofs='SEPARATE_AUTHENTICATED_REUSE',
                   seven_support_wrappers='UNCOMPILED', physical_representative=False,
                   universal_native_correctness=False, selected_provider_compiled=False,
                   original042_outer_guard='UNKNOWN', original057_outer_guard='UNKNOWN',
                   native_corpus='Earlier finite controls pinned by unchanged emission manifest; not rerun here.')
    (output / 'SUMMARY.json').write_text(json.dumps(summary, indent=2) + '\n')
    files = [dict(path=str(path.relative_to(output)), bytes=path.stat().st_size, sha256=sha(path))
             for path in sorted(output.rglob('*')) if path.is_file()]
    (output / 'FILES.json').write_text(json.dumps(dict(files=files, binaries_included=False), indent=2) + '\n')
    print(json.dumps(dict(status=summary['status'], files=len(files), audited_heads=len(audits),
                          summary_sha256=sha(output / 'SUMMARY.json'))))


if __name__ == '__main__':
    main()
