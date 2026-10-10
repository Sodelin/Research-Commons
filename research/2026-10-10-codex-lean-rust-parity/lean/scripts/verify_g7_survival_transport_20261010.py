#!/usr/bin/env python3
"""Post-run authentication of old aliases and newly compiled exact components.

Read-only. Source/core/native/kernel policies remain those of the frozen builder.
Partial-run cache objects establish component provenance, never root acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

from check_core import bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace', type=Path)
    parser.add_argument('--run', type=Path)
    args = parser.parse_args()
    work = args.workspace.resolve(strict=True)
    final = json.loads(((args.run / 'FINAL-RECEIPT.json') if args.run else work / '.build/LATEST-RUN.json').read_bytes())
    assert final['status'] == 'PASS_ALL_REQUESTED_TARGETS' and final['kernel_checking'] and final['trust_level'] == 0
    assert final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
    run = Path(final['run'])
    assert run.is_relative_to(work)
    prep = json.loads((work / 'PREPARATION.json').read_bytes())
    graph = json.loads((work / 'DEPENDENCY-GRAPH.json').read_bytes())
    assert sha(work / 'DEPENDENCY-GRAPH.json') == final['graph_sha256'] == prep['graph_sha256']
    for filename, key in [('build_connected.py', 'builder_sha256'), ('AuditTemplate.lean', 'audit_template_sha256'),
                          ('build_with_mathlib_overlay.py', 'namespace_overlay_wrapper_sha256'),
                          ('build_with_authenticated_overlay.py', 'optimized_overlay_sha256')]:
        assert sha(work / 'scripts' / filename) == prep[key]
    transport = json.loads((work / 'CACHE-TRANSPORT-PRE-USE-PLAN.json').read_bytes())
    seed = json.loads((work / 'CACHE-SEED-RECEIPT.json').read_bytes())
    assert sha(work / 'CACHE-TRANSPORT-PRE-USE-PLAN.json') == seed['pre_use_plan_sha256']
    aliases = json.loads((work / 'CACHE-INSTALL-ALIASES.json').read_bytes())
    derivation = json.loads((work / 'CACHE-INSTALL-TRANSPORT-DERIVATION.json').read_bytes())
    assert sha(work / 'CACHE-INSTALL-ALIASES.json') == derivation['alias_manifest_sha256']
    assert aliases['graph_sha256'] == final['graph_sha256']
    alias_by_module = {r['module']: r for r in aliases['entries']}
    proposed = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    original_staged_files = 0
    for entry in transport['entries']:
        for row in entry['files']:
            before, after = Path(row['source']), Path(row['destination'])
            assert sha(before) == sha(after) == row['sha256']
            assert before.stat().st_size == after.stat().st_size == row['bytes']
            original_staged_files += 1
    checked = {}
    def checked_bundle(path, expected):
        path = Path(path)
        if str(path) not in checked:
            checked[str(path)] = bundle(path)
        assert checked[str(path)] == expected
    installs = [json.loads(line) for line in (run / 'CACHE-INSTALL-TRANSPORT-CHECKS.jsonl').read_text().splitlines()]
    installed = {r['destination']: r for r in installs}
    assert len(installed) == len(installs)
    records = []
    installed_files = hardlinks = copies = 0
    for label in final['targets_passed']:
        target = graph['targets'][label]
        location = run / 'targets' / re.sub('[^A-Za-z0-9_-]', '_', label)
        result = json.loads((location / 'RESULT.json').read_bytes())
        assert result['status'] == 'PASS'
        components = {r['module']: r for r in result['component_receipts']}
        assert len(components) == len(result['component_receipts']) == len(target['modules'])
        assert set(components) == set(target['order'])
        for module in target['order']:
            rec = components[module]
            source_pin = target['modules'][module]['sha256']
            assert rec['source_sha256'] == source_pin == sha(work / 'source-store' / (source_pin + '.lean'))
            assert rec['source_and_imports_stable'] and rec['native_initialized_libraries_bound'] and rec['exit_code'] == 0
            assert all(f in rec['command'] for f in ['-j1', '-t0', '-Ddebug.skipKernelTC=false'])
            expected = rec['object_artifacts']
            original = Path(rec['cached_object'])
            staged = original
            receipt_path = original.parent / 'receipt.json'
            if module in alias_by_module:
                alias = alias_by_module[module]
                assert alias['source_sha256'] == source_pin and alias['object_artifacts'] == expected
                assert alias['original_cached_object'] == str(original)
                assert sha(Path(alias['original_receipt'])) == sha(Path(alias['staged_receipt'])) == alias['receipt_sha256']
                receipt_path = Path(alias['original_receipt'])
                staged = Path(alias['staged_cached_object'])
                provenance = 'VERIFIED_PRE_USE_ALIAS'
            else:
                assert module in proposed and original.is_relative_to(work / '.build/cache')
                provenance = 'CURRENT_CONTEXT_COMPONENT_CACHE_CREATED_BY_FROZEN_BUILDER'
            assert json.loads(receipt_path.read_bytes()) == rec
            checked_bundle(original, expected)
            checked_bundle(staged, expected)
            out = location / 'objects' / (module.replace('.', '/') + '.olean')
            checked_bundle(out, expected)
            install = installed[str(out)]
            assert install['original_object'] == str(original) and install['install_source'] == str(staged)
            assert install['object_artifacts'] == expected and install['original_and_staged_pre_post_checks_pass']
            for dep, binding in rec['direct_import_bindings'].items():
                checked_bundle(binding['path'], binding['artifacts'])
                if dep in components:
                    assert binding['artifacts'] == components[dep]['object_artifacts']
            for f in install['files']:
                a, b = Path(f['source']), Path(f['destination'])
                assert sha(a) == sha(b) == f['sha256'] and a.stat().st_size == b.stat().st_size == f['bytes']
                if f['transport'] == 'SAME_FILESYSTEM_HARD_LINK':
                    assert (a.stat().st_dev, a.stat().st_ino) == (b.stat().st_dev, b.stat().st_ino)
                    hardlinks += 1
                elif f['transport'] == 'EXDEV_HASH_CHECKED_COPY2':
                    copies += 1
                else:
                    assert f['transport'] == 'VERIFIED_EXISTING_DESTINATION'
                installed_files += 1
            records.append({'module': module, 'target': label, 'source_sha256': source_pin,
                            'original_receipt': str(receipt_path), 'original_receipt_sha256': sha(receipt_path),
                            'original_object': str(original), 'staged_object': str(staged), 'installed_object': str(out),
                            'object_artifacts': expected, 'component_provenance': provenance,
                            'original_staged_installed_and_import_bundles_rehashed': True})
    report = {'status': 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION', 'workspace': str(work),
              'run': str(run), 'graph_sha256': final['graph_sha256'], 'targets': final['targets_passed'],
              'final_receipt_sha256': sha(run / 'FINAL-RECEIPT.json'), 'verifier_sha256': sha(Path(__file__)),
              'original_staged_cache_files_rehashed': original_staged_files, 'selected_modules_verified': len(records),
              'installed_companion_files_rehashed': installed_files, 'installed_same_filesystem_hardlinks': hardlinks,
              'installed_exdev_copies': copies, 'unique_object_and_import_bundle_paths_rehashed': len(checked),
              'records': records, 'compiler_or_evaluator_invoked': False, 'accepted_inputs_modified': False,
              'root_acceptance_source': 'The actual fresh aggregate and complete owned audit, separately preserved.'}
    output = work / ('POST-RUN-TRANSPORT-REHASH-' + run.name + '.json')
    assert not output.exists()
    save(output, report)
    print(json.dumps({k: report[k] for k in ['status', 'selected_modules_verified', 'original_staged_cache_files_rehashed',
                                            'unique_object_and_import_bundle_paths_rehashed']}))


if __name__ == '__main__':
    main()
