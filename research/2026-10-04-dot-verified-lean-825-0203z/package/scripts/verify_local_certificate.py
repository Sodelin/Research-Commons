#!/usr/bin/env python3
"""Verify the complete local source/evidence packet without replaying proofs.

Add --objects in the pinned environment to check actual compiled bindings too.
This does not establish public delivery or unresolved mathematical masters.
"""
from pathlib import Path
import argparse, collections, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--objects', action='store_true')
    args = parser.parse_args()
    manifest = read(ROOT / 'LOCAL-SOURCE-EVIDENCE-MANIFEST.json')
    expected = {r['path'] for r in manifest['files']}
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*')
              if p.is_file() and not any(x in {'.build', '.lake', '__pycache__'}
                                        for x in p.relative_to(ROOT).parts)
              and p.name != 'LOCAL-SOURCE-EVIDENCE-MANIFEST.json'}
    assert expected == actual, ('file inventory differs', expected - actual, actual - expected)
    for row in manifest['files']:
        p = ROOT / row['path']
        b = p.read_bytes()
        assert len(b) == row['bytes'] and digest(p) == row['sha256'], row['path']
        assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == row['git_blob_sha1']
    registry = read(ROOT / 'catalog/SOURCE-REGISTRY.json')
    records = registry['records']
    assert len(records) == registry['active_source_record_count'] == manifest['active_source_records'] == 825
    bindings = read(ROOT / 'certificate/SOURCE-OBJECT-RECEIPT-BINDINGS.json')
    assert bindings['count'] == len(bindings['records']) == 825
    rows = {(x['profile'], x['module']): x for x in bindings['records']}
    assert len(rows) == 825
    for source in records:
        row = rows[source['profile'], source['module']]
        assert row['source'] == source['source']
        assert digest(ROOT / row['source']) == row['source_sha256'] == source['source_sha256']
        receipt_path = ROOT / 'certificate/components' / row['profile'] / Path(*row['module'].split('.')).with_suffix('.json')
        receipt = read(receipt_path)
        assert digest(receipt_path) == row['receipt_sha256']
        assert receipt['status'].startswith('PASS') and receipt['exit_code'] == 0
        assert receipt['source_sha256'] == row['source_sha256']
        assert receipt['object_sha256'] == row['object_sha256']
        assert receipt['direct_import_sha256'] == row['direct_import_sha256']
        assert receipt['source_and_direct_imports_stable']
        # Guarded fair-source compiles bind bytes/imports; their complete axiom
        # evidence is the profile audit below rather than selected print lines.
        if 'nonstandard_selected_axioms' in receipt:
            assert not receipt['nonstandard_selected_axioms']
        if 'compiler_commit' in receipt:
            assert receipt['compiler_commit'] == registry['compiler_commit']
        else:
            assert registry['compiler_commit'] in receipt['compiler'] and '4.33.1' in receipt['compiler']
        if 'mathlib_commit' in receipt:
            assert receipt['mathlib_commit'] == registry['mathlib_commit']
        assert receipt['compiler_binary_sha256'] == manifest['compiler_binary_sha256']
    audits = read(ROOT / 'certificate/AUDIT-SUMMARY.json')
    profiles = ['base', 'fair-g5-v1', 'fair-g5-normalization-v1', 'fair-g5-sharpness-v1', 'g1-contextual-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-normalization-v1', 'g1-temporal-v1', 'g1-interface-v1', 'g1-calendar-v1', 'g1-unranked-k-v1', 'g1-completion-v1', 'g1-compact-v1', 'main', 'pure-induction-v2']
    assert {(x['profile'], x['kind']) for x in audits} == {(p, k) for p in profiles for k in ['axioms', 'dependencies']}
    for row in audits:
        folder = ROOT / 'certificate' / (row['profile'] + '-' + row['kind'])
        receipt = read(folder / 'receipt.json')
        report = read(folder / 'declarations.json')
        assert digest(folder / 'receipt.json') == row['receipt_sha256']
        assert digest(folder / 'declarations.json') == row['report_sha256'] == receipt['report_sha256']
        assert receipt['status'].startswith('PASS') and receipt['exit_code'] == 0
        assert receipt['source_and_direct_imports_stable']
        assert len(report['declarations']) == row['declarations'] == receipt['declaration_count']
        assert len({x['name'] for x in report['declarations']}) == row['declarations']
        if row['kind'] == 'axioms':
            assert not report['missing_modules'] and not report['nonstandard_axiom_rows']
            assert not any(x['kind'] == 'axiom' or set(x['axioms']) - STANDARD for x in report['declarations'])
    import_maps = {}
    for profile in profiles:
        inventory = read(ROOT / 'certificate' / ('TRANSITIVE-' + profile + '.json'))
        assert inventory['exit_code'] == 0 and not inventory['missing_modules']
        assert inventory['selected_objects_stable'] and inventory['artifact_hashes_stable']
        assert inventory['artifact_count'] == len(inventory['artifact_rows'])
        assert inventory['imported_module_entries'] == len({x['module'] for x in inventory['artifact_rows']})
        assert inventory['compiler_commit'] == registry['compiler_commit']
        assert inventory['mathlib_commit'] == registry['mathlib_commit']
        import_maps[profile] = {x['module']: x['sha256'] for x in inventory['artifact_rows']
                               if x['path'].endswith('.olean')}
    for row in bindings['records']:
        profile = row['profile'] if row['profile'] in import_maps else 'main'
        assert all(import_maps[profile].get(m) == h for m, h in row['direct_import_sha256'].items()), (row['profile'], row['module'])
    terminal = read(ROOT / 'certificate/G1-CANONICAL21-LAKE-TEST-TERMINAL-RECEIPT.json')
    assert terminal['command'] == ['lake', 'test'] and terminal['exit_code'] == 0
    assert terminal['active_source_records'] == 825
    assert terminal['source_config_hashes_stable_before_after']
    assert terminal['stdout_sha256'] == digest(ROOT / 'certificate/G1-CANONICAL21-LAKE-TEST.stdout')
    assert terminal['registry_sha256'] == digest(ROOT / 'catalog/SOURCE-REGISTRY.json')
    assert terminal['builder_sha256'] == digest(ROOT / 'scripts/build_profiles.py')
    assert terminal['source_config_sha256']['lakefile.lean'] == digest(ROOT / 'lakefile.lean')
    stdout = (ROOT / 'certificate/G1-CANONICAL21-LAKE-TEST.stdout').read_text()
    reused = {x.removeprefix('REUSE_MATCHING_VERIFIED_ARTIFACT ') for x in stdout.splitlines()
              if x.startswith('REUSE_MATCHING_VERIFIED_ARTIFACT ')}
    assert reused == {x['profile'] + ':' + x['module'] for x in records}
    assert stdout.count('PASS_FRESH_COMPONENT') == 16
    assert stdout.count('PASS_AXIOMS_AUDIT') == stdout.count('PASS_DEPENDENCIES_AUDIT') == 16
    if args.objects:
        from build_profiles import Builder
        builder = Builder()
        assert all(builder.reusable(row) for row in builder.registry)
    print(json.dumps({'status': 'PASS_COMPLETE_LOCAL_SOURCE_EVIDENCE_PACKET',
                      'files': len(expected) + 1, 'active_source_records': 825,
                      'complete_audits': len(audits), 'actual_compiled_bindings_checked': args.objects,
                      'profile_counts': dict(collections.Counter(x['profile'] for x in records)),
                      'public_delivery_or_master_completion_inferred': False}))

if __name__ == '__main__':
    main()
