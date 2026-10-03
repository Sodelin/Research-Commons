#!/usr/bin/env python3
"""Verify recovered source/evidence bytes; never infer fresh Lean compilation."""
from pathlib import Path
import collections, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def git_digest(path):
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def main():
    manifest = read(ROOT / 'RECOVERY-MANIFEST.json')
    for row in manifest['entries']:
        path = ROOT / row['path']
        assert path.is_file() and len(path.read_bytes()) == row['bytes'], row['path']
        assert digest(path) == row['sha256'] and git_digest(path) == row['git_blob_sha'], row['path']
    original = read(ROOT / 'catalog/HISTORICAL-PROFILE-SOURCES.json')
    for row in original['rows']:
        path = ROOT / row['source_path']
        assert digest(path) == row['source_sha256'] and git_digest(path) == row['git_blob_sha'], row['module']
    archival = read(ROOT / 'catalog/RECOVERED-ORIGINAL-FORMAL-SOURCES.json')
    for row in archival['rows']:
        path = ROOT / row['path']
        assert digest(path) == row['source_sha256'] and git_digest(path) == row['git_blob_sha'], row['module']
    failed = ROOT / 'excluded-originals/main/GraphQuartetPortCounts/source.lean'
    untouched = ROOT / 'repair-v1/ORIGINAL.lean'
    repaired = ROOT / 'repair-v1/sources/GraphQuartetPortCounts.lean'
    assert failed.read_bytes() == untouched.read_bytes()
    assert digest(failed) == '56eb26a6abf08a69eb0e41187b02a8131096459f6707ab83898b1d7800a68fe0'
    assert digest(repaired) == '0832c80a5bcb28bbadbf7e0dbeccbb022dae6040d22c70cce7e7506eb1af6fb2'
    assert untouched.read_bytes().replace(b'namespace Nanuq.Source.RootedBinary\n',
           b'namespace Nanuq.Source.RootedBinary\n\nopen scoped Classical\n', 1) == repaired.read_bytes()
    failure_receipt = ROOT / 'excluded-originals/main/GraphQuartetPortCounts/receipt.json'
    failure_log = ROOT / 'excluded-originals/main/GraphQuartetPortCounts/compiler-failure.log'
    assert digest(failure_receipt) == 'e67180cef6117e37ba3596d78c6818db714991d0441d3a40d1768500d4cbbfe1'
    assert digest(failure_log) == '20f1b313d84c3f8a6e2bb1ac57fc53e8aa8e61a0b7b3809137812c074d105d75'
    r = read(failure_receipt)
    assert r['status'] == 'FAIL_COMPILER' and r['exit_code'] != 0 and r['raw_log_included']
    assert r['source_sha256'] == digest(failed) and r['log_sha256'] == digest(failure_log)
    report_checks = []
    for profile, declarations, theorems, expected in [
            ('main', 3696, 2360, '5281fe7b8decb214896767afaec035396b16a62729b3cc859ddb79013df3ae82'),
            ('pure-induction-v2', 439, 330, '256f9443499c8483732db6d0eb63ad75f978ba994eca69e87beb91eb3c832bf6')]:
        path = ROOT / 'profiles' / profile / 'all-declarations/declarations.json'
        assert digest(path) == expected
        data = read(path)
        assert data['declaration_count'] == len(data['declarations']) == declarations
        assert data['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in data['declarations']) == theorems
        assert not data['missing_modules'] and not data['nonstandard_axiom_rows']
        assert not any(r['kind'] == 'axiom' or set(r['axioms']) - STANDARD for r in data['declarations'])
        selected = sorted(r['module'] for r in original['rows'] if r['profile'] == profile and r['admitted_to_selected_profile'])
        assert sorted(data['selected_modules']) == selected
        report_checks.append({'profile': profile, 'declarations': declarations, 'theorems': theorems})
    print(json.dumps({'status': 'PASS_RECOVERED_BYTES_AND_PRESERVED_REPORT_INVENTORIES',
                      'manifest_files_checked_excluding_manifest': len(manifest['entries']),
                      'original_profile_source_hashes_checked': len(original['rows']),
                      'archival_formal_source_hashes_checked': len(archival['rows']),
                      'graph_repair_exact_bytes_checked': True,
                      'preserved_report_checks': report_checks,
                      'fresh_Lean_compilation_or_axiom_collection_executed': False,
                      'combined_build_or_master_completion_inferred': False}, indent=2))

if __name__ == '__main__':
    main()
