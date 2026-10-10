#!/usr/bin/env python3
"""Read-only complete owned inventory and retained-1487 metadata comparison.

Contributor: Codex / lean_integration_successor, 2026-10-10.
No compiler, evaluator, producer or proof source is invoked or changed.
"""
from __future__ import annotations
import collections
import gzip
import hashlib
import json
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def audited(name):
    p = ROOT / name
    cert = json.loads(p.read_bytes())
    target = cert['targets']['current/connected']
    archive = ROOT / cert['evidence'] / target['audit_distribution']
    raw = gzip.decompress(archive.read_bytes())
    assert hashlib.sha256(raw).hexdigest() == target['audit_raw_sha256']
    audit = json.loads(raw)
    del raw
    assert len(audit['selected_modules']) == target['closure_modules']
    assert audit['declaration_count'] == len(audit['declarations']) == target['owned_declarations']
    assert audit['theorem_declaration_count'] == target['owned_theorems']
    assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
    rows = {r['name']: r for r in audit['declarations']}
    assert len(rows) == len(audit['declarations'])
    return p, cert, audit, rows


def normalized(row):
    return {k: sorted(v) if isinstance(v, list) else v for k, v in row.items()}


def digest(rows):
    h = hashlib.sha256()
    for name in sorted(rows):
        h.update(json.dumps(normalized(rows[name]), sort_keys=True, separators=(',', ':')).encode())
        h.update(b'\n')
    return h.hexdigest()


def main():
    old_path, old_cert, old, before = audited('INTEGRATED-MODULAR-UNION-CERTIFICATE.json')
    new_path, cert, audit, current = audited('HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json')
    assert all(cert['source_pins'].get(n) == h for n, h in old_cert['source_pins'].items())
    assert len(old['selected_modules']) == 1487 and len(audit['selected_modules']) == 1497
    assert len(before) == 100217 and len(current) == 100764
    for name, row in before.items():
        assert name in current and normalized(row) == normalized(current[name]), name
    kinds = collections.Counter(r['kind'] for r in current.values())
    assert kinds['theorem'] == 91540 == audit['theorem_declaration_count']
    modules = {m: collections.Counter() for m in audit['selected_modules']}
    for row in current.values():
        assert row['module'] in modules
        modules[row['module']][row['kind']] += 1
    added = set(current) - set(before)
    new_modules = set(audit['selected_modules']) - set(old['selected_modules'])
    assert len(new_modules) == 10
    assert all(current[n]['module'] in new_modules for n in added)
    old_digest = digest(before)
    retained_digest = digest({name: current[name] for name in before})
    assert old_digest == retained_digest
    out = {'status': 'PASS_COMPLETE_UNIQUE_OWNED_DECLARATION_KIND_MODULE_INVENTORY',
        'certificate_sha256': sha(new_path), 'audit_raw_sha256': cert['targets']['current/connected']['audit_raw_sha256'],
        'selected_modules': len(modules), 'unique_declarations': len(current),
        'theorem_declarations': kinds['theorem'], 'kind_counts': dict(sorted(kinds.items())),
        'module_kind_counts': {m: dict(sorted(c.items())) for m, c in modules.items()},
        'selected_modules_with_owned_declarations': sum(bool(c) for c in modules.values()),
        'added_modules': {m: cert['source_pins'][m] for m in sorted(new_modules)},
        'added_owned_declarations': len(added), 'added_theorem_declarations': sum(current[n]['kind'] == 'theorem' for n in added),
        'prior1487_certificate_sha256': sha(old_path), 'prior1487_owned_declarations_checked': len(before),
        'prior1487_owned_theorem_declarations_checked': old['theorem_declaration_count'],
        'prior1487_declaration_names_module_kind_axiom_and_reference_multisets_unchanged': True,
        'prior1487_canonical_owned_inventory_sha256': old_digest,
        'current_prior1487_subset_canonical_inventory_sha256': retained_digest,
        'canonicalization': 'Sorted declaration names; one canonical compact JSON row plus newline. Sort every list-valued reference/axiom field, retaining all strings and multiplicities.',
        'prior1487_audit_raw_sha256': old_cert['targets']['current/connected']['audit_raw_sha256'],
        'owned_axioms': [], 'nonstandard_axiom_rows': [], 'missing_modules': [],
        'root_independent_review_pending': True, 'compiler_evaluator_or_native_process_invoked_by_inventory': False,
        'accepted_artifacts_modified': False, 'inventory_helper_sha256': sha(Path(__file__))}
    path = ROOT / 'HISTORY-ACCEPTED-UNION-1497-OWNED-INVENTORY.json'
    assert not path.exists()
    save(path, out)
    print(json.dumps({k: out[k] for k in ['status', 'selected_modules', 'unique_declarations', 'theorem_declarations',
                     'added_owned_declarations', 'added_theorem_declarations', 'kind_counts']}))


if __name__ == '__main__':
    main()
