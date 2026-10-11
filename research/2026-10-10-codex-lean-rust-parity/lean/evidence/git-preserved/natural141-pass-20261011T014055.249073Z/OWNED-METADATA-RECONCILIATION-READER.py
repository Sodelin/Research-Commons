#!/usr/bin/env python3
"""Read-only owned-metadata reconciliation; no Lean/native invocation.

Codex lean_integration_successor, 2026-10-11. Parent records are streamed.
Differences are disclosed for independent review, never silently accepted.
"""
import collections
import hashlib
import json
import pathlib
import re
import resource

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
W = pathlib.Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
R = W / '.build/runs/20261011T014055.249073Z'
A = pathlib.Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json')
B = pathlib.Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z/.build/runs/20261010T232230.265801Z/attempts/00003-OwnedAudit/work/AUDIT-RESULT.json')
N = R / 'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json'
F = pathlib.Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/metadata/factor-ite-true-proof-repair-3fc98f89-20261011T012921.157357Z/PROPOSAL-FREEZE-V10-ITE-TRUE.json')

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(2**20), b''):
            h.update(block)
    return h.hexdigest()

def records(p):
    """Parse this authenticated audit's declaration array in bounded chunks."""
    decoder = json.JSONDecoder()
    with p.open(encoding='utf-8') as f:
        header = ''
        while True:
            header += f.read(65536)
            match = re.search(r'"declarations"\s*:\s*\[', header)
            if match:
                break
            assert len(header) < 2**20, 'Audit header exceeds explicit bound'
        prefix, buf = header[:match.start()], header[match.end():]
        expected = int(re.search(r'"declaration_count"\s*:\s*(\d+)', prefix).group(1))
        for key in ('owned_axioms', 'nonstandard_axiom_rows', 'missing_modules'):
            assert re.search('"' + key + r'"\s*:\s*\[\s*\]', prefix)
        count = 0
        while True:
            buf = buf.lstrip()
            if buf.startswith(','):
                buf = buf[1:].lstrip()
            if buf.startswith(']'):
                assert count == expected
                return
            try:
                value, end = decoder.raw_decode(buf)
            except json.JSONDecodeError:
                more = f.read(65536)
                assert more, 'Incomplete authenticated audit record'
                buf += more
                assert len(buf) < 8 * 2**20, 'Single record exceeds explicit bound'
                continue
            assert isinstance(value, dict) and isinstance(value['name'], str)
            yield value
            count += 1
            buf = buf[end:]

assert sha(F) == 'd54d69c760f24b6e6a2e6fb7310c6b6d5a489250663bfafb82b0adda62d9da9f'
identity_before = {str(p): sha(p) for p in (A, B, N, F)}
freeze = json.loads(F.read_bytes())
current = json.loads(N.read_bytes())
assert len(current['selected_modules']) == 141
assert not current['owned_axioms'] and not current['nonstandard_axiom_rows'] and not current['missing_modules']
now = {r['name']: r for r in current['declarations']}
assert len(now) == current['declaration_count'] == 3486
assert sum(r['kind'] == 'theorem' for r in now.values()) == current['theorem_declaration_count'] == 2293
providers = {r['module'] for r in freeze['exact_composition']['accepted_providers']}
assert len(providers) == 139
arm = 'G6OriginalParallelArmTransport'
assert arm in providers
old, required, parent_counts = {}, set(), {}
for p, owned_modules in ((A, providers - {arm}), (B, {arm})):
    count, kept = 0, 0
    for row in records(p):
        count += 1
        required_here = row['module'] in owned_modules
        if required_here:
            required.add(row['name'])
        if row['name'] in now and (p == A or row['name'] not in old):
            old[row['name']] = {'record': row, 'parent_audit': str(p)}
            kept += 1
    parent_counts[str(p)] = {'complete_record_count': count, 'current_names_matched': kept}
missing = sorted(required - set(now))
assert not missing, 'Selected accepted-provider inventory is not fully retained'
identical, differences, new = [], [], []
for name, row in now.items():
    if name not in old:
        new.append(row)
        continue
    before = old[name]['record']
    if row == before:
        identical.append(name)
        continue
    fields = sorted(k for k in set(before) | set(row) if before.get(k) != row.get(k))
    differences.append({'name': name, 'parent_audit': old[name]['parent_audit'], 'changed_fields': fields,
                        'classification': 'GENERATED_OWNER_LABEL_ONLY' if fields == ['module'] else 'EXACT_REFERENCE_DELTA_REQUIRES_INDEPENDENT_REVIEW',
                        'before': before, 'after': row})
fresh_modules = {r['module'] for r in freeze['sources']}
assert all(r['module'] in fresh_modules for r in new)
headers = []
for source in freeze['sources']:
    owned = [r for r in now.values() if r['module'] == source['module']]
    for declaration in source['declarations']:
        names = [r for r in owned if r['name'].endswith('.' + declaration['name'])]
        assert len(names) == 1, (source['module'], declaration['name'], len(names))
        headers.append({'module': source['module'], 'authored_name': declaration['name'],
                        'header_sha256': declaration['sha256'], 'audited_name': names[0]['name'],
                        'audited_kind': names[0]['kind'], 'axioms': names[0]['axioms']})
assert len(headers) == 29
owned_counts = {m: dict(collections.Counter(r['kind'] for r in now.values() if r['module'] == m))
                for m in current['selected_modules']}
new_counts = {m: dict(collections.Counter(r['kind'] for r in new if r['module'] == m)) for m in fresh_modules}
report = {
    'status': 'PASS_COMPLETE_OWNED_RECONCILIATION_WITH_EXPLICIT_DELTAS_PENDING_SAVED_QC',
    'author': 'Codex lean_integration_successor', 'reader_path': str(pathlib.Path(__file__)),
    'reader_sha256': sha(pathlib.Path(__file__)), 'reader_address_space_limit_bytes': 256 * 2**20,
    'current_audit': {'path': str(N), 'sha256': sha(N), 'declarations': 3486, 'theorems': 2293},
    'parent_audits': [{'path': str(p), 'sha256': sha(p), **parent_counts[str(p)]} for p in (A, B)],
    'source_freeze': {'path': str(F), 'sha256': sha(F)}, 'accepted_provider_modules': 139,
    'expected_provider_names': len(required), 'missing_provider_names': missing,
    'inherited_names': len(old), 'literal_inherited_records': len(identical),
    'qualified_inherited_differences': differences, 'new_unique_owned_names': new,
    'new_unique_kind_counts_by_module': new_counts, 'actual_owner_kind_counts_all_modules': owned_counts,
    'authored_header_matches': headers,
    'prefix_qualification': 'a080 was an authenticated kernel-only component before this run. This is its first complete owned audit; prior owned metadata is not invented. Genuine new names remain distinct from inherited generated names whose narrow owner changes to Prefix.',
    'generated_context_qualification': 'Exact parsed fields, including module and private-reference aliases, are disclosed. Neither owner reassignment nor a reference delta is silently declared literal retention. Independent saved review and source/object identity checks remain required.',
    'coherent_union_executed': False, 'mathematical_or_native_producer_launched_by_this_reader': False,
}
assert identity_before == {str(p): sha(p) for p in (A, B, N, F)}
report['input_pre_post_hashes_stable'] = identity_before
out = R / 'OWNED-METADATA-RECONCILIATION.json'
assert not out.exists()
out.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
print(json.dumps({'report': str(out), 'sha256': sha(out), 'bytes': out.stat().st_size,
                  'inherited': len(old), 'literal': len(identical), 'differences': len(differences),
                  'new_unique': len(new), 'authored_headers': len(headers), 'new_kind_counts': new_counts}))
