"""Read-only authentication of downloaded terminal evidence; launches no build."""
from pathlib import Path
from collections import Counter
import base64
import gzip
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parent
LOG = BASE / 'timed-takeover-37658528073-actions.log'
FROZEN = '849757a968ea29e215c569b16bf3ca6d15af6abc'
AUTHOR = Path('/workspace/cloud-lean/research/2026-10-07-cloud-g5-sol-ultra-1557z/verification/evidence/g5-takeover-run-37658528073-PASS')
sha = lambda raw: hashlib.sha256(raw).hexdigest()
messages = []
for line in LOG.read_text().splitlines():
    tail = line.split('\t', 2)[-1]
    messages.append(re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', tail))
payloads = {}
decoded = {}
receipts = []
stdout_matches = []
pending = None
pending_output = []
for position, message in enumerate(messages):
    if message.startswith('G5_TAKEOVER_COMMAND '):
        assert pending is None
        pending = json.loads(message.split(' ', 1)[1])
        pending_output = []
    elif message.startswith('G5_TAKEOVER_RECEIPT '):
        receipt = json.loads(message.split(' ', 1)[1])
        assert pending is not None and receipt['label'] == pending['label']
        receipts.append(receipt)
        raw = ('\n'.join(pending_output) + ('\n' if pending_output else '')).encode()
        stdout_matches.append({'label': receipt['label'], 'matches': sha(raw) == receipt['output_sha256'],
                               'reconstructed_sha256': sha(raw), 'receipt_sha256': receipt['output_sha256']})
        pending = None
    elif pending is not None:
        pending_output.append(message)
    match = re.match(r'^(G5_TAKEOVER_[A-Z_]+)_PAYLOAD (\{.*\})$', message)
    if match:
        tag, header = match.group(1), json.loads(match.group(2))
        start, end = tag + '_GZIP_BASE64_BEGIN', tag + '_GZIP_BASE64_END'
        assert messages[position + 1] == start
        finish = messages.index(end, position + 2)
        raw = gzip.decompress(base64.b64decode(''.join(messages[position + 2:finish]), validate=True))
        assert len(raw) == header['bytes'] and sha(raw) == header['sha256']
        assert raw == (AUTHOR / header['file']).read_bytes()
        payloads[tag] = header | {'independent_log_recovery': True, 'author_bytes_equal': True}
        decoded[header['file']] = json.loads(raw)
assert pending is None
context = decoded['SOURCE-CONTEXT.json']
assert context['source_commit'] == FROZEN
source_checks = []
for module, record in context['modules'].items():
    raw = subprocess.check_output(['git', 'show', FROZEN + ':' + record['source']], cwd=BASE.parents[1])
    assert sha(raw) == record['sha256']
    source_checks.append({'module': module, 'source': record['source'], 'sha256': sha(raw)})
results = decoded['module-results.json']
assert len(results) == 170 and all(r['exit'] == 0 for r in results.values())
audit = decoded['AUDIT-OWNED.json']
rows = audit['declarations']
assert len(rows) == audit['declaration_count'] == 3856
assert len({r['name'] for r in rows}) == len(rows)
assert sum(r['kind'] == 'theorem' for r in rows) == audit['theorem_declaration_count'] == 2522
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(r['axioms']) <= standard for r in rows)
assert all(isinstance(r['type_references'], list) and isinstance(r['body_references'], list) for r in rows)
assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
assert len(audit['selected_modules']) == 170
assert set(r['module'] for r in rows) == set(audit['selected_modules'])
assert len(receipts) == 178 and all(r['exit'] == 0 for r in receipts)
build = decoded['BUILD-RECEIPT.json']
assert sha((AUTHOR / 'TakeoverCompleteAudit-reconstructed.lean').read_bytes()) == build['audit_source_sha256']
run = json.loads((BASE / 'timed-takeover-37658528073-run.json').read_text())
assert run['headSha'] == FROZEN and run['conclusion'] == 'success'
summary = {'schema': 'independent-timed-takeover-authentication-v1', 'run': run,
    'log_sha256': sha(LOG.read_bytes()), 'payloads': payloads, 'command_count': len(receipts),
    'zero_exit_commands': sum(r['exit'] == 0 for r in receipts),
    'selected_source_count': len(source_checks), 'selected_source_checks': source_checks,
    'custom_modules': len(results), 'declarations': len(rows), 'theorems': audit['theorem_declaration_count'],
    'declaration_kinds': dict(Counter(r['kind'] for r in rows)),
    'module_rows': dict(sorted(Counter(r['module'] for r in rows).items())),
    'owned_axioms': audit['owned_axioms'], 'nonstandard_axiom_rows': audit['nonstandard_axiom_rows'],
    'missing_modules': audit['missing_modules'], 'all_selected_modules_have_rows': True,
    'all_rows_have_type_and_body_reference_fields': True,
    'external_roots': context['external_roots'], 'toolchain': context['toolchain'],
    'mathlib_commit': context['mathlib_commit'], 'audit_source_sha256': build['audit_source_sha256'],
    'reconstructed_command_stdout_checks': stdout_matches,
    'fresh_compiler_launched_by_auditor': False}
(BASE / 'timed-takeover-37658528073-independent.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:summary[k] for k in ('command_count','zero_exit_commands','selected_source_count',
    'custom_modules','declarations','theorems','declaration_kinds','owned_axioms','nonstandard_axiom_rows','missing_modules')}))
print(json.dumps({'stdout_hash_matches':sum(r['matches'] for r in stdout_matches),
    'stdout_mismatches':[r['label'] for r in stdout_matches if not r['matches']]}))
