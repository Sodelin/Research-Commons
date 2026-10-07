"""Independently authenticate actual partially successful compile and complete ownership audit.

Reads saved terminal evidence and exact Git blobs. Launches no compiler.
"""
from pathlib import Path
import base64
import collections
import gzip
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
FROZEN = '3abf1607cc9db9a53e5604de420aa50c115e4ab0'
AUTHOR = '5a99dfc825ad2fa35d4a438d0c10140dd89a689e'
AUTHOR_FAILURE = '4e5265a0cf0eb0f3ba65ebfc90e8078a89331a1f'
PREFIX = 'literal-prefix-37673216721'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
log = BASE / (PREFIX + '-actions.log')
log_text = log.read_text()
assert 'RUNTIME_SMOKE_PASSED source_commit=' + FROZEN in log_text
assert 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' in log_text
assert 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550' in log_text
assert '5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758' in log_text
messages = []
for line in log.read_text().splitlines():
    if '\tVerify G6 frozen sources serially\t' in line:
        messages.append(re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '',
            line.split('\t', 2)[-1].lstrip('\ufeff')))
inputs = next(json.loads(m.split(' ', 1)[1]) for m in messages
    if m.startswith('G6_INPUTS '))
assert inputs['source_commit'] == FROZEN and len(inputs['modules']) == 148
prior = json.loads((BASE / 'clock-decoder-37668810494-independent.json').read_text())
old = {r['module']: r for r in prior['source_checks']}
source_checks = []
for module, record in inputs['modules'].items():
    if module in old:
        assert record['sha256'] == old[module]['sha256'], module
        source_checks.append({'module': module, 'sha256': record['sha256'],
            'matched_previous_complete_147_source': True})
    else:
        assert module == 'LiteralSameBinTrace', module
        file = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/LiteralSameBinTrace.lean'
        raw = subprocess.check_output(['git', 'show', FROZEN + ':' + file], cwd=ROOT)
        assert sha(raw) == record['sha256'], module
        source_checks.append({'module': module, 'source': file, 'sha256': sha(raw),
            'matched_frozen_git_source': True})
receipts, blocks, outputs = [], [], {}
pending = None
output = []
for message in messages:
    if message.startswith('G6_COMMAND '):
        assert pending is None
        pending = json.loads(message.split(' ', 1)[1]); output = []
    elif message.startswith('G6_RECEIPT '):
        assert pending is not None
        receipt = json.loads(message.split(' ', 1)[1])
        raw = ('\n'.join(output) + ('\n' if output else '')).encode()
        label = Path(receipt['argv'][-1]).stem if receipt['argv'][1:3] == ['env', 'lean'] else 'cache'
        blocks.append({'label': label, 'stdout_sha256': sha(raw),
            'matches_receipt': sha(raw) == receipt['output_sha256'], 'exit': receipt['exit']})
        outputs[label] = raw
        receipts.append(receipt); pending = None
    elif pending is not None:
        output.append(message)
assert pending is None and len(receipts) == 151
failed = [b['label'] for b in blocks if b['exit']]
assert failed == ['LiteralSameBinTrace'], failed
failed_stdout = outputs['LiteralSameBinTrace']
assert b':77:12: error:' in failed_stdout and b':85:12: error:' in failed_stdout
assert failed_stdout.count(b'sorryAx') == 4
assert sha(failed_stdout) == '16eb55098969c3bb06363cb4cdbe1f561dae52d54ea0a87f0b5d5cde1b39fae9'
(BASE / (PREFIX + '-FAILED-LiteralSameBinTrace.log')).write_bytes(failed_stdout)
assert all(b['matches_receipt'] for b in blocks if b['label'] != 'cache')
audit = outputs['DeclarationAudit'].decode()
reports = []
for match in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", audit, re.DOTALL):
    axioms = [x.strip() for x in (match.group(2) or '').split(',') if x.strip()]
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    reports.append({'name': match.group(1), 'axioms': axioms})
assert len(reports) == len({r['name'] for r in reports}) == 139
assert sum('.BinClock.' in r['name'] for r in reports) == 3
assert sum('.FiniteTagDecoder.' in r['name'] for r in reports) == 19
assert 'sorryAx' not in audit
(BASE / (PREFIX + '-final-audit.txt')).write_bytes(outputs['DeclarationAudit'])
receipt = next(json.loads(m.split(' ', 1)[1]) for m in messages
    if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
begin = messages.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN')
end = messages.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
payload_lines = messages[begin+1:end]
interleaved_stderr = [m for m in payload_lines if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}', m)]
assert interleaved_stderr == ['Selected source failure: [{"module": "LiteralSameBinTrace", "result": "1"}]']
compressed = base64.b64decode(''.join(m for m in payload_lines if m not in interleaved_stderr), validate=True)
raw = gzip.decompress(compressed)
assert len(raw) == receipt['bytes'] == 5263688
assert sha(raw) == receipt['sha256'] == 'c6954831b092cf5dd2525b6866c2f7787aa511e5fc29c34c7c8c42cda7947521'
inventory = json.loads(raw)
assert not inventory['owned_axioms'] and not inventory['nonstandard_axiom_rows'] and not inventory['missing_modules']
assert inventory['declaration_count'] == len(inventory['declarations']) == 3609
assert inventory['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in inventory['declarations']) == 2298
assert len({r['name'] for r in inventory['declarations']}) == 3609
failed_modules = {'LiteralSameBinTrace'}
owned = [n for n in inputs['topological_order'] if n not in failed_modules]
assert len(owned) == receipt['selected_custom_modules'] == 147
assert inventory['selected_modules'] == owned
assert set(r['module'] for r in inventory['declarations']) == set(owned)
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    and 'type_references' in r and 'body_references' in r
    and isinstance(r['type_references'], list) and isinstance(r['body_references'], list)
    for r in inventory['declarations'])
template_path = 'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean'
template = subprocess.check_output(['git', 'show', FROZEN + ':' + template_path], cwd=ROOT).decode()
assert sha(template.encode()) == inputs['dependencies']['complete_inventory_template_sha256']
old_names = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(old_names) == 1
template = template.replace(old_names, '#[' + ', '.join(json.dumps(n) for n in owned) + ']')
audit_source = ('\n'.join('import ' + n for n in owned) + '\n' + template).encode()
assert sha(audit_source) == receipt['audit_source_sha256']
helper_path = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/complete_environment.py'
helper = subprocess.check_output(['git', 'show', FROZEN + ':' + helper_path], cwd=ROOT)
assert sha(helper) == inputs['dependencies']['complete_inventory_helper_sha256']
author_base = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37668810494-PASS/'
author_checks = []
for filename, recovered in [('complete-environment-inventory.json', raw),
        ('DeclarationAudit-actual.log', outputs['DeclarationAudit']),
        ('CompleteEnvironmentAudit-actual.log', outputs['CompleteEnvironmentAudit']),
        ('CompleteEnvironmentAudit-reconstructed.lean', audit_source)]:
    published = subprocess.check_output(['git', 'show', AUTHOR + ':' + author_base + filename], cwd=ROOT)
    assert published == recovered, filename
    author_checks.append({'path': author_base + filename, 'sha256': sha(published), 'byte_equal': True})
failure_base = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37673216721-FAILED/'
failure_publication_checks = []
for filename, recovered in [('LiteralSameBinTrace-actual.log', failed_stdout),
        ('complete-environment-inventory.json', raw),
        ('DeclarationAudit-actual.log', outputs['DeclarationAudit']),
        ('CompleteEnvironmentAudit-reconstructed.lean', audit_source)]:
    published = subprocess.check_output(['git', 'show', AUTHOR_FAILURE + ':' + failure_base + filename], cwd=ROOT)
    assert published == recovered, filename
    failure_publication_checks.append({'path': failure_base + filename, 'sha256': sha(published), 'byte_equal': True})
(BASE / (PREFIX + '-inventory.json.gz')).write_bytes(compressed)
(BASE / (PREFIX + '-CompleteEnvironmentAudit.lean')).write_bytes(audit_source)
run = json.loads((BASE / (PREFIX + '-run.json')).read_text())
assert run['headSha'] == FROZEN and run['conclusion'] == 'failure'
result = {'schema': 'independent-literal-prefix-failure-complete-inventory-v1', 'run': run,
    'log_sha256': sha(log.read_bytes()), 'command_receipts': len(receipts),
    'zero_exit_commands': sum(r['exit'] == 0 for r in receipts),
    'custom_modules': 148, 'successful_custom_modules': 147, 'failed_custom_modules': sorted(failed_modules),
    'source_checks': source_checks, 'command_stdout_checks': blocks,
    'selected_reports': reports, 'selected_report_count': 139,
    'selected_report_counts': {'G6': sum(r['name'].startswith('UnifiedLean.G6.') for r in reports),
        'G3': sum('G3' in r['name'] for r in reports), 'G5': sum('G5' in r['name'] for r in reports)},
    'final_audit_sha256': sha(outputs['DeclarationAudit']), 'complete_inventory_receipt': receipt,
    'complete_inventory_kind_counts': dict(collections.Counter(r['kind'] for r in inventory['declarations'])),
    'complete_inventory_module_counts': dict(collections.Counter(r['module'] for r in inventory['declarations'])),
    'complete_inventory_each_module_owned_rows': True, 'all_successful_custom_modules_owned_and_compiled': True, 'failed_recovery_sorry_reports_rejected': 4,
    'complete_inventory_helper_sha256': sha(helper),
    'complete_inventory_reconstructed_source_sha256': sha(audit_source),
    'prior_successful_publication_commit': AUTHOR, 'author_readback_checks': author_checks,
    'failure_publication_commit': AUTHOR_FAILURE, 'failure_publication_readback_checks': failure_publication_checks,
    'runtime_smoke_and_version_binary_source_pins_present': True,
    'G6_complete_owned_declarations': sum(r['module'].startswith('UnifiedLean.G6.') for r in inventory['declarations']),
    'G6_complete_owned_theorems': sum(r['module'].startswith('UnifiedLean.G6.') and r['kind'] == 'theorem' for r in inventory['declarations']),
    'FiniteTag_complete_owned_kind_counts': dict(collections.Counter(r['kind'] for r in inventory['declarations'] if r['module'] == 'FiniteTagDecoder')),
    'non_payload_interleaved_stderr': interleaved_stderr, 'compiler_launched_by_auditor': False}
(BASE / (PREFIX + '-independent.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('command_receipts', 'zero_exit_commands', 'custom_modules',
    'successful_custom_modules', 'failed_custom_modules', 'selected_report_count', 'selected_report_counts',
    'final_audit_sha256', 'complete_inventory_receipt', 'complete_inventory_kind_counts')}))
