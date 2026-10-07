"""Independently authenticate actual partial compile and complete ownership audit.

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
FROZEN = '09015d8a33f8fd2f0509c4761d85a544ae008723'
PREFIX = 'clock-decoder-37666438115'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
log = BASE / (PREFIX + '-actions.log')
messages = []
for line in log.read_text().splitlines():
    if '\tVerify G6 frozen sources serially\t' in line:
        messages.append(re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '',
            line.split('\t', 2)[-1].lstrip('\ufeff')))
inputs = next(json.loads(m.split(' ', 1)[1]) for m in messages
    if m.startswith('G6_INPUTS '))
assert inputs['source_commit'] == FROZEN and len(inputs['modules']) == 147
prior = json.loads((BASE / 'timed-takeover-37658528073-independent.json').read_text())
old = {r['module']: r for r in prior['selected_source_checks']}
source_checks = []
for module, record in inputs['modules'].items():
    if module in old:
        assert record['sha256'] == old[module]['sha256'], module
        source_checks.append({'module': module, 'sha256': record['sha256'],
            'matched_previous_complete_170_source': True})
    else:
        if module == 'FiniteTagDecoder':
            file = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/FiniteTagDecoder.lean'
        else:
            assert module in {'UnifiedLean.G6.HistoryPrefix',
                'UnifiedLean.G6.RationalCertificate', 'UnifiedLean.G6.BinHistory',
                'UnifiedLean.G6.BinFold', 'UnifiedLean.G6.BinClock'}, module
            file = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/' + module.replace('.', '/') + '.lean'
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
assert pending is None and len(receipts) == 150
failed = [b['label'] for b in blocks if b['exit']]
assert failed == ['FiniteTagDecoder', 'BinClock'], failed
assert all(b['matches_receipt'] for b in blocks if b['label'] != 'cache')
audit = outputs['DeclarationAudit'].decode()
reports = []
for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit):
    axioms = [x.strip() for x in match.group(2).split(',') if x.strip()]
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    reports.append({'name': match.group(1), 'axioms': axioms})
assert len(reports) == len({r['name'] for r in reports}) == 117
assert not any('.BinClock.' in r['name'] or '.FiniteTagDecoder.' in r['name'] for r in reports)
assert 'sorryAx' not in audit
(BASE / (PREFIX + '-final-audit.txt')).write_bytes(outputs['DeclarationAudit'])
receipt = next(json.loads(m.split(' ', 1)[1]) for m in messages
    if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
begin = messages.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN')
end = messages.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
payload_lines = messages[begin+1:end]
interleaved_stderr = [m for m in payload_lines if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}', m)]
assert len(interleaved_stderr) == 1 and interleaved_stderr[0].startswith('Selected source failure: ')
compressed = base64.b64decode(''.join(m for m in payload_lines if m not in interleaved_stderr), validate=True)
raw = gzip.decompress(compressed)
assert len(raw) == receipt['bytes'] == 5200332
assert sha(raw) == receipt['sha256'] == 'c4e869579ffe47baa6fd3687ca1ed38519e2281276af0ea8cd7ac6e755764302'
inventory = json.loads(raw)
assert not inventory['owned_axioms'] and not inventory['nonstandard_axiom_rows'] and not inventory['missing_modules']
assert inventory['declaration_count'] == len(inventory['declarations']) == 3517
assert inventory['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in inventory['declarations']) == 2274
assert len({r['name'] for r in inventory['declarations']}) == 3517
failed_modules = {'FiniteTagDecoder', 'UnifiedLean.G6.BinClock'}
owned = [n for n in inputs['topological_order'] if n not in failed_modules]
assert len(owned) == receipt['selected_custom_modules'] == 145
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
(BASE / (PREFIX + '-inventory.json.gz')).write_bytes(compressed)
(BASE / (PREFIX + '-CompleteEnvironmentAudit.lean')).write_bytes(audit_source)
run = json.loads((BASE / (PREFIX + '-run.json')).read_text())
assert run['headSha'] == FROZEN and run['conclusion'] == 'failure'
result = {'schema': 'independent-clock-decoder-complete-inventory-v1', 'run': run,
    'log_sha256': sha(log.read_bytes()), 'command_receipts': len(receipts),
    'zero_exit_commands': sum(r['exit'] == 0 for r in receipts),
    'custom_modules': 147, 'successful_custom_modules': 145, 'failed_custom_modules': sorted(failed_modules),
    'source_checks': source_checks, 'command_stdout_checks': blocks,
    'selected_reports': reports, 'selected_report_count': 117,
    'selected_report_counts': {'G6': sum(r['name'].startswith('UnifiedLean.G6.') for r in reports),
        'G3': sum('G3' in r['name'] for r in reports), 'G5': sum('G5' in r['name'] for r in reports)},
    'final_audit_sha256': sha(outputs['DeclarationAudit']), 'complete_inventory_receipt': receipt,
    'complete_inventory_kind_counts': dict(collections.Counter(r['kind'] for r in inventory['declarations'])),
    'complete_inventory_module_counts': dict(collections.Counter(r['module'] for r in inventory['declarations'])),
    'complete_inventory_each_module_owned_rows': True, 'failed_modules_excluded_from_named_and_complete_audits': True,
    'complete_inventory_helper_sha256': sha(helper),
    'complete_inventory_reconstructed_source_sha256': sha(audit_source),
    'non_payload_interleaved_stderr': interleaved_stderr, 'compiler_launched_by_auditor': False}
(BASE / (PREFIX + '-independent.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ('command_receipts', 'zero_exit_commands', 'custom_modules',
    'successful_custom_modules', 'failed_custom_modules', 'selected_report_count', 'selected_report_counts',
    'final_audit_sha256', 'complete_inventory_receipt', 'complete_inventory_kind_counts')}))
