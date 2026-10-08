"""Authenticate the actual partial 176-module terminal, sources and full inventory; no compiler."""
from pathlib import Path
import base64, collections, gzip, hashlib, json, re, subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
FROZEN = '28921f4ff46126897828244e8cad86b13ff603b9'
PREFIX = 'natural-family-repair-attempt-37720559518'
PRIOR = 'natural-family-attempt-37718922897'
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(path):
    return subprocess.check_output(['git', 'show', FROZEN + ':' + path], cwd=ROOT)

log = (BASE / (PREFIX + '-actions.log')).read_bytes()
text = log.decode()
assert 'RUNTIME_SMOKE_PASSED source_commit=' + FROZEN in text
for pin in ['Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)',
            'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
            '5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758']:
    assert pin in text
msgs = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', l.split('\t', 2)[-1].lstrip('\ufeff')) for l in text.splitlines()]
inputs = next(json.loads(m.split(' ', 1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
assert inputs['source_commit'] == FROZEN and len(inputs['modules']) == 176
prior = json.loads((BASE / (PRIOR + '-independent.json')).read_text())
old = {r['module']: r for r in prior['source_checks'] if r['module'] in prior['successful_module_names']}
allold = {r['module']:r for r in prior['source_checks']}
newmodules = {'UnifiedLean.G6.PrivateRegister'+x for x in ['SourceStep','Boundary','Program','History']}
assert set(allold) == set(inputs['modules'])
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', FROZEN], cwd=ROOT).decode().splitlines()
checks = []
for module, rec in inputs['modules'].items():
    replacements = {'UnifiedLean.G6.PrivateRegisterSourceStep':'9dcd5b7e4629ca52045f8ca78342a1357b35392306f7bd3d6708924bf46e0b9f','UnifiedLean.G6.PrivateRegisterBoundary':'174e1dd766b450d680d93b5255528192367266617cbb2f7abdf0d9f73c96aef3'}
    assert rec['sha256'] == replacements.get(module,allold[module]['sha256']),module
    own = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/' + rec['path']
    candidates = sorted([p for p in paths if p.endswith('/' + rec['path'])], key=lambda p: (p != own, len(p), p))
    found = next((p for p in candidates if sha(git(p)) == rec['sha256']), None)
    assert found, module
    raw = git(found)
    checks.append({'module': module, 'source': found, 'sha256': sha(raw), 'bytes': len(raw),
                   'git_blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest(),
                   'matched_frozen_git_source': True, 'matched_prior_167_source': module in old})

receipts, blocks, outputs = [], [], {}
pending, lines = None, []
for msg in msgs:
    if msg.startswith('G6_COMMAND '):
        assert pending is None
        pending = json.loads(msg.split(' ', 1)[1]); lines = []
    elif msg.startswith('G6_RECEIPT '):
        assert pending is not None
        r = json.loads(msg.split(' ', 1)[1])
        assert pending['argv'] == r['argv']
        label = Path(r['argv'][-1]).stem if r['argv'][1:3] == ['env', 'lean'] else 'cache'
        raw = ('\n'.join(lines) + ('\n' if lines else '')).encode()
        if label != 'cache': assert sha(raw) == r['output_sha256'], label
        blocks.append({'label': label, 'exit': r['exit'], 'stdout_sha256': sha(raw), 'matches_receipt': sha(raw) == r['output_sha256']})
        outputs[label] = raw; receipts.append(r); pending = None
    elif pending is not None:
        lines.append(msg)
assert pending is None and len(receipts) == 176 and sum(r['exit'] == 0 for r in receipts) == 174
module_receipts = {m: next((r for r in receipts if Path(r['argv'][-1]).stem == m.rsplit('.', 1)[-1]), None) for m in inputs['modules']}
successful = [m for m in inputs['topological_order'] if module_receipts[m] is not None and module_receipts[m]['exit'] == 0]
failed = [m for m in inputs['topological_order'] if module_receipts[m] is not None and module_receipts[m]['exit'] != 0]
blocked = [m for m in inputs['topological_order'] if module_receipts[m] is None]
assert len(successful) == 171 and set(successful) == set(old) | newmodules
assert set(failed) == {'PrivateSeedFactorization','UnifiedLean.G6.PrivateRegisterCalendar'}
assert len(blocked) == 3 and set(failed+blocked) == set(inputs['modules']) - set(successful)
assert all(m not in old for m in failed+blocked)

audit = outputs['DeclarationAudit'].decode()
reports = []
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", audit, re.DOTALL):
    ax = [x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
    assert set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}
    reports.append({'name': m.group(1), 'axioms': ax})
assert len(reports) == len({r['name'] for r in reports}) == 403 and 'sorryAx' not in audit
report_counts = {'G6': sum(r['name'].startswith(('UnifiedLean.G6.', 'CloudG6.')) for r in reports),
                 'G3': sum(r['name'].startswith('CloudG3.') for r in reports),
                 'G5': sum(r['name'].startswith('GProgram.G5.') for r in reports)}
assert report_counts == {'G6': 271, 'G3': 117, 'G5': 15}
assert all(r in reports for r in prior['selected_reports'])
newreports = [r['name'] for r in reports if r['name'] not in {r['name'] for r in prior['selected_reports']}]
assert len(newreports) == 24 and all(any(n.startswith(m+'.') for m in newmodules) for n in newreports)

receipt = next(json.loads(m.split(' ', 1)[1]) for m in msgs if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
begin, end = msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN'), msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
payload = msgs[begin + 1:end]
interleave = [l for l in payload if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}', l)]
compressed = base64.b64decode(''.join(l for l in payload if l not in interleave), validate=True)
raw = gzip.decompress(compressed)
assert len(raw) == receipt['bytes'] == 6101553
assert sha(raw) == receipt['sha256'] == 'd61141f5293ad0b341657f5876c06810b7dad96b2dbb715850d57cfab677ab95'
inv = json.loads(raw)
prior_inv = json.loads((BASE / (PRIOR + '-inventory.json')).read_bytes())
assert not inv['owned_axioms'] and not inv['nonstandard_axiom_rows'] and not inv['missing_modules']
assert inv['declaration_count'] == len(inv['declarations']) == 4055
assert inv['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in inv['declarations']) == 2643
owned = successful
assert len(owned) == receipt['selected_custom_modules'] == 171 and inv['selected_modules'] == owned
assert set(r['module'] for r in inv['declarations']) == set(owned)
current = {r['name']: r for r in inv['declarations']}
assert len(current) == 4055 and all(r['name'] in current for r in reports)
assert all(current[r['name']] == r for r in prior_inv['declarations'])
rows = [r for r in inv['declarations'] if r['module'] in newmodules]
assert len(rows) == 28 and sum(r['kind'] == 'theorem' for r in rows) == 21 and sum(r['kind'] == 'definition' for r in rows) == 7
assert all(set(r['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} and isinstance(r['type_references'], list) and isinstance(r['body_references'], list) for r in inv['declarations'])

template = git('research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').decode()
assert sha(template.encode()) == inputs['dependencies']['complete_inventory_template_sha256']
marker = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(marker) == 1
template = template.replace(marker, '#[' + ', '.join(json.dumps(n) for n in owned) + ']')
complete_source = ('\n'.join('import ' + n for n in owned) + '\n' + template).encode()
assert sha(complete_source) == receipt['audit_source_sha256']
helper = git('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/complete_environment.py')
assert sha(helper) == inputs['dependencies']['complete_inventory_helper_sha256']
targets = [m for m in inputs['targets'] if m in successful]; source_lookup = {r['module']: r['source'] for r in checks}
decl = []
for module in targets:
    source = git(source_lookup[module]).decode()
    namespace = re.search(r'^namespace\s+(\S+)\s*$', source, re.M)[1]
    decl.extend(namespace + '.' + n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)", source, re.M))
assert decl == [r['name'] for r in reports]
named = ('\n'.join('import ' + n for n in targets) + '\n\n' + '\n'.join('#print axioms ' + n for n in decl) + '\n').encode()
run = json.loads((BASE / (PREFIX + '-run.json')).read_text())
job = json.loads((BASE / (PREFIX + '-job.json')).read_text())
assert run['head_sha'] == FROZEN and run['status'] == 'completed' and run['conclusion'] == 'failure'
assert job['id'] == 113126987490 and job['status'] == 'completed' and job['conclusion'] == 'failure'
for suffix, data in [('inventory.json', raw), ('CompleteEnvironmentAudit.lean', complete_source),
                     ('DeclarationAudit.lean', named), ('final-audit.txt', outputs['DeclarationAudit']),
                     ('PrivateRegisterSourceStep-actual.log',outputs['PrivateRegisterSourceStep']),
                     ('PrivateRegisterBoundary-actual.log',outputs['PrivateRegisterBoundary']),
                     ('PrivateRegisterProgram-actual.log',outputs['PrivateRegisterProgram']),
                     ('PrivateRegisterHistory-actual.log',outputs['PrivateRegisterHistory']),
                     ('PrivateSeedFactorization-failed.log',outputs['PrivateSeedFactorization']),
                     ('PrivateRegisterCalendar-failed.log',outputs['PrivateRegisterCalendar'])]:
    (BASE / (PREFIX + '-' + suffix)).write_bytes(data)
result = {'schema': 'independent-natural-family-partial-v1', 'run': run, 'job': job,
          'log_sha256': sha(log), 'command_receipts': 176, 'zero_exit_commands': 174,
          'custom_modules': 176, 'successful_custom_modules': 171, 'successful_module_names': successful, 'failed_custom_modules': failed,
          'blocked_custom_modules': blocked, 'excluded_custom_modules': failed+blocked, 'source_checks': checks,
          'command_stdout_checks': blocks, 'selected_reports': reports, 'selected_report_count': 403,
          'selected_report_counts': report_counts,
          'final_audit_sha256': sha(outputs['DeclarationAudit']), 'named_audit_source_sha256': sha(named),
          'complete_inventory_receipt': receipt, 'new_selected_reports': newreports,
          'new_owned_rows': rows, 'complete_inventory_kind_counts': dict(collections.Counter(r['kind'] for r in inv['declarations'])),
          'all_prior_4027_owned_rows_byte_equal': True, 'all176_source_pins_authenticated': True,
          'all_successful_modules_owned_including_generated_type_body_refs': True,
          'non_payload_interleaved_stderr': interleave, 'archive_transport_attempted': False,
          'compiler_launched_by_auditor': False, 'author_publication_commit': None,'new_modules':sorted(newmodules)}
(BASE / (PREFIX + '-independent.json')).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'command_receipts': 176, 'custom_modules': 176, 'successful_modules':171,'selected_reports': 403,
                  'owned': 4055, 'theorems': 2643, 'raw_sha256': sha(raw),
                  'audit_source_sha256': sha(complete_source), 'named_audit_source_sha256': sha(named),
                  'new_owned_rows': len(rows), 'interleaved_stderr': interleave}))
