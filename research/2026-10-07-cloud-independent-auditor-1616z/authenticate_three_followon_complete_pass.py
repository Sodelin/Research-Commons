"""Static authentication of the actual complete 179-source PASS; never invokes Lean."""
from pathlib import Path
import base64, collections, gzip, hashlib, json, re, subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
PREFIX = 'three-followon-pass-37738512508'
PRIOR = 'three-followon-repair-37734981680'
FROZEN = '62e937a2b58f00f6ed1197133650b6da2f96f71f'
NEW = {
    'UnifiedLean.G6.RationalResidualCertificate': 'd9f49ca8cacdb40ec20a185db60db17e768d38d2c8632fcf2842ae682e995d3a',
}
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(path):
    return subprocess.check_output(['git', 'show', FROZEN + ':' + path], cwd=ROOT)

log = (BASE / (PREFIX + '-actions.log')).read_bytes()
assert sha(log) == 'b65c176521e7797dd71ad91d4d4a6b318d3a6954c802ada6ed68d56e801850a5'
text = log.decode()
for pin in ['RUNTIME_SMOKE_PASSED source_commit=' + FROZEN,
            'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)',
            'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
            '5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758']:
    assert pin in text
msgs = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', l.split('\t', 2)[-1].lstrip('\ufeff')) for l in text.splitlines()]
inputs = next(json.loads(m.split(' ', 1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
prior = json.loads((BASE / (PRIOR + '-independent.json')).read_text())
old = {r['module']: r for r in prior['source_checks']}
assert inputs['source_commit'] == FROZEN and len(inputs['modules']) == 179
assert set(inputs['modules']) == set(old) and len(old) == 179
prior_success = set(prior['successful_module_names'])
assert len(prior_success) == 178
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', FROZEN], cwd=ROOT).decode().splitlines()
checks = []
for module, rec in inputs['modules'].items():
    assert rec['sha256'] == (NEW[module] if module in NEW else old[module]['sha256']), module
    own = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/' + rec['path']
    candidates = sorted([p for p in paths if p.endswith('/' + rec['path'])], key=lambda p: (p != own, len(p), p))
    found = next((p for p in candidates if sha(git(p)) == rec['sha256']), None)
    assert found, module
    b = git(found)
    checks.append({'module': module, 'source': found, 'sha256': sha(b), 'bytes': len(b),
                   'git_blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest(),
                   'matched_frozen_git_source': True, 'matched_prior178_source': module not in NEW})

receipts, blocks, outputs, pending, lines = [], [], {}, None, []
for msg in msgs:
    if msg.startswith('G6_COMMAND '):
        assert pending is None
        pending = json.loads(msg.split(' ', 1)[1]); lines = []
    elif msg.startswith('G6_RECEIPT '):
        assert pending is not None
        r = json.loads(msg.split(' ', 1)[1]); assert pending['argv'] == r['argv']
        label = Path(r['argv'][-1]).stem if r['argv'][1:3] == ['env', 'lean'] else 'cache'
        b = ('\n'.join(lines) + ('\n' if lines else '')).encode()
        if label != 'cache': assert sha(b) == r['output_sha256'], label
        assert label not in outputs, label
        outputs[label] = b
        blocks.append({'label': label, 'exit': r['exit'], 'stdout_sha256': sha(b), 'matches_receipt': sha(b) == r['output_sha256']})
        receipts.append(r); pending = None
    elif pending is not None:
        lines.append(msg)
assert pending is None and len(receipts) == 182 and sum(r['exit'] == 0 for r in receipts) == 182
assert all(all(flag in r['argv'] for flag in ['--trust=0','-j1','-M4096'])
           for r in receipts if r['argv'][1:3] == ['env','lean'])
module_receipts = {m: next((r for r in receipts if Path(r['argv'][-1]).stem == m.rsplit('.', 1)[-1]), None) for m in inputs['modules']}
successful = [m for m in inputs['topological_order'] if module_receipts[m] is not None and module_receipts[m]['exit'] == 0]
failed = [m for m in inputs['topological_order'] if module_receipts[m] is not None and module_receipts[m]['exit'] != 0]
blocked = [m for m in inputs['topological_order'] if module_receipts[m] is None]
assert len(successful) == 179 and set(successful) == prior_success | {'UnifiedLean.G6.RationalResidualCertificate'}
assert not failed and not blocked

audit = outputs['DeclarationAudit'].decode(); reports = []
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", audit, re.DOTALL):
    ax = [x.strip() for x in (m.group(2) or '').split(',') if x.strip()]
    assert set(ax) <= {'propext', 'Classical.choice', 'Quot.sound'}
    reports.append({'name': m.group(1), 'axioms': ax})
assert len(reports) == len({r['name'] for r in reports}) == 501 and 'sorryAx' not in audit
counts = {'G6': sum(r['name'].startswith(('UnifiedLean.G6.', 'CloudG6.')) for r in reports),
          'G3': sum(r['name'].startswith('CloudG3.') for r in reports),
          'G5': sum(r['name'].startswith('GProgram.G5.') for r in reports)}
assert counts == {'G6':352, 'G3':134, 'G5':15} and all(r in reports for r in prior['selected_reports'])
newreports = [r['name'] for r in reports if r['name'] not in {r['name'] for r in prior['selected_reports']}]
assert len(newreports) == 14 and all(n.startswith('UnifiedLean.G6.RationalResidualCertificate.') for n in newreports)

receipt = next(json.loads(m.split(' ', 1)[1]) for m in msgs if m.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
a, b = msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN'), msgs.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
payload = msgs[a + 1:b]
interleave = [l for l in payload if not re.fullmatch(r'[A-Za-z0-9+/]+={0,2}', l)]
raw = gzip.decompress(base64.b64decode(''.join(l for l in payload if l not in interleave), validate=True))
assert len(raw) == receipt['bytes'] == 6430249
assert sha(raw) == receipt['sha256'] == 'cf0a500c9e35831cd598d6f12edd4fc0e63b534a2ad4322eb6584981307944ba'
inv = json.loads(raw); prior_inv = json.loads((BASE / (PRIOR + '-inventory.json')).read_bytes())
assert not inv['owned_axioms'] and not inv['nonstandard_axiom_rows'] and not inv['missing_modules']
assert inv['declaration_count'] == len(inv['declarations']) == 4209
assert inv['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in inv['declarations']) == 2766
assert receipt['selected_custom_modules'] == len(successful) == 179 and inv['selected_modules'] == successful
assert set(r['module'] for r in inv['declarations']) == set(successful)
current = {r['name']:r for r in inv['declarations']}
assert len(current) == 4209 and all(r['name'] in current for r in reports)
assert all(current[r['name']] == r for r in prior_inv['declarations'])
rows = [r for r in inv['declarations'] if r['module'] == 'UnifiedLean.G6.RationalResidualCertificate']
assert len(rows) == 21 and sum(r['kind'] == 'theorem' for r in rows) == 18 and sum(r['kind'] == 'definition' for r in rows) == 3
assert all(set(r['axioms']) <= {'propext','Classical.choice','Quot.sound'} and isinstance(r['type_references'],list) and isinstance(r['body_references'],list) for r in inv['declarations'])
exception = prior['prior171_to175_generated_helper_reference_exception_retained']
assert len(exception) == 1 and current[exception[0]['current']['name']] == exception[0]['current']
helper_names = set(exception[0]['prior']['body_references']) ^ set(exception[0]['current']['body_references'])
prior_by_name = {r['name']:r for r in prior_inv['declarations']}
assert len(helper_names) == 2 and all(current[n] == prior_by_name[n] for n in helper_names)

template = git('research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').decode()
assert sha(template.encode()) == inputs['dependencies']['complete_inventory_template_sha256']
marker = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(marker) == 1
template = template.replace(marker, '#[' + ', '.join(json.dumps(n) for n in successful) + ']')
complete = ('\n'.join('import ' + n for n in successful) + '\n' + template).encode()
assert sha(complete) == receipt['audit_source_sha256'] == '2fd8f63e5618d1a856edf9252683e14ae130d2844c170d942d09758f40fbb47a'
helper = git('research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/complete_environment.py')
assert sha(helper) == inputs['dependencies']['complete_inventory_helper_sha256']
targets = [m for m in inputs['targets'] if m in successful]; lookup = {r['module']:r['source'] for r in checks}; decl=[]
for module in targets:
    s = git(lookup[module]).decode(); ns = re.search(r'^namespace\s+(\S+)\s*$',s,re.M)[1]
    decl.extend(ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)",s,re.M))
assert decl == [r['name'] for r in reports]
named = ('\n'.join('import '+m for m in targets)+'\n\n'+'\n'.join('#print axioms '+n for n in decl)+'\n').encode()
run = json.loads((BASE/(PREFIX+'-run.json')).read_text()); job=json.loads((BASE/(PREFIX+'-job.json')).read_text())
assert run['head_sha'] == FROZEN and run['status'] == 'completed' and run['conclusion'] == 'success'
assert job['id'] == 113183496375 and job['status'] == 'completed' and job['conclusion'] == 'success'
for suffix,data in [('inventory.json',raw),('CompleteEnvironmentAudit.lean',complete),('DeclarationAudit.lean',named),('final-audit.txt',outputs['DeclarationAudit']),('HybridSizeCore-actual.log',outputs['HybridSizeCore']),('RationalResidualCertificate-actual.log',outputs['RationalResidualCertificate'])]:
    (BASE/(PREFIX+'-'+suffix)).write_bytes(data)
result={'schema':'independent-three-followon-complete-pass-v1','run':run,'job':job,'log_sha256':sha(log),'command_receipts':182,'zero_exit_commands':182,'requested_custom_modules':179,'successful_custom_modules':179,'successful_module_names':successful,'failed_custom_modules':failed,'blocked_custom_modules':blocked,'excluded_custom_modules':failed+blocked,'source_checks':checks,'command_stdout_checks':blocks,'selected_reports':reports,'selected_report_count':501,'selected_report_counts':counts,'final_audit_sha256':sha(outputs['DeclarationAudit']),'named_audit_source_sha256':sha(named),'complete_inventory_receipt':receipt,'complete_inventory_kind_counts':dict(collections.Counter(r['kind'] for r in inv['declarations'])),'new_selected_reports':newreports,'new_owned_rows':rows,'all_prior4188_rows_byte_equal':True,'prior171_to175_generated_helper_reference_exception_retained':exception,'both_splitter_helper_rows_byte_equal_to178':True,'all179_frozen_source_pins_authenticated':True,'all181_noncache_stdout_authenticated':True,'all_successful_modules_owned_including_generated_type_body_refs':True,'non_payload_interleaved_stderr':interleave,'archive_transport_attempted':False,'compiler_launched_by_auditor':False,'author_publication_commit':None}
(BASE/(PREFIX+'-independent.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'receipts':182,'zero':182,'requested':179,'successful':179,'named':501,'owned':4209,'theorems':2766,'raw_sha256':sha(raw),'audit_source_sha256':sha(complete),'named_audit_source_sha256':sha(named),'all4188prior_rows_exact':True,'new_owned':len(rows),'failed':failed,'interleaved':interleave}))
