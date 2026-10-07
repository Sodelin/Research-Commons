"""Parse actual current-stage receipts; failed-source recovery is excluded."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
FROZEN = '4fed3030da86d94c85fbb7ecd7ea33b250e06772'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
LOG = BASE / 'history-fold-37663829244-actions.log'
messages = []
for line in LOG.read_text().splitlines():
    if '\tVerify G6 frozen sources serially\t' not in line:
        continue
    messages.append(re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', line.split('\t',2)[-1].lstrip('\ufeff')))
inputs = next(json.loads(m.split(' ',1)[1]) for m in messages if m.startswith('G6_INPUTS '))
assert inputs['source_commit'] == FROZEN and len(inputs['modules']) == 142
prior = json.loads((BASE / 'timed-takeover-37658528073-independent.json').read_text())
old = {r['module']:r for r in prior['selected_source_checks']}
checks = []
for module, record in inputs['modules'].items():
    if module in old:
        assert record['sha256'] == old[module]['sha256']
        checks.append({'module':module,'sha256':record['sha256'],'matched_previous_complete_170_source':True})
    else:
        assert module in {'UnifiedLean.G6.HistoryPrefix','UnifiedLean.G6.BinHistory','UnifiedLean.G6.RationalCertificate','UnifiedLean.G6.BinFold'}
        file='research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/'+module.replace('.','/')+'.lean'
        raw=subprocess.check_output(['git','show',FROZEN+':'+file],cwd=ROOT)
        assert sha(raw)==record['sha256']
        checks.append({'module':module,'source':file,'sha256':sha(raw),'matched_frozen_git_source':True})
receipts=[]
blocks=[]
pending=None
output=[]
for message in messages:
    if message.startswith('G6_COMMAND '):
        assert pending is None
        pending=json.loads(message.split(' ',1)[1]); output=[]
    elif message.startswith('G6_RECEIPT '):
        receipt=json.loads(message.split(' ',1)[1]); assert pending is not None
        raw=('\n'.join(output)+ ('\n' if output else '')).encode()
        label=Path(receipt['argv'][-1]).stem if receipt['argv'][1:3]==['env','lean'] else 'cache'
        blocks.append({'label':label,'stdout_sha256':sha(raw),'matches_receipt':sha(raw)==receipt['output_sha256'],'exit':receipt['exit']})
        receipts.append(receipt)
        if label=='DeclarationAudit':
            (BASE/'history-fold-37663829244-final-audit.txt').write_bytes(raw)
            audit_output=raw.decode()
        if label=='HistoryPrefix': failed_output=raw.decode()
        pending=None
    elif pending is not None:
        output.append(message)
assert pending is None and len(receipts)==144
assert all(r['exit']==0 for r in receipts)
assert not [b for b in blocks if b['exit']]
assert all(b['matches_receipt'] for b in blocks if b['label']!='cache')
reports=[]
for match in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit_output):
    axioms=[x.strip() for x in match.group(2).split(',') if x.strip()]
    assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
    reports.append({'name':match.group(1),'axioms':axioms})
assert len(reports)==len({r['name'] for r in reports})==117
assert sum('.HistoryPrefix.' in r['name'] for r in reports)==10
assert 'sorryAx' not in audit_output
run=json.loads((BASE/'history-fold-37663829244-run.json').read_text())
assert run['headSha']==FROZEN and run['conclusion']=='success'
result={'schema':'independent-current-stage-helper-compiler-review-v1','run':run,'log_sha256':sha(LOG.read_bytes()),
    'command_receipts':len(receipts),'zero_exit_commands':sum(r['exit']==0 for r in receipts),
    'custom_modules':142,'successful_custom_modules':142,'failed_custom_modules':[],
    'source_checks':checks,'all_sources_match_prior_authenticated_or_frozen_git':True,
    'command_stdout_checks':blocks,'successful_selected_audit_declarations':117,
    'successful_audit_counts':{'G6':sum(r['name'].startswith('UnifiedLean.G6.') for r in reports),
       'G3':sum('G3' in r['name'] for r in reports),'G5':sum('G5' in r['name'] for r in reports)},
    'successful_audit_reports':reports,'final_audit_sha256':sha(audit_output.encode()),
    'failed_history_recovery_reports_rejected':True,'current_history_compilation_passed':True,'new_helper_receipts':{b['label']:b for b in blocks if b['label'] in ('HistoryPrefix','RationalCertificate','BinHistory','BinFold')},
    'compiler_launched_by_auditor':False}
(BASE/'history-fold-37663829244-independent.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('command_receipts','zero_exit_commands','custom_modules',
    'successful_custom_modules','failed_custom_modules','successful_selected_audit_declarations','successful_audit_counts','final_audit_sha256','new_helper_receipts')}))
