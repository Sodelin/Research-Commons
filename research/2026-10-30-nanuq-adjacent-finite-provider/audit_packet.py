from pathlib import Path
import json,hashlib,re
r=Path(__file__).parent;m=json.loads((r/'SOURCE-MANIFEST.json').read_text());accept=json.loads((r/'BUILD-ACCEPTANCE.json').read_text());events=[json.loads(x) for x in (r/'BUILD-EVENTS.jsonl').read_text().splitlines()];last={e['module']:e for e in events};external=set()
for mod in m['order']:
 src=(r/(mod+'.lean')).read_bytes();sha=hashlib.sha256(src).hexdigest();e=last[mod]
 assert sha==m['modules'][mod]['source_sha256']==e['source_sha256'] and e['exit']==0
 assert hashlib.sha256((r/(mod+'.olean')).read_bytes()).hexdigest()==e['olean_sha256']
 text=src.decode();assert 'set_option debug.skipKernelTC false' in text
 assert not re.search(r'\bnative_decide\b|\bsorry\b|\badmit\b|debug\.skipKernelTC true|^\s*axiom\b',text,re.M),mod
 external.update(x for x in m['modules'][mod]['imports'] if x not in m['modules'])
log=(r/'build-logs/FiniteProvider.log').read_text();axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log)
assert len(axioms)==7
allowed={'propext','Classical.choice','Quot.sound'}
for row in axioms:assert set(x.strip() for x in row.split(','))<=allowed
assert len([x for x in m['order'] if x.startswith('Full_')])==120
result={'status':'PASS_EXACT_SOURCE_SCOPED_PROVIDER','module_count':len(m['order']),'all_120_masks':True,'source_manifest_sha256':hashlib.sha256((r/'SOURCE-MANIFEST.json').read_bytes()).hexdigest(),'endpoint_axiom_whitelist':sorted(allowed),'endpoint_axiom_checks':7,'external_imports':sorted(external),'all_sources_have_kernel_checking_enabled':True,'native_decide_sorry_admit_or_source_axiom':False,'whole_original_network_NANUQ_theorem_verified':False,'remaining_gates':['actual source plane/contour/order provider','actual opened graph to ordered Tree syntax and quartet semantics','arbitrary-size restriction to at most six labels','compose original source metric/circular reconstruction/global exact support']}
(r/'RECEIPT-AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
