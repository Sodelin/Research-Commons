from pathlib import Path
import json,hashlib
O=Path(__file__).parent;N=Path('LOCAL_EVIDENCE/natural309-independent-review-20261012-0423z')
rd=lambda p:json.loads(p.read_bytes());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=rd(O/'TERMINAL-EVIDENCE-CHECK.json');b=rd(N/'TERMINAL-EVIDENCE-CHECK.json');assert a['retained_prior_names']==102354 and a['changed_prior_records']==[]
new={x['name']:x for x in a['new_records']};narrow={x['name']:x for x in b['new_records']};assert len(new)==16 and new==narrow;assert a['declarations']==102370 and a['theorems']==92667
r={'status':'ALL_PRIOR_FULL_RECORDS_LITERAL_AND_ALL_NEW_RECORDS_MATCH_NARROW','prior1596_records':102354,'missing_old_records':0,'changed_old_records':0,'exact_new_records':16,'new_theorem_records':14,'full_record_count':102370,'full_theorem_count':92667,'narrow309_qualifications_not_used_as_exemptions':True,'full_evidence_sha256':H(O/'TERMINAL-EVIDENCE-CHECK.json'),'narrow_evidence_sha256':H(N/'TERMINAL-EVIDENCE-CHECK.json'),'new_records':a['new_records']};(O/'LITERAL-RECORD-COMPARISON.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='new_records'},indent=2))
