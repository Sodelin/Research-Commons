"""Incremental exact-source receipt inventory; no compilation or proof claims."""
from pathlib import Path
import json,hashlib,datetime,re,sys
B=Path(__file__).parent;p=B/'receipts/FULL-CLAIMED-PACKAGE-LEAN-MANIFEST.json'
o=json.loads(p.read_text());rows=[]
for src in sorted((B/'program').glob('*.lean')):
 rec=B/'receipts'/f'{src.stem}-receipt.json';digest=hashlib.sha256(src.read_bytes()).hexdigest();d=json.loads(rec.read_text()) if rec.exists() else {}
 exitcode=d.get('exit_code',d.get('compile_exit_code',d.get('aggregate_compile_exit_code')))
 status=d.get('status',('PASS_LOCAL_COMPONENT' if exitcode==0 else 'FAILED_ATTEMPT') if exitcode is not None else 'NO_MATCHING_RECEIPT')
 expected=d.get('source_sha256',d.get('aggregate_source_sha256'))
 if expected and expected!=digest:status='SOURCE_CHANGED_SINCE_RECEIPT'
 axioms=d.get('axiom_lines',[])
 if not axioms and 'modules'in d:axioms=[line for m in d['modules'] for line in m.get('axiom_lines',[])]
 for line in axioms:
  names=re.search(r'\[(.*?)\]',line)
  if names and any(a.strip() not in ['propext','Classical.choice','Quot.sound'] for a in names.group(1).split(',') if a.strip()):
   if status.startswith('PASS'):status='NONSTANDARD_AXIOM_AUDIT'
 moved=[]
 for module, oldhash in d.get('direct_project_import_olean_sha256',{}).items():
  obj=B/'build/objects'/Path(*module.split('.')).with_suffix('.olean')
  if not obj.exists() or hashlib.sha256(obj.read_bytes()).hexdigest()!=oldhash:moved.append(module)
 rows.append({'module':src.stem,'source':str(src.relative_to(B)),'status':status,'source_sha256':digest,'receipt':str(rec.relative_to(B)) if rec.exists() else None,'verified_snapshot':d.get('verified_snapshot'),'axiom_lines':axioms,'elapsed_seconds':d.get('elapsed_seconds'),'current_import_objects_moved_since_receipt':moved,'scope':d.get('scope','local component or aggregate; not a whole-lane source theorem')})
o['program_modules']=rows;o['as_of_utc']=sys.argv[1] if len(sys.argv)>1 else datetime.datetime.now(datetime.timezone.utc).isoformat();p.write_text(json.dumps(o,indent=2)+'\n')
print('Proof inventory:',len(rows),'source records; no whole-package completion')
print('Unverified:',[(r['module'],r['status']) for r in rows if not r['status'].startswith('PASS')])
