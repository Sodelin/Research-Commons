"""Reproduce the classified all68 G2 diagnostic after `lake build connected`.
Uses the same reviewed invocation implementation and a new preserved run.
This adapter is supplied for reproduction; original executed invocations are in evidence.
"""
from pathlib import Path
import hashlib,importlib.util,json,subprocess,sys
P=Path(__file__).resolve().parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
prior=read(P/'.build/LATEST-RUN.json');assert prior['status']=='PASS_ALL_REQUESTED_TARGETS';run=Path(prior['run']);target=read(run/'targets/targeted_G2-current-complete/RESULT.json');assert target['status']=='PASS';context=run/'targets/targeted_G2-current-complete/objects';census=Path(target['audit_receipt']['audit_output'])
spec=importlib.util.spec_from_file_location('reviewed_builder',P/'scripts/build_connected.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);b=mod.Builder();receipts=[]
for name in ['G2CurrentSafetyClassification','G2CurrentAll68ClassifiedDAGAudit']:
 source=P/(name+'.lean');imports=[m for l in source.read_text().splitlines()if l.startswith('import ')for m in l[7:].split()]
 rec,obj=b.invoke(name,source,True,imports,context,180,4096,'reproduced-current-G2-diagnostic');receipts.append(rec)
 if not obj:
  mod.save(b.run/'FINAL-RECEIPT.json',{'status':'FAILED_DIAGNOSTIC','receipts':receipts});raise SystemExit(1)
validation=b.run/'FULL-DAG-VALIDATION.json';cmd=[sys.executable,str(P/'verify_dag_audit_v2.py'),str(Path(receipts[-1]['receipt_directory'])/'stdout'),'--modules',str(P/'ALL-G2-68.json'),'--census',str(census),'--classification',str(P/'RUNTIME-COMPANION-CLASSIFICATION.json'),'--output',str(validation)]
r=subprocess.run(cmd,capture_output=True,text=True,timeout=180);(b.run/'VALIDATOR.stdout').write_text(r.stdout);(b.run/'VALIDATOR.stderr').write_text(r.stderr)
safety=read(Path(receipts[0]['working_directory'])/'G2-SAFETY-CENSUS.json');wide=read(census);by={x['name']:x for x in wide['declarations']};assert set(by)=={x['name']for x in safety['declarations']}
for x in safety['declarations']:
 w=by[x['name']];assert x['kind']==w['kind']and x['module']==w['module'];assert all(set(x[k])==set(w[k])for k in ['axioms','type_references','body_references'])
partials=[x for x in safety['declarations']if x['partial']];assert len(partials)==14 and not any(x['unsafe']for x in safety['declarations']);assert all(x['base_exists']and not x['base_unsafe']and not x['base_partial']and x['same_base_type']for x in partials)
names={x['name']for x in partials};assert not any(((set(x['type_references'])|set(x['body_references']))&names)-{x['name']}for x in safety['declarations'])
final={str(p):mod.sha(p)for p in b.native_paths};stable=all(final[p]==v['sha256']for p,v in b.native_runtime.items());mod.save(b.run/'NATIVE-RUNTIME-FINAL-REHASH.json',{'stable':stable,'hashes':final})
result={'status':'PASS_REPRODUCED_CURRENT_G2_AUDIT'if r.returncode==0 and stable else 'FAILED_VALIDATION','diagnostic_receipts':receipts,'validator_exit_code':r.returncode,'native_runtime_final_rehash_stable':stable,'run':str(b.run),'runtime_execution_verified':False}
if validation.exists():result['validation']=read(validation)
mod.save(b.run/'FINAL-RECEIPT.json',result);print(result['status']);raise SystemExit(0 if result['status'].startswith('PASS_')else 1)
