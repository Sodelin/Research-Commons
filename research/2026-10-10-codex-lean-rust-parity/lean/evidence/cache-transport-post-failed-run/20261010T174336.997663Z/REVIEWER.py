#!/usr/bin/env python3
# Codex / lean_integration_successor. Read-only cache identities after the
# preserved aggregate main-name collision; no target or audit acceptance.
import pathlib,json,hashlib,shutil
import sys
sys.path.insert(0,str(pathlib.Path.cwd()))
from scripts.check_core import sha,bundle,save
R=pathlib.Path('.').resolve()
W=pathlib.Path('/tmp/rc-lean-integrated-union-1489-20261010T173948.908291Z')
E=pathlib.Path(__file__).resolve().parent
final=json.loads((W/'.build/LATEST-RUN.json').read_bytes())
assert final['status']=='INCOMPLETE_TARGET_FAILURES_PRESERVED'
assert final['kernel_checking'] and final['trust_level']==0 and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
run=pathlib.Path(final['run']);plan=json.loads((W/'CACHE-TRANSPORT-PRE-USE-PLAN.json').read_bytes());aliases=json.loads((W/'CACHE-INSTALL-ALIASES.json').read_bytes());derivation=json.loads((W/'CACHE-INSTALL-TRANSPORT-DERIVATION.json').read_bytes())
assert sha(W/'CACHE-INSTALL-ALIASES.json')==derivation['alias_manifest_sha256']
assert sha(W/'scripts/build_connected.py')==derivation['core_builder_sha256']
checks={}
def checked(p,v):
 p=pathlib.Path(p)
 if str(p) not in checks:checks[str(p)]=bundle(p)
 assert checks[str(p)]==v,p
files=0
for entry in plan['entries']:
 for row in entry['files']:
  assert sha(pathlib.Path(row['source']))==sha(pathlib.Path(row['destination']))==row['sha256']
  files+=1
context=run/'targets/current_connected/objects';records=[]
for row in aliases['entries']:
 rec=json.loads(pathlib.Path(row['original_receipt']).read_bytes());assert sha(pathlib.Path(row['original_receipt']))==sha(pathlib.Path(row['staged_receipt']))==row['receipt_sha256']
 checked(row['original_cached_object'],row['object_artifacts']);checked(row['staged_cached_object'],row['object_artifacts']);out=context/(row['module'].replace('.','/')+'.olean');checked(out,row['object_artifacts'])
 for binding in rec['direct_import_bindings'].values():checked(binding['path'],binding['artifacts'])
 records.append({'module':row['module'],'cache_key':row['cache_key'],'receipt_sha256':row['receipt_sha256'],'object_artifacts':row['object_artifacts'],'all_original_staged_installed_rehashes_pass':True})
q={'status':'PASS_READONLY_ORIGINAL_STAGED_INSTALLED_CACHE_IDENTITIES_AFTER_FAILED_AGGREGATE','failed_run':str(run),'failed_result_sha256':sha(R/'INTEGRATED-MODULAR-UNION-1489-FAILED-RESULT.json'),'entries':len(records),'original_and_staged_files_rehashed':files,'companion_bundle_paths_verified':len(checks),'records':records,'reviewer_sha256':sha(pathlib.Path(__file__)),'inputs_modified':False,'compiler_invoked':False,'target_or_owned_audit_pass_claimed':False,'failure':'Global main declaration collision between two separately accepted evaluator entrypoint modules','evidence':str(E.relative_to(R))}
save(E/'RECEIPT.json',q);save(R/'INTEGRATED-UNION-1489-FAILED-TRANSPORT-REVIEW.json',q);print(json.dumps({k:q[k] for k in ['status','entries','original_and_staged_files_rehashed','companion_bundle_paths_verified','evidence']}))
