import gzip,hashlib,json,subprocess,tarfile
from pathlib import Path
repo=Path('commons').resolve(); out=repo/'research/2026-10-10-codex-desktop-g3-union'
p=repo/'research/2026-10-10-codex-lean-rust-parity'
h=p/'lean/evidence/proof-extensions/history-accepted-union-1497/20261010T204542.182773Z/run-20261010T204745.833238Z'
paths=subprocess.check_output(['git','-C',str(repo),'ls-tree','-r','--name-only','HEAD',str(h.relative_to(repo)).replace('\\','/')],text=True).splitlines()
auditpath=next(x for x in paths if x.endswith('/work/AUDIT-RESULT.json.gz'))
raw=subprocess.check_output(['git','-c','core.longpaths=true','-C',str(repo),'show','HEAD:'+auditpath]); base=json.loads(gzip.decompress(raw))
dot=repo/'research/2026-10-10-dot-modular-lean-reuse-handoff-1448z/g3-fixed-residue-critical-bridge-1522z/evidence/AUDIT-RESULT.json'
g3=json.loads(dot.read_bytes())
old={r['name']:r for r in base['declarations']}; new={r['name']:r for r in g3['declarations']}
shared=set(old)&set(new)
assert len(old)==100764 and len(new)==1087 and len(shared)==367
assert all(old[n]==new[n] for n in shared)
add={n:r for n,r in new.items() if n not in shared}
assert all(r['module'] not in base['selected_modules'] for r in add.values())
report={'status':'PASS_STATIC_IDENTITY_PREFLIGHT_NOT_A_BUILD','owned_base_declarations':len(old),'g3_declarations':len(new),'shared_identical_declarations':len(shared),'new_name_collisions':0,'prospective_owned_declarations':len(old)+len(add),'prospective_theorems':base['theorem_declaration_count']+sum(r['kind']=='theorem' for r in add.values()),'baseline_audit_gzip_sha256':hashlib.sha256(raw).hexdigest(),'baseline_audit_uncompressed_bytes':len(gzip.decompress(raw)),'dot_audit_sha256':hashlib.sha256(dot.read_bytes()).hexdigest(),'compiled_objects_available_from_packets':0}
(out/'STATIC-PREFLIGHT.json').write_text(json.dumps(report,indent=2)+'\n')
register=p/'reuse/HISTORY-RECONCILIATION-20261010T205629Z.json'; data=json.loads(register.read_bytes())
manifest=json.loads((out/'SOURCE-MANIFEST.json').read_bytes())
mods={r['module']:r['sha256'] for r in manifest['modules']}; rows={}
for oid,r in data['obligations'].items():
    bindings=[]
    for b in r['frozen_provider_bindings']:
        exact=[m for m,s in mods.items() if s==b['sha256']]
        bindings.append({'original_source_path':b['path'],'sha256':b['sha256'],'declared_endpoints':b.get('declarations',[]),'exact_source_modules_in_union':exact,'inherited_accepted_contexts':b.get('accepted_exact_context_matches',{}),'union_verification':'PENDING_FRESH_AGGREGATE_AND_AUDIT'})
    rows[oid]={'original_goal':r['original_goal'],'original_obligation':r['original_obligation'],'inherited_status':r['current_status'],'inherited_acceptance_scope':r['acceptance_scope'],'accepted_provider_bindings':bindings,'remaining_interface':r['remaining_interface']}
assert len(rows)==65
rows['G3-GLOBAL']['additive_provider']={'module':'G3ActualFixedResidueCriticalFiniteness','sha256':mods['G3ActualFixedResidueCriticalFiniteness'],'endpoint':'GProgram.G3.CriticalCertificates.actual_fixed_residue_strict_critical_finite','accepted_external_context':{'modules':70,'declarations':1087,'theorems':788,'audit_sha256':report['dot_audit_sha256']},'desktop_union_status':'PENDING_FRESH_AGGREGATE_AND_AUDIT','scope':'Supplied real r>0; strict source pairs in the original six-exponent normalWeight model. No effective enumeration, parameter acquisition, source-size bound or whole-fibre YES/NO recognizer.'}
mapdata={'schema':'additive_desktop_provider_obligation_map_v1','basis_path':str(register.relative_to(repo)).replace('\\','/'),'basis_sha256':hashlib.sha256(register.read_bytes()).hexdigest(),'original_register_unchanged':True,'obligation_count':65,'all_ids_preserved':True,'status':'STATIC_MAP_UNION_UNVERIFIED','obligations':rows,'coordination':'Desktop G3 owner; six G7 continuation consumers assigned separately to cloud at 4ca16003ad9caeb75875e441d0068844d0c50a7c; no prospective 1567 claim.'}
(out/'PROVIDER-OBLIGATION-MAP.json').write_text(json.dumps(mapdata,indent=2)+'\n')
print(json.dumps(report))
