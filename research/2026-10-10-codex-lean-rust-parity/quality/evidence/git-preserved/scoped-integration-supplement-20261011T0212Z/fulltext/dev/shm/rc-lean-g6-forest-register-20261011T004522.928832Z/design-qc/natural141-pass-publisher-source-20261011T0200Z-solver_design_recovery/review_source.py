"""AST/payload source-only publisher QC; no target execution or Git."""
import ast, copy, hashlib, json, os
from pathlib import Path
from datetime import datetime,timezone
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
N=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
B=W/'metadata/git-evidence-publication'
Q=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 assert sha(p)==h,str(p)
 return {'path':str(p),'bytes':p.stat().st_size,'sha256':h}
parent=B/'publish_forest101_fixed_shmem_to_git_20261011.py'
new=B/'publish_natural141_pass_fixed_shmem_to_git_20261011.py'
pins=[pin(parent,'09bcaebd946eafdb0c8473f5a0b49c0b517c9f39e82253604607bed47c228482'),pin(new,'ccb2353c8c02323e0840215772d3a10ffbd406fa9c1bb0865d0c71d41071eea3'),pin(W/'design-qc/forest101-git-publisher-20261011T0107Z-solver_design_recovery/FOREST101-GIT-PUBLISHER-STATIC-QC-ATTEMPT1.json','95f10f77bbd80c35f344abea1886f19ace5c7a0c1a7af74a3fbd7ad85243379b')]
a,z=ast.parse(parent.read_bytes()),ast.parse(new.read_bytes())
assert len(a.body)==len(z.body)
allowed={'RESULT','RESULT_SHA','EXPORT','PREFIX','OUT'}
bindings={}
for x,y in zip(a.body,z.body):
 if isinstance(x,ast.Assign) and isinstance(y,ast.Assign) and len(x.targets)==len(y.targets)==1 and isinstance(x.targets[0],ast.Name) and isinstance(y.targets[0],ast.Name) and x.targets[0].id==y.targets[0].id and x.targets[0].id in allowed:
  bindings[x.targets[0].id]=copy.deepcopy(y.value);x.value=copy.deepcopy(y.value)
assert set(bindings)==allowed
counts=[v for v in ast.walk(a) if isinstance(v,ast.Assert) and ast.unparse(v.test)=='len(rows) == 66']
assert len(counts)==1
counts[0].test.comparators[0]=ast.Constant(value=73)
assert ast.dump(a)==ast.dump(z),'No broader publisher method/guard delta permitted'
literal=lambda n:n.value if isinstance(n,ast.Constant) else n.args[0].value
r=N/'G6-NATURAL-COMMON-FACTORIZATION-PROOF141-20261011T014055.249073Z-RESULT.json'
pins.append(pin(r,'6db53e2eba1679cae6841cf1e2c6ffc37cd3d985873d0f8d73a8e2c17094bf30'))
result=json.loads(r.read_bytes());export=Path(result['complete_lossless_export_original'])
expect={'RESULT':str(r),'RESULT_SHA':pins[-1]['sha256'],'EXPORT':str(export),'PREFIX':'research/2026-10-10-codex-lean-rust-parity/lean/evidence/git-preserved/natural141-pass-20261011T014055.249073Z','OUT':str(B/'NATURAL141-PASS-PUBLICATION.json')}
assert all(literal(bindings[k])==v for k,v in expect.items())
assert result['status']=='PASS_ALL_REQUESTED_TARGETS' and result['packet_distribution_complete'] is False
assert (export/'PRESERVATION-MANIFEST.json').read_bytes()==r.read_bytes()
saved=N/'design-qc/natural141-saved-20261011T0152Z-solver_design_recovery/NATURAL141-SAVED-QC-ATTEMPT2.json'
pins.append(pin(saved,'6ed6b44b114704fb39a236a126b1f2a36197a6b443d53da5a2816a7efa5a19c4'))
assert json.loads(saved.read_bytes())['status'].startswith('PASS_SAVED_NATURAL141_')
paths=set()
for row in result['preserved_files']:
 rel=Path(row['path']);assert not rel.is_absolute() and '..' not in rel.parts
 p=export/rel;assert not p.is_symlink() and sha(p)==row['sha256'] and p.stat().st_size==row['bytes'];paths.add(p)
assert len(paths)==71
paths|={export/'PRESERVATION-MANIFEST.json',export/'COMPRESSED-DISTRIBUTIONS.json'}
assert len(paths)==73 and set(p for p in export.rglob('*') if p.is_file())==paths
rows=[]
for p in sorted(paths):
 assert not p.is_symlink()
 data=p.read_bytes();assert data[:4]!=b'\x7fELF' and not p.name.endswith(('.rlib','.a','.so','.olean'))
 rows.append({'original_path':str(p),'git_tree_path':expect['PREFIX']+'/'+str(p.relative_to(export)),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'git_blob':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()})
payload=sum(v['bytes'] for v in rows);assert payload==4672092
pool=Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z');index=Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
assert pool.is_symlink() and pool.resolve()==W/'metadata/git-object-pool-preserved-20261011'
size=sum(p.stat().st_size for p in pool.rglob('*') if p.is_file())
free=lambda p:os.statvfs(p).f_bavail*os.statvfs(p).f_frsize
capacity={'object_pool_content_bytes':size,'payload_bytes':payload,'per_file_allowance_bytes':73*4096,'projected_object_pool_content_bound_bytes':size+payload+73*4096,'object_pool_64MiB_before_check':size+payload+73*4096<64*1024*1024,'index_bytes':index.stat().st_size,'tmp_free_bytes':free('/tmp'),'tmp_payload_index_reserve_check':free('/tmp')>payload+73*4096+index.stat().st_size+2*1024*1024,'overlay_free_bytes':free('/workspace'),'overlay_8MiB_floor_check':free('/workspace')>8*1024*1024}
report={'schema':'natural141_pass_publisher_source_only_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'status':'PASS_SOURCE_ONLY_EXACT_NATURAL141_PUBLISHER_BINDING_DERIVATIVE','reviewer_sha256':sha(Path(__file__)),'pins':pins,'whole_ast_equal_except_five_bindings_and_66_to_73':True,'bindings':expect,'payload_rows':rows,'payload_files':73,'payload_bytes':payload,'compiled_payload_files':0,'dated_capacity_observation':capacity,'qualification':['Source-only gate. Root must still authenticate absent paths/index entries, result/payload/source identity, current capacity, and full blob/index readback at execution.','Complete fixed-shmem export is preserved. Original packet_distribution_complete:false remains historical and unchanged; evidence publication does not widen accepted1504 or native/source/physical context claims.','Publisher retains all accepted09b floor/object/index checks and preexisting-index equality. No Git, publisher, producer, helper, or compiler invoked by reviewer.'],'git_commands_or_target_producers_started':0,'overlay_writes':0}
out=Q/'NATURAL141-PASS-PUBLISHER-SOURCE-QC-ATTEMPT1.json'
with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({'receipt':str(out),'sha256':sha(out),'status':report['status'],'capacity':capacity}))
