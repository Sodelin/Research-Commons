"""Source-only protocol inspection; does not import or invoke the publisher."""
from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,os,traceback
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
Q=W/'design-qc/static1573-and-readout-gap-20261011T0230Z-solver_design_recovery'
S=W/'metadata/git-evidence-publication/preserve_final_checkpoint_text_blobs_20261011.py'
C=Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/RESOURCE-AND-RUN-PLAN.json')
def require(t,s):
 if not t:raise AssertionError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def check():
 data=S.read_bytes();tree=ast.parse(data);text=data.decode()
 imports=[]
 for n in tree.body:
  if isinstance(n,ast.Import):imports.extend(x.name for x in n.names)
 require(set(imports)=={'os','json','pathlib','subprocess','hashlib','datetime'},'bounded standard-library imports')
 require('unlink(' not in text and 'rmtree(' not in text and 'rename(' not in text and 'exec(' not in text and 'eval(' not in text,'no target execution or deletion/redirect')
 expected_calls={'ls-files','hash-object','cat-file','update-index','show'}
 actual={n.args[0].value for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='git' and n.args and isinstance(n.args[0],ast.Constant)}
 require(actual==expected_calls,'fixed limited Git protocol calls')
 for snippet in ["b.decode('utf-8')", "assert not b.startswith(b'\\x7fELF')", "assert len(b)==row['bytes'] and sha(b)==row['sha256']", "assert 30<=len(rows)<=100", "payload<6*1024**2", "reserve=payload+len(rows)*4096+4*1024**2", "pool()+reserve<96*1024**2", "config['scratch_abort_bytes']==2013265920", "config['scratch_hard_limit_bytes']==2147483648", "config['memory_abort_bytes']==16106127360", "len(config['allocation_roots'])==26", "free('/workspace')>8*1024**2", "git('cat-file','blob',blob)==b", "('100644 '+x['git_blob']", "git('update-index','--skip-worktree'", "not (R/row['git_tree_path']).exists()", "x.split(b'\\t',1)[1] not in added)==before", "git('show',':'+row['git_tree_path'])==pathlib.Path(row['source_path']).read_bytes()"]:
  require(snippet in text,'source protocol retained '+snippet)
 configdata=C.read_bytes();require(sha(configdata)=='2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c','canonical26-root config')
 config=json.loads(configdata);roots=config['allocation_roots'];require(len(roots)==len(set(roots))==26 and all(Path(x).is_dir() for x in roots),'26 unique present approved roots')
 require((config['scratch_hard_limit_bytes'],config['scratch_abort_bytes'],config['memory_abort_bytes'])==(2147483648,2013265920,16106127360),'unchanged exact global caps')
 pool=Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z');require(pool.is_symlink() and pool.resolve()==W/'metadata/git-object-pool-preserved-20261011','logicalpool alreadycountedshmem')
 require((W/'metadata/git-evidence-publication/FINAL-CHECKPOINT-FULLTEXT-PUBLICATION.json').exists() is False,'source review before publisher invocation')
 return {'source_path':str(S),'source_bytes':len(data),'source_sha256':sha(data),'canonical_prelaunch_resource_config_path':str(C),'canonical_prelaunch_resource_config_bytes':len(configdata),'canonical_prelaunch_resource_config_sha256':sha(configdata),'canonical_allocation_roots_sha256':sha(json.dumps(roots,separators=(',',':')).encode()),'four_fixed_caps':{'Git_evidence_pool_bytes':96*1024**2,'global_scratch_hard':2147483648,'global_scratch_abort':2013265920,'nonreclaim_memory_abort':16106127360},'bounded_payload_bytes':6*1024**2,'final_row_count_bounds':[30,100],'future_tree_reserve_bytes':4*1024**2,'no_whole_main_AST_identity_claim':True,'full_fixed_text_blob_index_and_old_stage_preservation_protocol_checked':True,'scope':'Source protocol review for one root-owned frozen UTF8 metadata set. This is not untrusted manifest acceptance, source/kernel/cache admission or authorization for an unknown input set.','required_frozen_manifest_prelaunch_gate':['Authenticate exact manifest bytes/SHA and publisher SHA; include this source and immutable full QA/correction files as regular text rows.','Bind resource_config to the canonical path/SHA and exact ordered26 unique present roots above; script checks numeric caps/count but does not itself authenticate config SHA/root identities.','Authenticate every regular source row SHA/size, unique genuinely absent physical/index tree path inside the new evidence prefix, and30..100 final rows including runtime-appended inputmanifest.','Remeasure actual pool+payload+per-file+4MiB reserve, counted26-root allocation, nonreclaim memory, index/tmp and8MiB overlay floors immediately before execution.','Root alone mutates Git/index/refs; preserve incomplete outcomes and original evidence if a check stops. Read back actual full blobs/index entries afterward.'],'tmp_reserve_qualification':'Logical object pool resolves inside counted WF; object payload is funded there, while /tmp preflight covers live index rewrite plus2MiB. If object storage changes, re-gate.','future_tree_reserve_qualification':'A funded4MiB allocation allowance, not a theorem that arbitrary future write-tree fits. Root rechecks actual capacities at checkpoint.','reviewer_target_import_or_invocation_Git_command_compiler_producer_or_source_edit':False}
report={'schema':'independent_final_metadata_publisher_source_protocol_qc_v1','contributor':'Codex solver_design_recovery','utc':datetime.now(timezone.utc).isoformat(),'reviewer_path':str(Path(__file__)),'reviewer_sha256':sha(Path(__file__).read_bytes())}
try:report['checks']=check();report['status']='PASS_SOURCE_PROTOCOL_ONLY_REQUIRES_FIXED_MANIFEST_AND_RESOURCE_PRELAUNCH_GATE'
except Exception as e:report['status']='FAIL_OWN_REVIEWER';report['error']=str(e);report['traceback']=traceback.format_exc()
out=Q/'FINAL-CHECKPOINT-PUBLISHER-SOURCE-PROTOCOL-QC-ATTEMPT1.json';require(not out.exists(),'immutable own output');out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n');size=sum(p.stat().st_size for p in Q.iterdir() if p.is_file());print(json.dumps({'status':report['status'],'path':str(out),'sha256':sha(out.read_bytes()),'bytes':out.stat().st_size,'source_sha256':report.get('checks',{}).get('source_sha256'),'directory_bytes':size,'error':report.get('error')}));require(size<128*1024,'same countedQunder128KiB')
