from pathlib import Path
import hashlib,json,importlib.util,time,shutil
P=Path('LOCAL_EVIDENCE/connected-union1588-20261011-1049z');B=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z');A=Path('LOCAL_EVIDENCE/parent-path-check154-20261011-1021z');G7=Path('LOCAL_EVIDENCE/g7-restoration-check-20261011-0842z');O=Path(__file__).parent
spec=importlib.util.spec_from_file_location('u','LOCAL_EVIDENCE/union1575-independent-review-20261011-0400z/check_final.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u);rd=lambda p:json.loads(p.read_bytes());start=time.time()
u.check(P/'DEPENDENCY-GRAPH.json','534564494039d127c137a1ec2a9010fd5250a871dead60dc2d5cf48ae1341919');g=rd(P/'DEPENDENCY-GRAPH.json');old=rd(B/'DEPENDENCY-GRAPH.json');t=g['targets']['current/connected'];mods=t['modules'];before=old['targets']['current/connected']['modules'];added={'GroupedParentPathCalendar':'bb59c82f0a9c0f2fdf6d68b671dd72435264227dbdac8b20682b52e195f70c5b','FirstParentJoin':'9596a8111e5558850a2323b205636d6277f771f89942494c2733e31c44b369c9','MixedParentBoundary':'274ec8727d5f04e9fa1ed89221cc4697168c31954ef5fab25ff26fa2063886f6'}
assert len(mods)==1588 and set(mods)-set(before)==set(added)
for n,d in before.items():assert mods[n]==d
for n,h in added.items():assert mods[n]['sha256']==h
for label,body in old['targets'].items():assert g['targets']['history/accepted1585' if label=='current/connected' else label]==body
assert g['targets']['candidate/parent-path']==rd(A/'DEPENDENCY-GRAPH.json')['targets']['candidate/parent-path']
assert set(g['targets'])==set(old['targets'])|{'history/accepted1585','candidate/parent-path'}
fixture=g['targets']['fixture/g7-population'];assert 'G7OriginalPopulationFixture' not in mods and fixture==old['targets']['fixture/g7-population'];allmods=dict(mods);allmods.update(fixture['modules']);assert len(allmods)==1589
for n,d in allmods.items():
 p=P/'source-store'/(d['sha256']+'.lean');u.check(p,d['sha256']);assert u.imports(p.read_bytes())==d['imports']
pos={n:i for i,n in enumerate(t['order'])};assert len(pos)==1588 and set(pos)==set(mods)
for n,d in mods.items():
 for q in d['imports']:
  if q in mods:assert pos[q]<pos[n]
  else:assert q in t['external_imports']
assert {n for n in mods if n.startswith('Mathlib.')}=={'Mathlib.Data.FinEnum','Mathlib.Algebra.MvPolynomial.Polynomial','Mathlib.Algebra.MvPolynomial.Funext','Mathlib.Analysis.Convex.Caratheodory'}
prep=rd(P/'PREPARATION.json');assert prep['graph_sha256']==u.sha(P/'DEPENDENCY-GRAPH.json')
for n,h in prep['scripts'].items():u.check(P/'scripts'/n,h);assert (P/'scripts'/n).read_bytes()==(B/'scripts'/n).read_bytes()
for n,h in u.PINS.items():u.check(P/n,h)
for n in ['lakefile.lean','lake-manifest.json','lean-toolchain']:assert (P/n).read_bytes()==(B/n).read_bytes()
auth=rd(P/'AUTHENTICATED-ADDITIVE-PREFLIGHT.json');assert auth['selected_expected_reuse']==1588 and auth['isolated_fixture_reuse']==1 and not auth['foreign_compiled_objects_admitted'];rows=auth['records'];assert len(rows)==1589;by={x['module']:x for x in rows};assert set(by)==set(allmods)
accepted={x['module']:x for x in rd(B/'.build/runs/20261011T094301.633551Z/targets/current_connected/RESULT.json')['component_receipts']}
for x in rd(A/'.build/runs/20261011T104206.717245Z/targets/candidate_parent-path/RESULT.json')['component_receipts']:
 if x['module'] in added:accepted[x['module']]=x
for x in rd(G7/'.build/runs/20261011T084427.511721Z/targets/fixture_g7-population/RESULT.json')['component_receipts']:
 if x['module']=='G7OriginalPopulationFixture':accepted[x['module']]=x
assert set(accepted)==set(allmods);nimports=0;digests=set()
for n,row in by.items():
 rp=P/'.build/cache'/row['key']/'receipt.json';u.check(rp,row['receipt_sha256']);assert rp.read_bytes()==Path(row['original_receipt_path']).read_bytes();r=rd(rp);assert r==accepted[n]
 assert r['module']==n and r['source_sha256']==allmods[n]['sha256']==row['source_sha256'];assert r['kind']=='component' and r['status']=='PASS_FRESH_KERNEL_CHECK' and r['exit_code']==0;assert r['source_and_imports_stable'] and r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound'];assert r['compiler_sha256']==u.BIN and r['mathlib_commit']==u.MATHLIB
 cmd=r['command'];u.check(Path(cmd[0]),u.BIN);assert cmd[1:3]==['-j1','-t0'] and '-Ddebug.skipKernelTC=false' in cmd;cap=(600,6144) if n=='ThetaCertificate5' else (180,4096);assert (r['cap_seconds'],r['cap_memory_mib'])==cap and cmd[3]=='-M'+str(cap[1]);assert set(r['direct_import_bindings'])==set(allmods[n]['imports']);u.bundle(Path(r['cached_object']),r['object_artifacts']);u.bundle(rp.parent/'artifact.olean',r['object_artifacts']);assert row['object_sha256']==r['object_sha256']
 for q,b in r['direct_import_bindings'].items():
  u.bundle(Path(b['path']),b['artifacts']);assert b['sha256']==r['direct_import_sha256'][q] and b['artifacts']==r['direct_import_artifacts'][q]
  if q in accepted:assert b['artifacts']==accepted[q]['object_artifacts']
  nimports+=1
 k={'module':n,'source':r['source_sha256'],'compiler':u.BIN,'mathlib':u.MATHLIB,'trust':0,'kernel_check':True,'imports':r['direct_import_artifacts'],'native_runtime_digest':r['native_runtime_digest'],'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
 if n=='ThetaCertificate5':k['resource_exception']={'memory_mib':6144,'seconds':600}
 assert hashlib.sha256(json.dumps(k,sort_keys=True).encode()).hexdigest()==row['key'];digests.add(r['native_runtime_digest'])
 for path,v in r['native_initialized_libraries'].items():u.check(Path(path),v['sha256'])
assert len(digests)==1
budget=rd(P/'STAGING-BUDGET-RECEIPT.json');assert budget['status']=='PASS_HARD_40MIB_PREPARATION_WITHIN_PRIOR64MIB_MAX' and budget['preparation_cap']==40*2**20;assert budget['new_regular_file_allocation']<budget['preparation_cap'] and budget['observed_consumption']<budget['preparation_cap'];assert budget['launch_threshold']==20*2**30 and not budget['compiler_invoked'];assert prep['selected_mathematical_source_bytes']==sum((P/'source-store'/(v['sha256']+'.lean')).stat().st_size for v in mods.values());assert prep['isolated_fixture_source_bytes']==10203;assert prep['source_bytes']==prep['all_distinct_staged_source_bytes']==sum((P/'source-store'/(v['sha256']+'.lean')).stat().st_size for v in allmods.values())==prep['selected_mathematical_source_bytes']+prep['isolated_fixture_source_bytes'];assert prep['new_source_bytes']==sum((P/'source-store'/(h+'.lean')).stat().st_size for h in added.values());assert not (P/'.build/LATEST-RUN.json').exists()
free=shutil.disk_usage(P).free;mem=int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024;assert free>20*2**30 and mem>=7*2**30
r={'status':'PASS_INDEPENDENT_EXACT1588_PREFLIGHT_NO_COMPILER','graph_sha256':u.sha(P/'DEPENDENCY-GRAPH.json'),'selected_modules':1588,'old_module_records_literal_preserved':1585,'all_old_targets_literal_preserved':True,'selected_reused_accepted_receipts':1588,'isolated_fixture_receipts':1,'total_source_bodies_and_cache_contexts':1589,'fresh_unchecked_components':0,'source_additions':added,'direct_import_bundles_checked':nimports,'native_runtime_digests':sorted(digests),'unchanged_four_owned_mathlib_wrapper':True,'staging_budget':budget,'observed_free_bytes':free,'observed_available_memory_bytes':mem,'required_explicit_target':'current/connected','compiler_invoked':False,'hash_checked_files':len(u.MEMO),'hash_checked_bytes':u.hashed_bytes,'elapsed_seconds':time.time()-start};(O/'PREFLIGHT-RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
