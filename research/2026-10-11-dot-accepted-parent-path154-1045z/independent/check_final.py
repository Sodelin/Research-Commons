"""Independent final recovery evidence review. No Lean or Lake invocation."""
from pathlib import Path
import collections,gzip,hashlib,importlib.util,json,re,time
import sys
O=Path(__file__).parent;P=Path('LOCAL_EVIDENCE/parent-path-check154-20261011-1021z');R=P/'.build/runs'/sys.argv[1];B=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z');BR=B/'.build/runs/20261011T094301.633551Z';ACCEPTED_EMPTY=Path('LOCAL_EVIDENCE/g4-below-meeting-check-20261011-0643z')
spec=importlib.util.spec_from_file_location('helper',Path('LOCAL_EVIDENCE/union1575-independent-review-20261011-0400z/check_final.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);h=m.sha;rd=m.read;start=time.time();pin=sys.argv[2]
assert h(P/'DEPENDENCY-GRAPH.json')==h(R/'DEPENDENCY-GRAPH.json')==pin
g=rd(P/'DEPENDENCY-GRAPH.json')['targets']['candidate/parent-path'];mods=g['modules'];prep=rd(P/'PREPARATION.json')
for n,v in prep['scripts'].items():assert h(P/'scripts'/n)==v and (P/'scripts'/n).read_bytes()==(ACCEPTED_EMPTY/'scripts'/n).read_bytes()
assert rd(Path(sys.argv[3]))['exit_code']==0
final=rd(R/'FINAL-RECEIPT.json');assert final==rd(P/'.build/LATEST-RUN.json');assert final['status']=='PASS_ALL_REQUESTED_TARGETS' and sum(final['counts'].values())==154;assert final['targets_requested']==final['targets_passed']==['candidate/parent-path'];assert final['trust_level']==0 and final['kernel_checking'];assert final['compiler_sha256']==final['compiler_final_sha256']==m.BIN and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
trp=R/'targets/candidate_parent-path/RESULT.json';tr=rd(trp);assert tr['status']=='PASS' and tr['closure_modules']==154
by={x['module']:x for x in tr['component_receipts']};assert set(by)==set(mods)
freshpins={'GroupedParentPathCalendar':'bb59c82f0a9c0f2fdf6d68b671dd72435264227dbdac8b20682b52e195f70c5b','FirstParentJoin':'9596a8111e5558850a2323b205636d6277f771f89942494c2733e31c44b369c9','MixedParentBoundary':'274ec8727d5f04e9fa1ed89221cc4697168c31954ef5fab25ff26fa2063886f6'}
for n,v in freshpins.items():assert mods[n]['sha256']==v
prior=rd(BR/'targets/current_connected/RESULT.json');priorreceipts={x['module']:x for x in prior['component_receipts']}
for n,r in by.items():
 if n not in freshpins:assert r==priorreceipts[n]
assert len(set(by)-set(freshpins))==151
positions={n:i for i,n in enumerate(g['order'])};assert set(positions)==set(mods) and len(positions)==154
for n,v in mods.items():
 for q in v['imports']:
  if q in mods:assert positions[q]<positions[n]
  else:assert q in g['external_imports']
nr=rd(R/'NATIVE-RUNTIME-PINS.json');nf=rd(R/'NATIVE-RUNTIME-FINAL-REHASH.json');assert nf['stable'] and nf['compiler_identity_stable'];native=nr['libraries'];assert nf['hashes']=={p:v['sha256'] for p,v in native.items()}
for p,v in native.items():assert h(Path(p))==v['sha256']
entries={};indexpins={};roots={Path(r['receipt_directory'].split('/.build/')[0]) for r in by.values()}|{P}
for root in roots:
 ip=root/'trace-transport/INDEX.json';indexpins[root.name]=h(ip)
 for e in rd(ip)['entries']:entries[str(root/e['raw_path'])]=(root,e)
traces=[]
def trace(t,rp):
 root,e=entries[t['path']];assert str(root/e['receipt_path'])==str(rp);assert h(rp)==e['receipt_sha256'];assert e['receipt_status']=='PASS_FRESH_KERNEL_CHECK';a=root/e['archive_path'];assert h(a)==e['archive_sha256'] and a.stat().st_size==e['archive_bytes'];assert t['sha256']==e['raw_sha256'];z=gzip.open(a,'rb');hh=hashlib.sha256();n=0;used=set();carry=b''
 with z:
  for b in iter(lambda:z.read(1048576),b''):
   hh.update(b);n+=len(b);lines=(carry+b).split(b'\n');carry=lines.pop()
   for line in lines:
    hit=re.search(rb'calling init:\s*(/[^\s]+)',line)
    if hit:used.add(str(Path(hit.group(1).decode()).resolve()))
 assert hh.hexdigest()==t['sha256'] and n==e['raw_bytes'];traces.append({'raw_sha256':t['sha256'],'raw_bytes':n});return used
context=R/'targets/candidate_parent-path/objects';summary=[]
def receipt(r,source,imports,kind):
 rp=Path(r['receipt_directory'])/'receipt.json';assert rd(rp)=={k:v for k,v in r.items() if k not in ['cached_object','audit_output']};assert r['kind']==kind and r['status']=='PASS_FRESH_KERNEL_CHECK' and r['exit_code']==0;assert r['source_and_imports_stable'] and r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound'];assert r['native_runtime_digest']==nr['native_runtime_digest'];assert r['compiler_sha256']==m.BIN and r['mathlib_commit']==m.MATHLIB
 assert r['source_sha256']==hashlib.sha256(source).hexdigest();f=Path(r['working_directory'])/(r['module'].replace('.','/')+'.lean');assert f.read_bytes()==source
 cmd=r['command'];assert h(Path(cmd[0]))==m.BIN and cmd[1:5]==['-j1','-t0','-M4096','-Ddebug.skipKernelTC=false'];assert r['cap_memory_mib']==4096 and r['cap_seconds']==180
 assert cmd[-1]==str(f.relative_to(r['working_directory']))
 for k in ['stdout','stderr']:assert h(rp.parent/k)==r[k+'_sha256'];assert b'sorryAx' not in (rp.parent/k).read_bytes()
 assert set(r['direct_import_bindings'])==set(imports)==set(r['direct_import_artifacts'])
 for name,b in r['direct_import_bindings'].items():
  assert b['artifacts']==r['direct_import_artifacts'][name];m.bundle(Path(b['path']),b['artifacts'])
  if name in mods:assert b['artifacts']==by[name]['object_artifacts']
 if kind!='complete-owned-audit':m.bundle(Path(cmd[-2]),r['object_artifacts'])
 used=set()
 for t in r['native_loader_outputs']:used|=trace(t,rp)
 assert used==set(r['native_initialized_libraries'])
 for name in used:assert r['native_initialized_libraries'][name]==native[name]
 for a in r['auxiliary_outputs']:assert h(rp.parent/a['path'])==a['sha256'] and (rp.parent/a['path']).stat().st_size==a['bytes']
 summary.append({'module':r['module'],'source_sha256':r['source_sha256'],'receipt_sha256':h(rp),'fresh':R in rp.parents})

for n in g['order']:
 v=mods[n];source=(P/'source-store'/(v['sha256']+'.lean')).read_bytes();assert hashlib.sha256(source).hexdigest()==v['sha256'];assert m.imports(source)==v['imports'];receipt(by[n],source,v['imports'],'component');m.bundle(context/(n.replace('.','/')+'.olean'),by[n]['object_artifacts']);m.bundle(Path(by[n]['cached_object']),by[n]['object_artifacts'])
assert sum(x['fresh'] for x in summary)==final['counts']['fresh_components'];assert {x['module'] for x in summary if x['fresh']}<=set(freshpins)
agg=('\n'.join('import '+n for n in g['roots'])+'\n').encode();receipt(tr['aggregate_receipt'],agg,g['roots'],'aggregate');assert summary[-1]['fresh']
body=(P/'scripts/AuditTemplate.lean').read_text().replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]','#'+json.dumps(g['order'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"');receipt(tr['audit_receipt'],agg+body.encode(),g['roots']+['Lean.Util.CollectAxioms'],'complete-owned-audit');assert summary[-1]['fresh']
ap=Path(tr['audit_receipt']['audit_output']);assert h(ap)==sys.argv[4];audit=rd(ap);assert audit['selected_modules']==g['order'];assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules'];decl={x['name']:x for x in audit['declarations']};assert len(decl)==audit['declaration_count']==len(decl);assert sum(x['kind']=='theorem' for x in decl.values())==audit['theorem_declaration_count']==sum(x['kind']=='theorem' for x in decl.values())
for x in decl.values():assert set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}
spec2=importlib.util.spec_from_file_location('archived',Path('LOCAL_EVIDENCE/completed1585-audit-transport-20261011-1035z/audit_transport.py'));ar=importlib.util.module_from_spec(spec2);spec2.loader.exec_module(ar);assert h(Path(spec2.origin))=='02aed23bbc3d94871e981b1525932fe1cc3a080900b412e0f9a11f4772fb4a6f';basebytes=ar.read_audit(prior['audit_receipt']['audit_output']);assert hashlib.sha256(basebytes).hexdigest()=='763852d35780a7986ec812fbc96b372e4a8dfe7bdf102f8cda513930a53856e5';olddecl={x['name']:x for x in json.loads(basebytes)['declarations']}
new={n:x for n,x in decl.items() if n not in olddecl};shared=set(decl)&set(olddecl);changes=[{'name':n,'old':olddecl[n],'actual':decl[n]} for n in sorted(shared) if olddecl[n]!=decl[n]];missing=[n for n,x in olddecl.items() if x['module'] in mods and n not in decl]
compare={'base1585_shared_names':len(shared),'base1585_literal_equal':sum(decl[n]==olddecl[n] for n in shared),'base1585_missing_selected_names':missing,'base1585_deltas':changes,'new_names':new,'new_name_count':len(new),'new_theorem_rows':sum(x['kind']=='theorem' for x in new.values())};(O/'EXACT-DECLARATION-COMPARISON.json').write_text(json.dumps(compare,indent=2)+'\n')
imported=rd(R/'targets/candidate_parent-path/ACTUAL-IMPORTED-ARTIFACTS.json');groups=collections.defaultdict(dict)
for x in imported:assert h(Path(x['path']))==x['sha256'] and Path(x['path']).stat().st_size==x['bytes'];assert x['suffix'] not in groups[x['module']];groups[x['module']][x['suffix']]=x['sha256']
assert set(groups)==set(audit['all_imported_module_names'])
for n in mods:assert groups[n]==by[n]['object_artifacts']
for line in (R/'NAMESPACE-RESOLUTION-CHECKS.jsonl').read_text().splitlines():
 row=json.loads(line);assert Path(row['context'])==context
 for n,v in row['imports'].items():assert Path(v['lean_path']).resolve()==Path(v['resolved_target']).resolve();m.bundle(Path(v['lean_path']),v['artifacts'])
mask=rd(R/'EMPTY-OWNED-MATHLIB-PINS.json');assert mask['specialization_sha256']=='80a95c662ac89dbd67694a6e024d1a14899bfb27918277de6697ee55a397d3ce' and mask['graph_sha256']==pin and mask['owned_mathlib_modules']==[] and mask['complete_official_namespace_retained'] and mask['inherited_inventory_resolution_companion_kernel_and_audit_checks_unchanged'];assert h(R/'EMPTY-OWNED-MATHLIB-WRAPPER.py')==mask['specialization_sha256'];assert not any(n.startswith('Mathlib.') for n in mods)
sup_path=Path(sys.argv[5]);sup=rd(sup_path);assert sup['status']=='TERMINAL_EXIT_ZERO' and sup['exit_code']==0 and sup['limit_event'] is None;assert sup['allocation_limit_bytes']==12*2**30 and sup['free_floor_bytes']==8*2**30 and sup['per_file_hard_limit_bytes']==512*2**20;assert sup['peak_path_counted_allocated_bytes']<sup['allocation_limit_bytes'] and sup['minimum_observed_free_bytes']>=sup['free_floor_bytes']
out={'status':'PASS_EVIDENCE_PENDING_EXACT_DECLARATION_DELTA_REVIEW','graph_sha256':pin,'result_sha256':h(trp),'final_receipt_sha256':h(R/'FINAL-RECEIPT.json'),'audit_sha256':h(ap),'receipt_summary':summary,'declarations':len(decl),'theorem_rows':audit['theorem_declaration_count'],'fresh_components':final['counts']['fresh_components'],'terminal_reuse':final['counts']['cache_reuse'],'literal_accepted1585_reuse':151,'comparison_summary':{k:v for k,v in compare.items() if k not in ['new_names','base1585_deltas']},'comparison_deltas':changes,'owned_axioms':0,'nonstandard_axiom_rows':0,'missing_modules':0,'imported_modules':len(groups),'imported_artifact_records':len(imported),'actual_imported_artifacts_sha256':h(R/'targets/candidate_parent-path/ACTUAL-IMPORTED-ARTIFACTS.json'),'native_traces':traces,'trace_index_sha256':indexpins,'supervisor_sha256':h(sup_path),'reviewer_compiler_invoked':False,'elapsed_seconds':time.time()-start,'distinct_files_hashed':len(m.MEMO),'bytes_hashed':m.hashed_bytes};(O/'FINAL-EVIDENCE-RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['receipt_summary','native_traces','comparison_deltas']},indent=2));print('DELTAS',[(x['name'],[k for k in x['old'] if x['old'][k]!=x['actual'][k]]) for x in changes])
