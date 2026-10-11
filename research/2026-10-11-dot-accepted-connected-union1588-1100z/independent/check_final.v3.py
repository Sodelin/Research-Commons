#!/usr/bin/env python3
"""Independent read-only source/evidence verifier. Never invokes Lean, Lake, or an owner checker."""
import argparse, collections, gzip, hashlib, json, re, time
from pathlib import Path
ROOT=Path('LOCAL_EVIDENCE/connected-union1588-20261011-1049z')
BASE1585=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z')
PARENT154=Path('LOCAL_EVIDENCE/parent-path-check154-20261011-1021z')
BASE1581=Path('LOCAL_EVIDENCE/connected-union1581-20261011-0705z')
G7=Path('LOCAL_EVIDENCE/g7-restoration-check-20261011-0842z')
NEW_MODULES={'GroupedParentPathCalendar','FirstParentJoin','MixedParentBoundary'}
BASE1575=Path('LOCAL_EVIDENCE/connected-union1575-20261011-0358z')
SMOOTH=Path('LOCAL_EVIDENCE/g3-smoothness-check-20261011-0427z')
G46=Path('LOCAL_EVIDENCE/g46-frozen-check-20261011-0608z')
SUPPORT=Path('LOCAL_EVIDENCE/g4-below-meeting-check-20261011-0643z')
ACCEPTED_RECEIPTS={}
BASE=Path('LOCAL_EVIDENCE/connected-union1570-g4span-20261011-0212z')
OLDEST=Path('LOCAL_EVIDENCE/connected-union1568-20261010-2318z')
G4=Path('LOCAL_EVIDENCE/g4-span-check-20261011-0146z')
PRIOR=Path('LOCAL_EVIDENCE/g34-public-recovery-20261010-2309z')
OUT=Path(__file__).resolve().parent
RUN=None
GRAPH=None
BIN='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
SUFFIXES=['.olean','.olean.private','.olean.server','.ilean','.ir']
PINS={'scripts/build_connected.py':'13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc', 'scripts/build_desktop.py':'a9d4d3f210eec5d01152661ca360e12cac295d8fdb1286ce99f548f307daf941','scripts/AuditTemplate.lean':'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a','scripts/build_with_authenticated_overlay.py':'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc','scripts/build_with_mathlib_overlay.py':'09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0','scripts/run_union.py':'fbacfbb57330651053acc1848c6b1c31fdcda121b6f8c4cadf088b45617692ee','scripts/completed_trace_transport.py':'d9537eafeb4905c5e757890a0dc3e428991ccb485969c27e44aea9af0af121e6'}
MEMO={}; hashed_bytes=0

def digest_bytes(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
def sha(p):
 global hashed_bytes
 p=p.resolve(strict=True);s=p.stat();key=(str(p),s.st_size,s.st_mtime_ns,s.st_ctime_ns)
 if key not in MEMO:
  h=hashlib.sha256()
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1048576),b''):h.update(b);hashed_bytes+=len(b)
  MEMO[key]=h.hexdigest()
 return MEMO[key]
def check(p,w):
 actual=sha(p);assert actual==w,('hash mismatch',str(p),actual,w)
def companion(base,s):return base.with_suffix(s) if s in ['.olean','.ilean','.ir'] else Path(str(base)+s[len('.olean'):])
def bundle(p,expected):
 actual={s:sha(companion(p,s)) for s in SUFFIXES if companion(p,s).is_file()}
 assert actual==expected,('companion mismatch',str(p),actual,expected)
def imports(b):
 # Strip nested Lean block comments and line comments while retaining line breaks.
 s=b.decode();o=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    o.append('\n' if s[i]=='\n' else ' ');i+=1
  elif not string and s.startswith('/-',i):depth=1;i+=2
  elif not string and s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:
   if s[i]=='"' and (i==0 or s[i-1]!='\\'):string=not string
   o.append(s[i]);i+=1
 assert depth==0
 return [t for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',''.join(o),re.M) for t in line.split()]

def final_check(g,expected):
 terminals=[(p,read(p)) for p in ROOT.glob('LAKE*-TERMINAL.json')];passing=[(p,v) for p,v in terminals if v.get('exit_code')==0];assert len(passing)==1
 terminal_path,terminal=passing[0];launch=read(terminal_path.with_name(terminal_path.name.replace('TERMINAL','LAUNCH')));assert launch['review_sha256']=='114de5b8b5c011f0b07bed432754b9989421087ad8c15e3ec28bbffb6a52a36a';assert sha(OUT/'INDEPENDENT-PREFLIGHT-REVIEW.md')==launch['review_sha256'];assert read(OUT/'PREFLIGHT-RESULT.json')['graph_sha256']==GRAPH
 assert launch['command'][1:]==['test','--','current/connected'] and all(terminal[k]==v for k,v in launch.items())
 assert launch['free_bytes']>20*2**30 and launch['available_ram']>=7*2**30
 f=read(RUN/'FINAL-RECEIPT.json');assert read(ROOT/'.build/LATEST-RUN.json')==f
 assert f['status']=='PASS_ALL_REQUESTED_TARGETS' and f['targets_requested']==f['targets_passed']==['current/connected']
 assert f['graph_sha256']==GRAPH and f['trust_level']==0 and f['kernel_checking'] is True
 assert f['compiler_sha256']==f['compiler_final_sha256']==BIN and f['mathlib_commit']==MATHLIB
 assert f['native_runtime_final_rehash_stable'] and f['compiler_identity_stable']
 assert sum(f['counts'].values())==1588,f['counts']
 assert not f['fresh_every_selected_component_context_in_this_run']
 pins=read(RUN/'RUNNER-AND-INPUT-PINS.json')
 check(RUN/'BUILDER.py',pins['builder_sha256']);check(RUN/'AuditTemplate.lean',pins['audit_template_sha256'])
 trp=RUN/'targets/current_connected/RESULT.json';tr=read(trp);assert tr['status']=='PASS' and tr['closure_modules']==1588
 nr=read(RUN/'NATIVE-RUNTIME-PINS.json');nf=read(RUN/'NATIVE-RUNTIME-FINAL-REHASH.json');assert nf['stable'] and nf['compiler_identity_stable'] and nf['compiler_sha256']==BIN
 native=nr['libraries'];assert nf['hashes']=={p:v['sha256'] for p,v in native.items()}
 assert digest_bytes(json.dumps(nf['hashes'],sort_keys=True).encode())==nr['native_runtime_digest']==f['native_runtime_digest']
 for p,v in native.items():check(Path(p),v['sha256'])
 index_snapshots={};entries={};new_entries=set()
 for origin in [OLDEST,G4,BASE,BASE1575,SMOOTH,G46,SUPPORT,BASE1581,G7,BASE1585,PARENT154,ROOT]:
  ip=origin/'trace-transport/INDEX.json'
  if not ip.exists():
   assert origin==ROOT;continue
  ib=ip.read_bytes();ix=json.loads(ib);index_snapshots[ip]=ib
  for e in ix['entries']:
   raw=str(origin/e['raw_path']);assert raw not in entries;entries[raw]=(origin,e)
   if origin==ROOT:new_entries.add(raw)
 traced=set();trace_total=0;native_used_by_trace={}
 def verify_trace(t,rp):
  nonlocal trace_total
  raw=Path(t['path']);pair=entries.get(str(raw));origin,e=pair if pair else (None,None);h=hashlib.sha256();n=0;used=set();carry=b''
  if e is not None:
   assert str(origin/e['receipt_path'])==str(rp);check(rp,e['receipt_sha256'])
   assert e['receipt_status']=='PASS_FRESH_KERNEL_CHECK' and e['raw_sha256']==t['sha256'] and e['all_original_bytes_recoverable'] is True
   arc=origin/e['archive_path'];check(arc,e['archive_sha256']);assert arc.stat().st_size==e['archive_bytes'];stream=gzip.open(arc,'rb')
  else:assert raw.exists();stream=raw.open('rb')
  with stream as z:
   for b in iter(lambda:z.read(1048576),b''):
    h.update(b);n+=len(b);lines=(carry+b).split(b'\n');carry=lines.pop()
    for line in lines:
     hit=re.search(rb'calling init:\s*(/[^\s]+)',line)
     if hit:used.add(str(Path(hit.group(1).decode()).resolve()))
  if carry:
   hit=re.search(rb'calling init:\s*(/[^\s]+)',carry)
   if hit:used.add(str(Path(hit.group(1).decode()).resolve()))
  assert h.hexdigest()==t['sha256'],('native trace',str(raw))
  if e is not None:assert n==e['raw_bytes']
  if raw.exists():check(raw,t['sha256'])
  traced.add(str(raw));trace_total+=n;native_used_by_trace[str(raw)]=sorted(used);return used
 mods=g['modules'];records=tr['component_receipts'];assert len(records)==1588
 bymodule={r['module']:r for r in records};assert len(bymodule)==1588 and set(bymodule)==set(mods)
 assert all(bymodule[m]==r for m,r in ACCEPTED_RECEIPTS.items())
 assert set(bymodule)==set(ACCEPTED_RECEIPTS) and len(ACCEPTED_RECEIPTS)==1588
 context=RUN/'targets/current_connected/objects';fresh=[];reused=[];receipt_summary=[]
 def verify_receipt(r,kind,im,sourcebytes):
  name=r['module'];rp=Path(r['receipt_directory'])/'receipt.json';raw=read(rp)
  assert raw=={k:v for k,v in r.items() if k not in ['cached_object','audit_output']},('raw receipt equality',name)
  assert r['status']=='PASS_FRESH_KERNEL_CHECK' and r['kind']==kind and r['exit_code']==0
  assert r['source_and_imports_stable'] and r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound']
  assert r['native_runtime_digest']==nr['native_runtime_digest'] and r['compiler_sha256']==BIN and r['mathlib_commit']==MATHLIB
  command=r['command'];check(Path(command[0]),BIN);assert command[1:3]==['-j1','-t0'] and '-Ddebug.skipKernelTC=false' in command
  cap=(600,6144) if name=='ThetaCertificate5' else (180,4096) if kind=='component' else (300,6144)
  assert (r['cap_seconds'],r['cap_memory_mib'])==cap and command[3]=='-M'+str(cap[1])
  if name=='ThetaCertificate5':assert r['source_sha256']=='e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab'
  assert r['source_sha256']==digest_bytes(sourcebytes)
  frozen=Path(r['working_directory'])/(name.replace('.','/')+'.lean');assert frozen.read_bytes()==sourcebytes
  assert command[-1]==str(frozen.relative_to(r['working_directory']))
  for k in ['stdout','stderr']:
   p=rp.parent/k;check(p,r[k+'_sha256']);assert b'sorryAx' not in p.read_bytes()
  assert set(r['direct_import_bindings'])==set(im)
  assert set(r['direct_import_sha256'])==set(r['direct_import_artifacts'])==set(im)
  for imp,v in r['direct_import_bindings'].items():
   assert v['artifacts']==r['direct_import_artifacts'][imp] and v['sha256']==r['direct_import_sha256'][imp]==v['artifacts']['.olean']
   bundle(Path(v['path']),v['artifacts'])
   if imp in mods:
    assert v['artifacts']==bymodule[imp]['object_artifacts'],('owned import identity',name,imp)
    bundle(context/(imp.replace('.','/')+'.olean'),v['artifacts'])
  if kind!='complete-owned-audit':
   assert command[-3]=='-o';objectpath=Path(command[-2]);bundle(objectpath,r['object_artifacts']);assert r['object_sha256']==r['object_artifacts']['.olean']
  used=set()
  assert r['native_loader_outputs']
  for t in r['native_loader_outputs']:used|=verify_trace(t,rp)
  assert used==set(r['native_initialized_libraries']),('native initialized set',name)
  for lib in used:assert r['native_initialized_libraries'][lib]==native[lib]
  for a in r['auxiliary_outputs']:
   ap=rp.parent/a['path'];check(ap,a['sha256']);assert ap.stat().st_size==a['bytes']
  return rp
 for m in g['order']:
  r=bymodule[m];rp=verify_receipt(r,'component',mods[m]['imports'],(ROOT/'source-store'/(mods[m]['sha256']+'.lean')).read_bytes())
  keydata={'module':m,'source':r['source_sha256'],'compiler':BIN,'mathlib':MATHLIB,'trust':0,'kernel_check':True,'imports':r['direct_import_artifacts'],'native_runtime_digest':nr['native_runtime_digest'],'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
  if m=='ThetaCertificate5':keydata['resource_exception']={'memory_mib':6144,'seconds':600}
  key=digest_bytes(json.dumps(keydata,sort_keys=True).encode());cp=ROOT/'.build/cache'/key/'receipt.json';assert read(cp)==r
  bundle(Path(r['cached_object']),r['object_artifacts']);bundle(context/(m.replace('.','/')+'.olean'),r['object_artifacts'])
  (fresh if RUN in rp.parents else reused).append(m)
  receipt_summary.append({'module':m,'source_sha256':r['source_sha256'],'receipt_sha256':sha(rp),'cache_key':key,'object_artifacts':r['object_artifacts'],'fresh_in_terminal_run':RUN in rp.parents})
 assert len(fresh)+len(reused)==1588 and set(fresh)<=NEW_MODULES
 assert f['counts'].get('fresh_components',0)==len(fresh)
 assert f['counts'].get('cache_reuse',0)==len(reused)
 events=[json.loads(x) for x in (RUN/'EVENTS.jsonl').read_text().splitlines()]
 assert set(e['component'] for e in events if e.get('status')=='FRESH_KERNEL_PASS')==set(fresh)
 assert sum(e.get('status')=='FRESH_KERNEL_PASS' for e in events)==len(fresh)
 assert not any(e.get('status') in ['FAILED_OR_RESOURCE','REUSED_PRIOR','FAILED_OR_BLOCKED'] for e in events)
 roots=g['roots'];aggregate=('\n'.join('import '+m for m in roots)+'\n').encode()
 verify_receipt(tr['aggregate_receipt'],'aggregate',roots,aggregate)
 assert RUN in Path(tr['aggregate_receipt']['receipt_directory']).parents
 template=(ROOT/'scripts/AuditTemplate.lean').read_text();body=template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]','#'+json.dumps(g['order'])).replace('"AUDIT-OWNED.json"','"AUDIT-RESULT.json"')
 ar=tr['audit_receipt'];verify_receipt(ar,'complete-owned-audit',roots+['Lean.Util.CollectAxioms'],aggregate+body.encode())
 assert RUN in Path(ar['receipt_directory']).parents
 auditp=Path(ar['audit_output']);audit=read(auditp);assert audit['selected_modules']==g['order']
 assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
 actual={x['name']:x for x in audit['declarations']};assert len(actual)==len(audit['declarations'])==audit['declaration_count']
 assert set(expected)<=set(actual),'missing inherited declaration'
 differences={n:{'old':v,'new':actual[n]} for n,v in expected.items() if v!=actual[n]}
 newnames={n:v for n,v in actual.items() if n not in expected}
 (OUT/'INHERITED-DECLARATION-DELTAS.json').write_text(json.dumps(differences,indent=2)+'\n')
 (OUT/'EXACT-NEW-DECLARATION-RECORDS.json').write_text(json.dumps(newnames,indent=2)+'\n')
 allow=OUT/'REVIEWED-EXACT-DECLARATION-DELTAS.json'
 assert differences==(read(allow) if allow.exists() else {}),'explicit inherited metadata review needed'
 assert all(v['module'] in NEW_MODULES for v in newnames.values()),'new helper requires explicit review'
 assert sum(x['kind']=='theorem' for x in actual.values())==audit['theorem_declaration_count']==tr['theorems']
 for x in actual.values():assert x['kind']!='axiom' and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} and x['module'] in mods
 importedp=RUN/'targets/current_connected/ACTUAL-IMPORTED-ARTIFACTS.json';imported=read(importedp);group=collections.defaultdict(dict)
 for x in imported:
  p=Path(x['path']);check(p,x['sha256']);assert p.stat().st_size==x['bytes'];assert x['suffix'] not in group[x['module']];group[x['module']][x['suffix']]=x['sha256']
 assert set(group)==set(audit['all_imported_module_names'])
 for m,art in group.items():
  op=next(Path(x['path']) for x in imported if x['module']==m and x['suffix']=='.olean');bundle(op,art)
  if m in mods:assert art==bymodule[m]['object_artifacts']
 # Independently verify the actual namespace-resolution ledger and the four
 # owned upstream modules' isolation from the official external cache.
 namespacep=RUN/'NAMESPACE-RESOLUTION-CHECKS.jsonl'
 nrows=[json.loads(x) for x in namespacep.read_text().splitlines()]
 for row in nrows:
  assert Path(row['context'])==context
  for m,v in row['imports'].items():
   lp=Path(v['lean_path']);assert lp.resolve(strict=True)==Path(v['resolved_target']).resolve(strict=True)
   bundle(lp,v['artifacts'])
   if m in mods:assert v['artifacts']==bymodule[m]['object_artifacts']
 mask=read(RUN/'DESKTOP-NAMESPACE-MASK.json');assert mask['status']=='PASS_READONLY_NAMESPACE_MASK'
 assert len(mask['owned_exact_upstream_sources'])==4
 for m,h in mask['owned_exact_upstream_sources'].items():
  assert mods[m]['sha256']==h
  op=context/(m.replace('.','/')+'.olean');assert not op.is_symlink();bundle(op,bymodule[m]['object_artifacts'])
  assert not (Path(mask['actual_filtered_external_root'])/(m.replace('.','/')+'.olean')).exists()
 assert new_entries<=traced,'unreviewed new compressed trace'
 for ip,ib in index_snapshots.items():assert ip.read_bytes()==ib,'trace index changed during review'
 supers=[(p,read(p)) for p in ROOT.glob('SUPERVISOR-*.json')];good=[(p,x) for p,x in supers if x.get('status')=='TERMINAL_EXIT_ZERO']
 assert len(good)==1;sp,sup=good[0];assert sup['exit_code']==0 and sup['limit_event'] is None
 assert sup['allocation_limit_bytes']==12*2**30 and sup['free_floor_bytes']==8*2**30 and sup['per_file_hard_limit_bytes']==512*2**20
 assert sup['peak_path_counted_allocated_bytes']<sup['allocation_limit_bytes'] and sup['minimum_observed_free_bytes']>=sup['free_floor_bytes']
 assert sup['unchanged_core_sha256']==PINS['scripts/build_connected.py']
 assert not (ROOT/'EXECUTOR-INTERRUPTION.json').exists()
 return {'status':'PASS_INDEPENDENT_EXACT_1588_CONTEXT_REVIEW','result_sha256':sha(trp),'final_receipt_sha256':sha(RUN/'FINAL-RECEIPT.json'),'audit_sha256':sha(auditp),'actual_imported_artifacts_sha256':sha(importedp),'trace_index_sha256s':{str(ip.parent.parent.name):digest_bytes(ib) for ip,ib in index_snapshots.items()},'supervisor_terminal_sha256':sha(sp),'fresh_components':len(fresh),'fresh_component_names':fresh,'authenticated_component_reuse':len(reused),'fresh_aggregate':True,'fresh_complete_audit':True,'owned_axioms':0,'nonstandard_axiom_rows':0,'missing_modules':0,'old_records_literal_equal':len(expected)-len(differences),'inherited_metadata_differences':differences,'globally_new_declarations':len(newnames),'globally_new_theorems':sum(x['kind']=='theorem' for x in newnames.values()),'declarations':len(actual),'theorems':audit['theorem_declaration_count'],'all_imported_modules':len(group),'imported_artifact_records':len(imported),'native_trace_files_verified':len(traced),'native_trace_raw_bytes_verified':trace_total,'component_records':receipt_summary,'no_master_closure_inferred':True}



def main():
 global RUN,ACCEPTED_RECEIPTS,GRAPH
 import importlib.util
 start=time.time();RUN=Path(read(ROOT/'.build/LATEST-RUN.json')['run'])
 assert read(ROOT/'.build/LATEST-RUN.json')['status']=='PASS_ALL_REQUESTED_TARGETS'
 GRAPH=sha(ROOT/'DEPENDENCY-GRAPH.json')
 for name,w in PINS.items():check(ROOT/name,w)
 check(RUN/'DEPENDENCY-GRAPH.json',GRAPH)
 graph=read(ROOT/'DEPENDENCY-GRAPH.json');g=graph['targets']['current/connected']
 assert GRAPH=='534564494039d127c137a1ec2a9010fd5250a871dead60dc2d5cf48ae1341919'
 for n,x in g['modules'].items():
  p=ROOT/'source-store'/(x['sha256']+'.lean');check(p,x['sha256']);assert imports(p.read_bytes())==x['imports']
 basegraph=read(BASE1585/'DEPENDENCY-GRAPH.json');bg=basegraph['targets']['current/connected']
 assert all(g['modules'][m]==v for m,v in bg['modules'].items()) and set(g['modules'])-set(bg['modules'])==NEW_MODULES
 base_result=read(BASE1585/'.build/runs/20261011T094301.633551Z/targets/current_connected/RESULT.json')
 tp=Path('LOCAL_EVIDENCE/completed1585-audit-transport-20261011-1035z/audit_transport.py');check(tp,'02aed23bbc3d94871e981b1525932fe1cc3a080900b412e0f9a11f4772fb4a6f');sp=importlib.util.spec_from_file_location('explicit_transport',tp);t=importlib.util.module_from_spec(sp);sp.loader.exec_module(t)
 raw=t.read_audit(base_result['audit_receipt']['audit_output']);assert len(raw)==115612308 and digest_bytes(raw)=='763852d35780a7986ec812fbc96b372e4a8dfe7bdf102f8cda513930a53856e5';b={x['name']:x for x in json.loads(raw)['declarations']};del raw;assert len(b)==102014
 ACCEPTED_RECEIPTS={r['module']:r for r in base_result['component_receipts']}
 rr=read(PARENT154/'.build/runs/20261011T104206.717245Z/targets/candidate_parent-path/RESULT.json')
 for r in rr['component_receipts']:
  if r['module'] in NEW_MODULES:ACCEPTED_RECEIPTS[r['module']]=r
 assert len(ACCEPTED_RECEIPTS)==1588
 report=final_check(g,b)
 assert report['fresh_components']==0 and report['authenticated_component_reuse']==1588
 expected_path=Path('LOCAL_EVIDENCE/parent-path154-independent-review-20261011-1024z/EXACT-DECLARATION-COMPARISON.json');check(expected_path,'6fd226a51d39b82212336dd27a07974a5cade75eef291d84da5e593361a98c29');wanted=read(expected_path)['new_names'];actual_new=read(OUT/'EXACT-NEW-DECLARATION-RECORDS.json');assert actual_new==wanted,'new-record equality to reviewed154 requires explicit difference audit'
 assert report['declarations']==102084 and report['theorems']==92445 and report['globally_new_declarations']==70 and report['globally_new_theorems']==59
 report.update(graph_sha256=GRAPH,compiler_invoked=False,distinct_file_hashes=len(MEMO),bytes_hashed=hashed_bytes,elapsed_seconds=time.time()-start,archived_base_authenticated_reader=True)
 check(ROOT/'DEPENDENCY-GRAPH.json',GRAPH);(OUT/'FINAL-UNION-REVIEW.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['component_records','inherited_metadata_differences']},indent=2))
if __name__=='__main__':main()
