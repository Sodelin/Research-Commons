"""Read-only graph/budget/control audit; no builder, Lean or staging invoked."""
from pathlib import Path
import ast,hashlib,json,os
P=Path('LOCAL_EVIDENCE/union1598-budget-proposal-20261012-0451z'); B=Path('LOCAL_EVIDENCE/connected-union1597-20261012-0431z'); N=Path('LOCAL_EVIDENCE/g4-observable-certificate310-check-20261012-0446z'); O=Path(__file__).parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rd=lambda p:json.loads(p.read_bytes())
pins=rd(P/'PROPOSAL-PINS.json')
for f,h in pins.items():assert H(P/f)==h
old=rd(B/'DEPENDENCY-GRAPH.json');g=rd(P/'DEPENDENCY-GRAPH.json');a=old['targets']['current/connected'];b=g['targets']['current/connected'];assert len(a['modules'])==1597 and len(b['modules'])==1598
for t,v in old['targets'].items():assert (g['targets']['history/accepted1597'] if t=='current/connected' else g['targets'][t])==v
assert all(b['modules'][n]==v for n,v in a['modules'].items());assert [n for n in b['order'] if n in a['modules']]==a['order'];assert b['roots'][:len(a['roots'])]==a['roots'];assert a['external_imports']==b['external_imports']
allmods={}
for t in g['targets'].values():
 for n,e in t['modules'].items():
  if n in allmods:assert (e['sha256'],e['imports'])==(allmods[n]['sha256'],allmods[n]['imports'])
  allmods[n]=e
assert len(allmods)==1599
new={'G4ActualObservableBankCertificate'};cache={};largest=0;cachefiles=0
for origin in [B,N]:
 for f in (origin/'.build/cache').glob('*/receipt.json'):
  r=rd(f);n=r.get('module')
  if n not in allmods or (n in new)!=(origin==N) or r.get('source_sha256')!=allmods[n]['sha256']:continue
  assert n not in cache;payload=0
  for x in f.parent.iterdir():
   assert x.is_file() and not x.is_symlink();payload+=x.stat().st_blocks*512;largest=max(largest,x.stat().st_size);cachefiles+=1
  cache[n]=payload
assert set(cache)==set(allmods);assert sum(cache.values())==727539712;assert sum(cache[n] for n in new)==602112
# Execute only these pure locally authored policy functions, not module top-level code.
def pure(name,file):
 tree=ast.parse((P/file).read_text());fn=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name==name);d={};exec(compile(ast.Module(body=[fn],type_ignores=[]),'<pure-policy-check>','exec'),d);return d[name]
f=pure('allowed_invocation','build_aggregate1598.py'); tests=[]
for name,kind,obj,seconds,memory,want in [('G4SpecifiedCombEvent','component',True,300,6144,False),('AnyPrerequisite','component',True,180,4096,False),('Connected_current_connected','aggregate',True,300,6144,True),('OwnedAudit','complete-owned-audit',False,300,6144,True),('Connected_other','aggregate',True,300,6144,False),('OwnedAudit','complete-owned-audit',True,300,6144,False),('Connected_current_connected','aggregate',True,180,4096,False),('Connected_current_connected','aggregate',True,301,6144,False),('OwnedAudit','component',False,300,6144,False)]:
 assert f(name,'x'*64,obj,seconds,memory,kind)==want;tests.append([name,kind,obj,seconds,memory,want])
l=pure('limit_event','run_aggregate1598.py');cap=3*2**30;floor=8*2**30;perfile=512*2**20
for size,largestf,free,mem,want in [(cap-1,perfile-1,floor,2**30,None),(cap,0,floor,2**30,'PACKAGE_ALLOCATION_LIMIT'),(0,perfile,floor,2**30,'PER_FILE_LIMIT'),(0,0,floor-1,2**30,'FREE_STORAGE_FLOOR'),(0,0,floor,2**30-1,'AVAILABLE_MEMORY_FLOOR')]:assert l(size,largestf,free,mem,cap,floor,perfile)==want
# Exact already-reviewed narrow supervisor except names, cap and explanatory string.
sup=(P/'run_aggregate1598.py').read_text();expected=(B/'scripts/run_aggregate1597.py').read_text().replace('run_aggregate1597.py','run_aggregate1598.py').replace('build_aggregate1597.py','build_aggregate1598.py').replace('aggregate-only1597','aggregate-only1598');assert sup==expected
sp=rd(P/'STAGING-INPUT-PINS.json')
for n,h in sp['scripts'].items():assert H((P if n in ['run_aggregate1598.py','build_aggregate1598.py','run_current.py'] else B/'scripts')/n)==h
for n,h in sp['config'].items():assert H(B/n)==h
out={'status':'STATIC_GRAPH_BUDGET_POLICY_PASS_STAGING_AND_RUNTIME_PENDING','proposal_pins':pins,'all_prior_current_module_entries_literal':1597,'all_prior_targets_preserved':len(old['targets']),'new_selected_modules':1598,'source_store_including_isolated_fixture':1599,'cache_path_allocated_bytes':sum(cache.values()),'cache_files':cachefiles,'largest_cache_file_bytes':largest,'one_new_cache_allocated_bytes':sum(cache[n] for n in new),'new_bundle_allocated_bytes':{n:cache[n] for n in sorted(new)},'installed_namespace_charged_again':True,'policy_controls_passed':len(tests)+5,'invocation_controls':tests,'supervisor_exact_reviewed_derivative':True,'compiler_builder_or_staging_invoked':False,'approval_for_larger_profile_inherited':False}
(O/'PROPOSAL-CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['proposal_pins','invocation_controls']},indent=2))
