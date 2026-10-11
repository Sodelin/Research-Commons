from pathlib import Path
import json,hashlib,os,shutil
D=Path(__file__).resolve().parent;B=Path('LOCAL_EVIDENCE/connected-union1585-20261011-0910z');N=Path('LOCAL_EVIDENCE/parent-path-check154-20261011-1021z');O=Path('LOCAL_EVIDENCE/connected-union1588-20261011-1049z');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();floor=20*2**30;cap=40*2**20;start=shutil.disk_usage(B).free;assert start>floor+cap;assert not O.exists() or not any(O.iterdir());O.mkdir(exist_ok=True);new=[]
def guard():
 size=sum(p.stat().st_blocks*512 for p in new);free=shutil.disk_usage(O).free;assert size<cap and start-free<cap and free>floor;return size,free
def cp(p,q):
 guard();q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);new.append(q);guard()
def write(p,x):
 guard();p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n');new.append(p);guard()
def link(p,q):
 guard();q.parent.mkdir(parents=True,exist_ok=True);os.link(p,q);guard()
g=json.loads((B/'DEPENDENCY-GRAPH.json').read_text());assert sha(B/'DEPENDENCY-GRAPH.json')=='862b5662a109f923be271eb7a28d27c2cb76b7eb46934692257896707a57bd9f';t=g['targets']['current/connected'];g['targets']['history/accepted1585']=json.loads(json.dumps(t));nt=json.loads((N/'DEPENDENCY-GRAPH.json').read_text())['targets']['candidate/parent-path'];names=['GroupedParentPathCalendar','FirstParentJoin','MixedParentBoundary']
for n in names:
 assert n not in t['modules'];t['modules'][n]=nt['modules'][n];t['order'].append(n);t['roots'].append(n)
t['external_imports']=sorted({i for m in t['modules'].values() for i in m['imports'] if i not in t['modules']});g['targets']['candidate/parent-path']=nt;g['scope']='Prospective exact accepted1585 plus three separately accepted parent-path sources; fixture isolated, fresh union aggregate/audit required.'
assert len(t['modules'])==1588
seen=set()
for n in t['order']:assert all(i not in t['modules'] or i in seen for i in t['modules'][n]['imports']);seen.add(n)
allmods=dict(t['modules'])
for target in g['targets'].values():
 for n,m in target['modules'].items():
  if n in allmods:assert m['sha256']==allmods[n]['sha256'] and m['imports']==allmods[n]['imports'] and m.get('module',n)==allmods[n].get('module',n)
  else:allmods[n]=m
assert set(allmods)-set(t['modules'])=={'G7OriginalPopulationFixture'}
write(O/'DEPENDENCY-GRAPH.json',g)
for n,m in allmods.items():
 p=(N if n in names else B)/'source-store'/(m['sha256']+'.lean');assert sha(p)==m['sha256'];link(p,O/'source-store'/p.name)
for p in (B/'scripts').iterdir():
 if p.is_file():cp(p,O/'scripts'/p.name)
for n in ['lakefile.lean','lean-toolchain','lake-manifest.json']:cp(B/n,O/n)
found=set();records=[]
for origin in [B,N]:
 for p in (origin/'.build/cache').glob('*/receipt.json'):
  r=json.loads(p.read_text());n=r['module']
  if n in found or n not in allmods or r['source_sha256']!=allmods[n]['sha256']:continue
  if origin==N and n not in names:continue
  assert r['exit_code']==0 and r['source_and_imports_stable'];dst=O/'.build/cache'/p.parent.name
  for q in p.parent.iterdir():
   if q.is_file():
    if q.name=='receipt.json':cp(q,dst/q.name)
    else:link(q,dst/q.name)
  found.add(n);records.append({'module':n,'key':p.parent.name,'receipt_sha256':sha(p),'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'accepted_origin':origin.name,'original_receipt_path':str(p)})
assert found==set(allmods)
write(O/'AUTHENTICATED-ADDITIVE-PREFLIGHT.json',{'status':'PREPARED_REQUIRES_REVIEW','records':records,'selected_expected_reuse':1588,'isolated_fixture_reuse':1,'new_math_modules':names,'foreign_compiled_objects_admitted':False})
for origin,label in [(B,'accepted1585'),(N,'accepted154')]:
 cp(origin/'DEPENDENCY-GRAPH.json',O/'provenance'/(label+'-DEPENDENCY-GRAPH.json'))
cp(Path(__file__),O/'provenance/prepare.py')
write(O/'PREPARATION.json',{'status':'PREPARED_PENDING_REVIEW_NO_COMPILER','graph_sha256':sha(O/'DEPENDENCY-GRAPH.json'),'selected_math_modules':1588,'total_distinct_bodies':1589,'fresh_selected_sources':0,'reused_selected_components':1588,'source_bytes':sum((O/'source-store'/(m['sha256']+'.lean')).stat().st_size for m in allmods.values()),'new_source_bytes':sum((O/'source-store'/(t['modules'][n]['sha256']+'.lean')).stat().st_size for n in names),'fixture_main_isolated':True,'scripts':{p.name:sha(p) for p in (O/'scripts').iterdir() if p.is_file()}})
size,free=guard();write(O/'STAGING-BUDGET-RECEIPT.json',{'status':'PASS_HARD_40MIB_PREPARATION_WITHIN_PRIOR64MIB_MAX','start_free':start,'end_free':free,'observed_consumption':start-free,'new_regular_file_allocation':size,'preparation_cap':cap,'launch_threshold':floor,'compiler_invoked':False});print(sha(O/'DEPENDENCY-GRAPH.json'),size,free)
