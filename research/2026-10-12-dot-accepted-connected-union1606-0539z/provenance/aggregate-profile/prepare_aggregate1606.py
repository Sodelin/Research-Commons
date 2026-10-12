"""Additive immutable hardlink staging; no compiler, no foreign objects."""
from pathlib import Path
import argparse,hashlib,json,os,shutil
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def require(x,m):
 if not x:raise ValueError(m)
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--destination',type=Path,required=True);ap.add_argument('--review',type=Path,required=True);ap.add_argument('--review-sha',required=True);ap.add_argument('--execute',action='store_true');a=ap.parse_args()
 require(a.execute and H(a.review)==a.review_sha,'explicit reviewed staging required')
 proposal=Path(__file__).resolve().parent
 require(H(proposal/'STAGING-INPUT-PINS.json')=='ff1eb2639233bb2ab1ddf0e03edc28e7fc898f6e132f6d05ec80fb0e9377ea24','reviewed staging pin file')
 pins=json.loads((proposal/'STAGING-INPUT-PINS.json').read_bytes())
 old=Path('LOCAL_EVIDENCE/connected-union1598-20261012-0456z');narrow=Path('LOCAL_EVIDENCE/g4-sparse-existence318-check-20261012-0523z');dest=a.destination
 require(not dest.exists(),'fresh destination required');require(shutil.disk_usage(dest.parent).free>11*2**30+64*2**20,'preparation and launch reserve')
 require(H(proposal/'DEPENDENCY-GRAPH.json')==pins['graph_sha256'],'graph pin')
 graph=json.loads((proposal/'DEPENDENCY-GRAPH.json').read_bytes());selected=graph['targets']['current/connected']['modules'];allmods={}
 for t in graph['targets'].values():
  for n,e in t['modules'].items():
   require(n not in allmods or (allmods[n]['sha256'],allmods[n]['imports'])==(e['sha256'],e['imports']),'historical source/import conflict');allmods[n]=e
 require(len(selected)==1606 and len(allmods)==1607,'exact selected/store count')
 additions={'Mathlib.Algebra.Polynomial.CoeffList', 'G4ActualSparseCertificateExistence', 'Mathlib.Algebra.Polynomial.RuleOfSigns', 'Mathlib.Analysis.Asymptotics.SpecificAsymptotics', 'Mathlib.Analysis.Polynomial.Basic', 'Mathlib.Analysis.Polynomial.Order', 'Mathlib.Data.List.Destutter', 'Mathlib.Algebra.Polynomial.Basis'};roots={};cache={};inherited=set()
 for n,e in allmods.items():
  origin=narrow if n in additions else old;p=origin/'source-store'/(e['sha256']+'.lean');require(H(p)==e['sha256'],'source identity');roots[n]=p;s=p.stat();inherited.add((s.st_dev,s.st_ino))
 for origin in [old,narrow]:
  for f in (origin/'.build/cache').glob('*/receipt.json'):
   d=json.loads(f.read_bytes());n=d.get('module')
   if n not in allmods or (n in additions)!=(origin==narrow) or d.get('source_sha256')!=allmods[n]['sha256']:continue
   require(n not in cache,'duplicate exact cache');rows=[]
   for p in f.parent.iterdir():
    require(p.is_file() and not p.is_symlink(),'regular cache files only');s=p.stat();inherited.add((s.st_dev,s.st_ino));rows.append(dict(path=str(p),name=p.name,sha256=H(p),bytes=s.st_size))
   cache[n]=dict(key=f.parent.name,receipt_sha256=H(f),files=rows)
 require(set(cache)==set(allmods),'every selected and isolated fixture context required')
 def meter():
  count=new=extra=0;seen=set()
  for p in [dest]+list(dest.rglob('*')):
   s=p.lstat();key=(s.st_dev,s.st_ino)
   if p.is_file() and not p.is_symlink():count+=s.st_blocks*512
   else:extra+=s.st_blocks*512
   if key not in inherited and key not in seen:new+=s.st_blocks*512;seen.add(key)
  require(new<=64*2**20,'64MiB preparation cap');require(count<=1024*2**20,'1GiB initial counted cap');require(shutil.disk_usage(dest).free>11*2**30,'launch reserve')
  return dict(new_nonshared_allocated_bytes=new,path_counted_file_bytes=count,directory_symlink_allocated_bytes=extra)
 dest.mkdir();(dest/'source-store').mkdir();(dest/'scripts').mkdir();(dest/'.build/cache').mkdir(parents=True)
 shutil.copyfile(proposal/'DEPENDENCY-GRAPH.json',dest/'DEPENDENCY-GRAPH.json')
 for i,(n,p) in enumerate(roots.items()):
  os.link(p,dest/'source-store'/(allmods[n]['sha256']+'.lean'))
  if i%100==0:meter()
 for i,(n,d) in enumerate(cache.items()):
  out=dest/'.build/cache'/d['key'];out.mkdir()
  for row in d['files']:os.link(row['path'],out/row['name'])
  if i%100==0:meter()
 for name,digest in pins['scripts'].items():
  origin=proposal if name in ['build_aggregate1606.py','run_aggregate1606.py','run_current.py'] else old/'scripts'
  require(H(origin/name)==digest,'origin script');shutil.copyfile(origin/name,dest/'scripts'/name);require(H(dest/'scripts'/name)==digest,'staged script')
 for name,digest in pins['config'].items():
  require(H(old/name)==digest,'config pin');shutil.copyfile(old/name,dest/name);require(H(dest/name)==digest,'staged config')
 save(dest/'PREPARATION.json',dict(status='PREPARED_PENDING_INDEPENDENT_PREFLIGHT',graph_sha256=pins['graph_sha256'],source_bytes=sum(roots[n].stat().st_size for n in selected),source_store_bytes=sum(p.stat().st_size for p in roots.values()),new_source_bytes=sum(roots[n].stat().st_size for n in additions),selected_count=1606,source_store_count=1607,reuse_count=1606,fresh_count=0,scripts=pins['scripts'],profile_review_sha256=a.review_sha,immutable_hardlink_reuse=True,owned_mathlib_count=11,new_allocation_limit_bytes=64*2**20))
 save(dest/'AUTHENTICATED-REUSE-INPUTS.json',cache)
 for n,p in roots.items():require(H(p)==allmods[n]['sha256'] and H(dest/'source-store'/(allmods[n]['sha256']+'.lean'))==allmods[n]['sha256'],'source final authentication')
 for n,d in cache.items():
  for row in d['files']:require(H(Path(row['path']))==row['sha256'] and H(dest/'.build/cache'/d['key']/row['name'])==row['sha256'],'cache final authentication')
 stats=meter();save(dest/'STAGING-BUDGET.json',stats);stats=meter();save(dest/'STAGING-BUDGET.json',stats);meter();print(json.dumps(stats),flush=True)
if __name__=='__main__':main()
