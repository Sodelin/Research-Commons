from pathlib import Path
from itertools import combinations
from functools import lru_cache
import json,time,sys
start=time.monotonic()
@lru_cache(None)
def trees(labels):
 if len(labels)==1:return (labels[0],)
 first=labels[0];rest=labels[1:];out=[]
 for k in range(len(rest)):
  for take in combinations(rest,k):
   left=tuple(sorted((first,)+take));right=tuple(x for x in labels if x not in left)
   for l in trees(left):
    for r in trees(right):out.append((l,r))
 return tuple(out)
def build(t):
 parents={};children={}
 def rec(x):
  if isinstance(x,str):node=(x,);children[node]=[];return node
  a,b=rec(x[0]),rec(x[1]);node=tuple(sorted(a+b));children[node]=[a,b];parents[a]=node;parents[b]=node;return node
 root=rec(t);return root,parents,children
def anc(v,parents):
 out=[v]
 while v in parents:v=parents[v];out.append(v)
 return out
def lca(a,b,parents):
 bb=set(anc(b,parents));return next(v for v in anc(a,parents) if v in bb)
def path(a,b,parents):
 out=[]
 while a!=b:out.append(a);a=parents[a]
 return set(out)
rows=[];summary=[]
for na,nb in [(1,1),(1,2),(2,1),(2,2)]:
 aa=[f'A{i}' for i in range(1,na+1)];bb=[f'B{i}' for i in range(1,nb+1)]
 ts=trees(tuple(aa+bb));expected={2:1,3:3,4:15}[na+nb];assert len(ts)==expected
 passed=0
 for t in ts:
  rt,par,children=build(t);A=[(x,) for x in aa];B=[(x,) for x in bb]
  w=A[0] if na==1 else lca(A[0],A[1],par)
  good=all(len({lca(a,b,par) for a in A})==1 for b in B)
  record={'A_tips':na,'B_tips':nb,'tree':t,'calibrated_lca_condition':good}
  if good:
   passed+=1;assert not(set(w)&set(bb))
   for a in A:
    e=path(a,w,par)
    for b in B:
     meet=lca(a,b,par);tt=path(w,meet,par);assert e.isdisjoint(tt);assert path(a,meet,par)==e|tt
   record['additive_path_vector_identity']=True
  else:
   witnesses=[]
   for b in B:
    if na==2:
     m1,m2=lca(A[0],b,par),lca(A[1],b,par)
     if m1!=m2:
      s1,s2=path(b,m1,par),path(b,m2,par)
      assert s1<s2 or s2<s1
      witnesses.append({'fixed_B':b[0],'meeting1':m1,'meeting2':m2,'strict_extra_edges':sorted(s1^s2)})
   assert witnesses;record['strict_positive_hazard_witnesses']=witnesses
  rows.append(record)
 summary.append({'A_tips':na,'B_tips':nb,'trees':len(ts),'satisfy_calibration_lca':passed})
assert len(rows)==22
out={'status':'PASS all22 selected rooted binary skeletons','summary':summary,'trees':rows,'python':sys.version,'elapsed_seconds':time.monotonic()-start,'scope':'Selected-skeleton step only; general source reduction remains hand proof'}
Path('skeleton-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'summary':summary,'elapsed_seconds':out['elapsed_seconds']},indent=2))
