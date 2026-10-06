from fractions import Fraction as F
from pathlib import Path
import json,time,sys
start=time.monotonic()
E=[('R','u'),('R','v'),('u','hA'),('u','hB'),('v','hA'),('v','hB'),('hA','sA'),('hB','sB'),('sA','A'),('sA','C'),('sB','B'),('sB','D')]
V=['R','u','v','hA','hB','sA','sB','A','B','C','D']; leaves={'A','B','C','D'}
children={v:[b for a,b in E if a==v] for v in V}; parents={v:[a for a,b in E if b==v] for v in V}
for v in V:
 expected=(0,2) if v=='R' else (1,0) if v in leaves else (2,1) if v in {'hA','hB'} else (1,2)
 assert (len(parents[v]),len(children[v]))==expected
remaining=set(V); order=[]
while remaining:
 ready=sorted(v for v in remaining if not(set(parents[v])&remaining)); assert ready
 order.extend(ready); remaining-=set(ready)
def reach(remove=None,drop=None,undirected=False):
 seen=set() if remove=='R' else {'R'}; todo=list(seen)
 while todo:
  a=todo.pop()
  for e in E:
   if drop and set(e)==set(drop): continue
   if e[0]==a: b=e[1]
   elif undirected and e[1]==a: b=e[0]
   else: continue
   if b!=remove and b not in seen: seen.add(b);todo.append(b)
 return seen
assert reach()==set(V)
assert all(any(t in reach(remove=v) for t in leaves if t!=v) for v in V if v!='R')
for drop,below in [(('hA','sA'),{'sA','A','C'}),(('hB','sB'),{'sB','B','D'})]: assert set(V)-reach(drop=drop,undirected=True)==below
rot={'R':['u','v'],'u':['R','hA','hB'],'v':['R','hB','hA'],'hA':['u','v','sA'],'hB':['u','sB','v'],'sA':['hA','C','A'],'sB':['hB','B','D'],'A':['sA'],'C':['sA'],'B':['sB'],'D':['sB']}
darts={(a,b) for a,b in E}|{(b,a) for a,b in E}; unseen=set(darts); faces=[]
while unseen:
 first=min(unseen); curr=first; face=[]
 while True:
  assert curr in unseen;unseen.remove(curr);face.append(curr[0]);a,b=curr
  nb=rot[b];curr=(b,nb[(nb.index(a)-1)%len(nb)])
  if curr==first: break
 faces.append(face)
assert len(faces)==3 and len(V)-len(E)+len(faces)==2
assert any(leaves<=set(face) for face in faces)
surv={e:F(1,2) for e in E};surv.update({('u','hA'):F(3,4),('v','hA'):F(1,4),('R','u'):F(1,3),('R','v'):F(1,2)})
assert all(0<x<1 for x in surv.values())
z=surv[('sA','A')]*surv[('hA','sA')];a,b,c,d=[surv[e] for e in [('u','hA'),('v','hA'),('R','u'),('R','v')]]
pa,pb=F(1,2),F(2,3)
cases=[('u','u',z*a,pa*pb),('v','v',z*b,(1-pa)*(1-pb)),('u','v',z*a*c,pa*(1-pb)),('v','u',z*b*d,(1-pa)*pb)]
mu={}
for _,_,x,w in cases:mu[x]=mu.get(x,F(0))+w
assert mu=={F(1,32):F(1,3),F(1,16):F(1,3),F(3,16):F(1,3)}
lam=[0,1,3,6,10,15,21]; A=[[F(1)]]
for m in range(2,8):
 row=[F(lam[m-1],lam[m-1]-lam[j])*A[-1][j] for j in range(m-1)]
 row.append(F(2,m*(m+1))-sum(row));assert row[-1]!=0;A.append(row)
mom=[sum(w*x**n for x,w in mu.items()) for n in lam]
obs=[sum(c*x for c,x in zip(row,mom)) for row in A[1:]]
assert all(0<x<1 for x in obs)
# c0=1; solve six equations for the other six sparse coefficients.
M=[]
for x in sorted(mu):
 M.append([x**n for n in lam[1:]]+[F(-1)])
 M.append([n*x**(n-1) for n in lam[1:]]+[F(0)])
for j in range(6):
 k=next(k for k in range(j,6) if M[k][j]);M[j],M[k]=M[k],M[j]
 scale=M[j][j];M[j]=[v/scale for v in M[j]]
 for k in range(6):
  if k!=j:
   c=M[k][j];M[k]=[a-c*b for a,b in zip(M[k],M[j])]
coef=[F(1)]+[M[k][-1] for k in range(6)]
assert all(sum(c*x**n for c,n in zip(coef,lam))==0 for x in mu)
assert all(sum(c*n*x**(n-1) for c,n in zip(coef[1:],lam[1:]))==0 for x in mu)
assert [1 if c>0 else -1 if c<0 else 0 for c in coef]==[1,-1,1,-1,1,-1,1]
def ss(x):return str(x)
out={'status':'PASS exact explicit graph/routing/monophyly/exposing checks','vertices':V,'edges':E,'topological_order':order,'rotation_system':rot,'faces':faces,'all_taxa_common_face':True,'root_unique_common_stable_ancestor':True,'hybrid_child_bridges':True,'survivals':[{ 'edge':e,'x':ss(x)} for e,x in surv.items()],'routing_cases':[{'A_parent':aa,'B_parent':bb,'X':ss(x),'probability':ss(w)} for aa,bb,x,w in cases],'law':[{ 'X':ss(x),'probability':ss(w)} for x,w in sorted(mu.items())],'lambda':lam,'moments':list(map(ss,mom)),'monophyly_coefficients':[[ss(x) for x in row] for row in A],'diagonal_nonconstant':[ss(row[-1]) for row in A[1:]],'observed_monophyly_probabilities':list(map(ss,obs)),'row_total_copies':list(range(5,11)),'exposing_coefficients':list(map(ss,coef)),'exposing_sign_variations':6,'python':sys.version,'elapsed_seconds':time.monotonic()-start,'not_checked':['arbitrary graph catalogue','general G2 source compiler','independent implementation','original G3 recognition']}
Path('result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
