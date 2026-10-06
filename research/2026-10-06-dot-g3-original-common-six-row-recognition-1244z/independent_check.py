import resource
resource.setrlimit(resource.RLIMIT_CPU,(5,5))
resource.setrlimit(resource.RLIMIT_AS,(128*1024**2,128*1024**2))
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,time,sys,itertools
start=time.monotonic();root=Path('g3-two-hybrid-marginal-obstruction-20261006-1202z')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(root/'result.json')=='81edb406f1768885ff472c785d30421f4cc71bd3fca403b0f9c1b9116b8380f1';given=json.loads((root/'result.json').read_text())
provider_pins={'ORIGINAL-TESTER-PROOF.md':'661696b322c1ee2f57ffeb45ada556808f945d698ef0187c1a32ec0d881e40a1','SOURCE-CHECKPOINT.md':'0cb9d8b1443c63764ce30a9e8d5af4e8bb59a65f27f119ee7ff738d396da201b','INTERIOR-OBSTRUCTION.md':'ed4caaea43f4965d37378f180a1ee4a787ab726dbb13de40f59c1fb975afc16f'}
for n,h in provider_pins.items():assert sha(root/'providers'/n)==h
E=[('R','u'),('R','v'),('u','hA'),('v','hA'),('u','hB'),('v','hB'),('hA','sA'),('hB','sB'),('sA','A'),('sA','C'),('sB','B'),('sB','D')]
V=set(sum(([a,b] for a,b in E),[]));leaves=set('ABCD');assert len(V)==11 and len(E)==12
adj={a:[b for u,b in E if u==a] for a in V}
paths=[]
def walk(v,seq):
 assert v not in seq
 seq=seq+[v]
 if v in leaves:paths.append(seq)
 for w in adj[v]:walk(w,seq)
walk('R',[])
assert set.intersection(*(set(p) for p in paths))=={'R'}
for v in V:
 deg=(sum(b==v for a,b in E),sum(a==v for a,b in E))
 assert deg==((0,2) if v=='R' else (1,0) if v in leaves else (2,1) if v in {'hA','hB'} else (1,2))
for cut,want in [(('hA','sA'),{'sA','A','C'}),(('hB','sB'),{'sB','B','D'})]:
 seen={'R'}
 while True:
  nxt=seen|{b for a,b in E if (a,b)!=cut and a in seen}|{a for a,b in E if (a,b)!=cut and b in seen}
  if nxt==seen:break
  seen=nxt
 assert V-seen==want
rot=given['rotation_system'];darts=set(E)|{(b,a) for a,b in E}
assert all(set(rot[v])=={b for a,b in darts if a==v} and len(rot[v])==len(set(rot[v])) for v in V)
faces=[]
while darts:
 startdart=min(darts);cur=startdart;face=[]
 while True:
  darts.remove(cur);a,b=cur;face.append(a);cur=(b,rot[b][(rot[b].index(a)+1)%len(rot[b])])
  if cur==startdart:break
 faces.append(face)
assert len(faces)==3 and len(V)-len(E)+len(faces)==2 and any(leaves<=set(f) for f in faces)
mu={}
for A,B in itertools.product(['u','v'],repeat=2):
 w=F(1,2)*(F(2,3) if B=='u' else F(1,3));x=F(1,4)*(F(3,4) if A=='u' else F(1,4))
 if A!=B:x*=F(1,3) if A=='u' else F(1,2)
 mu[x]=mu.get(x,F(0))+w
assert mu=={F(1,32):F(1,3),F(1,16):F(1,3),F(3,16):F(1,3)}
lam=[k*(k-1)//2 for k in range(1,8)];f0=[F(2,k*(k+1)) for k in range(1,8)]
def Q(v):return [F(0)]+[lam[k]*(v[k-1]-v[k]) for k in range(1,7)]
cols=[]
for j in range(7):
 v=f0[:]
 for ell in range(7):
  if ell==j:continue
  qv=Q(v);v=[(a+lam[ell]*b)/(lam[ell]-lam[j]) for a,b in zip(qv,v)]
 assert Q(v)==[-lam[j]*a for a in v]
 cols.append(v)
A=[[cols[j][k] for j in range(k+1)] for k in range(7)]
assert all(cols[j][k]==0 for j in range(7) for k in range(j));assert [sum(row) for row in A]==f0
assert [[str(v) for v in row] for row in A]==given['monophyly_coefficients']
mom=[sum(w*x**n for x,w in mu.items()) for n in lam];obs=[sum(c*m for c,m in zip(row,mom)) for row in A[1:]]
assert [str(v) for v in obs]==given['observed_monophyly_probabilities']
coeff=list(map(F,given['exposing_coefficients']));assert [1 if c>0 else -1 for c in coeff]==[1,-1,1,-1,1,-1,1]
for x in mu:
 assert sum(c*x**n for c,n in zip(coeff,lam))==0
 assert sum(c*n*x**(n-1) for c,n in zip(coeff[1:],lam[1:]))==0
x,y,z=sorted(mu);det=(y-x)*(z-x)*(z-y)*(x+y+z);assert det>0
out={'status':'PASS_INDEPENDENT_FIXED_GRAPH_AND_RATIONAL_CHECKS','new_execution':True,'source_sha256':sha(Path(__file__)),'author_result_sha256':sha(root/'result.json'),'provider_pins':provider_pins,'all_root_leaf_paths':paths,'common_dominators':['R'],'reverse_orientation_faces':faces,'atoms':{str(x):str(w) for x,w in sorted(mu.items())},'spectral_projector_coefficients':[[str(v) for v in row] for row in A],'monophyly_probabilities':list(map(str,obs)),'exposing_double_root_and_sign_check':True,'weight_matrix_determinant':str(det),'not_executed':['general source compiler','source catalogue','arbitrary-core membership'],'seconds':time.monotonic()-start,'python':sys.version}
p=root/'independent-result.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
