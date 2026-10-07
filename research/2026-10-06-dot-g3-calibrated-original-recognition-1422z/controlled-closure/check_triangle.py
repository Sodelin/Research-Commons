from fractions import Fraction as F
from pathlib import Path
import json,hashlib,time,sys
start=time.monotonic()
E=[('R','u'),('R','h'),('u','h'),('u','sB'),('h','sA'),('sA','A'),('sA','C'),('sB','B'),('sB','D')]
V={'R','u','h','sA','sB','A','B','C','D'};leaves=set('ABCD')
children={a:[b for x,b in E if x==a] for a in V};parents={b:[a for a,y in E if y==b] for b in V}
for v in V:assert (len(parents[v]),len(children[v]))==((0,2) if v=='R' else (2,1) if v=='h' else (1,0) if v in leaves else (1,2))
paths=[]
def walk(v,p):
 assert v not in p
 p=p+[v]
 if v in leaves:paths.append(p)
 for c in children[v]:walk(c,p)
walk('R',[]);assert set.intersection(*(set(p) for p in paths))=={'R'}
seen={'R'};todo=['R']
while todo:
 a=todo.pop()
 for x,y in E:
  if (x,y)==('h','sA'):continue
  b=y if x==a else x if y==a else None
  if b is not None and b not in seen:seen.add(b);todo.append(b)
assert V-seen=={'sA','A','C'}
rot={'R':['u','h'],'u':['R','h','sB'],'h':['R','sA','u'],'sA':['h','A','C'],'sB':['u','B','D'],'A':['sA'],'B':['sB'],'C':['sA'],'D':['sB']}
unseen={(a,b) for a,b in E}|{(b,a) for a,b in E};faces=[]
while unseen:
 dart=min(unseen);first=dart;face=[]
 while True:
  assert dart in unseen;unseen.remove(dart);a,b=dart;face.append(a);rs=rot[b];dart=(b,rs[(rs.index(a)-1)%len(rs)])
  if dart==first:break
 faces.append(face)
assert len(V)-len(E)+len(faces)==2;assert any(leaves<=set(f) for f in faces)
x={e:F(1,2) for e in E};x['u','sB']=F(3,4);x['sB','B']=F(2,3)
assert all(0<v<1 for v in x.values())
records=[]
for label,chosen in [(0,('u','h')),(1,('R','h'))]:
 es=[e for e in E if e[1]!='h' or e==chosen];par={b:a for a,b in es}
 def ancestry(v):
  p=[v]
  while p[-1]!='R':p.append(par[p[-1]])
  return p
 pa,pb=ancestry('A'),ancestry('B');meet=next(v for v in pa if v in pb)
 def survival(path):
  y=F(1)
  for a,b in zip(path,path[1:]):
   if a==meet:break
   y*=x[b,a]
  return y
 xa,xb=survival(pa),survival(pb)
 records.append({'parent_label':label,'A_ancestry':pa,'B_ancestry':pb,'meeting':meet,'XA':str(xa),'XB':str(xb)})
 assert xa==F(1,8);assert xb==(F(1,2) if label==0 else F(1,4))
lam=[0,1,3,6,10,15,21];rows=[[F(1)]]
for m in range(2,8):
 rate=F(m*(m-1),2);row=[rate*c/(rate-lam[j]) for j,c in enumerate(rows[-1])];row.append(F(2,m*(m+1))-sum(row));rows.append(row)
A=[sum(c*F(1,8)**l for c,l in zip(row,lam)) for row in rows[1:]]
pair=[F(2,3),F(1,6)];triple=[F(25,48),F(89,384)];forced=F(5,6)
for row in[pair,triple]:assert 0<row[0]<1 and 0<sum(row)<1
assert all(0<a<1 for a in A);assert 0<forced<1
mu=[F(1,2),F(-1,4)];cube=[F(0)]*4
for i,a in enumerate(mu):
 for j,b in enumerate(mu):
  for k,c in enumerate(mu):cube[i+j+k]+=a*b*c
moment3=[F(1,8),F(-7,64),F(0),F(0)];defect=[a-b for a,b in zip(moment3,cube)];assert defect==[F(0),F(5,64),F(-6,64),F(1,64)]
assert [1-F(2,3)*mu[0],-F(2,3)*mu[1]]==pair
assert [1-mu[0]+moment3[0]/6,-mu[1]+moment3[1]/6]==triple
assert forced-F(2,3)==F(1,6)
out={'status':'PASS_NEW_FIXED_TRIANGLE_RATIONAL_CHECK','code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'vertices':sorted(V),'edges':E,'all_root_leaf_paths':paths,'common_dominators':['R'],'rotation_faces':faces,'hybrid_child_cut_component':['sA','A','C'],'edge_survivals':[{'edge':e,'survival':str(x[e])} for e in E],'parent_path_records':records,'natural_B_pair_affine':list(map(str,pair)),'natural_B_triple_affine':list(map(str,triple)),'jensen_defect_coefficients':list(map(str,defect)),'limit_profile':list(map(str,A+[F(2,3),F(25,48),forced])),'forced_gap':'1/6','not_checked':['all-core nonattainment by execution','general controlled compiler','QE','Lean'],'seconds':time.monotonic()-start,'python':sys.version}
f=Path('triangle-result.json');assert not f.exists();f.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
