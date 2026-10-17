"""Own extension: exact zero-energy grounded-superconductor conductance.
Same rational devices and dyadic kernel as finite pair 02. No floating acceptance.
"""
import json, hashlib
from pathlib import Path
from dyadic_interval import *
if not __debug__: raise RuntimeError('optimized mode forbidden')
N=60; t=F(501643,20000); lam=F(5,2); B=F(2); Delta=F(1,5); M=F(1000)
base=F(1234318662378001,25000000000000)
E=(0,2); H=(1,3)
def adj(a):return [[C(a[j][i].r,-a[j][i].i) for j in range(len(a))] for i in range(len(a[0]))]
def norm2(z):return z.r.square()+z.i.square()
def contains_zero(z):return z.r.lo<=0<=z.r.hi and z.i.lo<=0<=z.i.hi
def probability(a,rows,cols):return sum((norm2(a[i][j]) for i in rows for j in cols),I(0))
def certify(a):
 T=[[-t,0,-lam,0],[0,t,0,lam],[lam,0,-t,0],[0,-lam,0,t]]
 U=[[-x for x in row] for row in T]; L=[list(x) for x in zip(*U)]
 def onsite(x,contact):
  h=[[x,Delta,B,0],[Delta,-x,0,B],[B,0,x,Delta],[0,B,Delta,-x]]
  return [[C(-h[i][j],int(contact and i==j)) for j in range(4)] for i in range(4)]
 # S_j is the exact right-eliminated diagonal block, j=0,...,59.
 invS=[None]*N
 invS[-1]=inverse(onsite(M,True))
 for j in range(N-2,-1,-1):
  invS[j]=inverse(sub(onsite(M if j==0 else a,j==0),mm(mm(U,invS[j+1]),L)))
 GLL=invS[0]; GRL=GLL; column=[GLL]
 for j in range(1,N):
  GRL=mm(mm(invS[j],L),GRL)
  GRL=[[-z for z in row] for row in GRL]
  column.append(GRL)
 # Check all block equations K G[:,L] = identity[:,L].
 for j in range(N):
  residual=mm(onsite(M if j in (0,N-1) else a,j in (0,N-1)),column[j])
  if j>0:
   term=mm(L,column[j-1]); residual=[[residual[x][y]+term[x][y] for y in range(4)] for x in range(4)]
  if j<N-1:
   term=mm(U,column[j+1]); residual=[[residual[x][y]+term[x][y] for y in range(4)] for x in range(4)]
  for x in range(4):
   for y in range(4):assert contains_zero(residual[x][y]-int(j==0 and x==y))
 r=[[C(int(i==j))-C(0,2)*GLL[i][j] for j in range(4)] for i in range(4)]
 tr=[[C(0,-2)*GRL[i][j] for j in range(4)] for i in range(4)]
 Ree=probability(r,E,E); Rhe=probability(r,H,E)
 Tee=probability(tr,E,E); The=probability(tr,H,E)
 gLL=I(2)-Ree+Rhe; gRL=The-Tee
 # Full column-orthogonality consistency test. Mathematical unitarity also
 # follows from K-K^dagger=2i(P_L+P_R), see accompanying note.
 rr=mm(adj(r),r); tt=mm(adj(tr),tr)
 for i in range(4):
  for j in range(4):assert contains_zero(rr[i][j]+tt[i][j]-int(i==j))
 # Independent expression for local conductance from quasiparticle conservation.
 alt=2*Rhe+Tee+The
 assert (gLL-alt).lo<=0<=(gLL-alt).hi
 return {'R_ee':Ree,'R_he':Rhe,'T_ee':Tee,'T_he':The,'g_LL':gLL,'g_RL':gRL}
values={name:certify(a) for name,a in [('minus',base+F(1,100000000)),('plus',base+F(1,10000))]}
for name,v in values.items():
 print(name, {key:(float(z.lower()),float(z.upper())) for key,z in v.items()})
gapL=values['minus']['g_LL']-values['plus']['g_LL']
gapR=values['minus']['g_RL']-values['plus']['g_RL']
print('g_LL minus-plus',float(gapL.lower()),float(gapL.upper()))
print('g_RL minus-plus',float(gapR.lower()),float(gapR.upper()))
assert F(1209,1000)<values['minus']['g_LL'].lower()<values['minus']['g_LL'].upper()<F(1210,1000)
assert F(3,1000)<values['plus']['g_LL'].lower()<values['plus']['g_LL'].upper()<F(4,1000)
assert F(-791,1000)<values['minus']['g_RL'].lower()<values['minus']['g_RL'].upper()<F(-790,1000)
assert F(-3,1000)<values['plus']['g_RL'].lower()<values['plus']['g_RL'].upper()<F(-2,1000)
assert gapL.lower()>F(1205,1000)
assert (-gapR).lower()>F(787,1000)
# Fixed decision thresholds with explicitly bounded readout errors.
assert values['minus']['g_LL'].lower()-F(1,2)>F(3,5)
assert values['plus']['g_LL'].upper()+F(1,2)<F(3,5)
assert values['minus']['g_RL'].upper()+F(3,10)<F(-2,5)
assert values['plus']['g_RL'].lower()-F(3,10)>F(-2,5)
print('PASS: rational ranges, separations, readout-error thresholds, all block residuals, column unitarity')
result={'status':'PASS','units':'e^2/h','electron_indices':list(E),'hole_indices':list(H),
 'values':{name:{k:z.out() for k,z in v.items()} for name,v in values.items()},
 'difference_minus_plus':{'g_LL':gapL.out(),'g_RL':gapR.out()},
 'hashes':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in ['verify_conductance.py','dyadic_interval.py']}}
Path('CONDUCTANCE-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
