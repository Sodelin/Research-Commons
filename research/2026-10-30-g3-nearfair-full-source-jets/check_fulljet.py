import argparse,sys,json,time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('engine_root',type=Path);args=ap.parse_args()
sys.path.insert(0,str(args.engine_root))
from source_bindings import verify
verify(args.engine_root)
from forest_modular import *
start=time.time();n=12
Q=ordinary(n);Qc,F,R,cs=colored(n);dim=Q.shape[0]
print(json.dumps({'cap':n,'ordinary_dimension':dim,'colored_dimension':Qc.shape[0]}),flush=True)
Z=F.toarray()%P;A=[]
for k in range(5):
 if k:Z=(Qc@Z)%P
 A.append((R@Z)%P)
 print('computed fair full source derivative',k,flush=True)
I=np.eye(dim,dtype=np.int64);Q1=Q.toarray()%P;Q2=(Q@Q1)%P;Q3=(Q@Q2)%P;Q4=(Q@Q3)%P
assert np.array_equal(A[0],I)
assert np.array_equal(A[1],Q1*pow(2,-1,P)%P)
assert np.array_equal(A[2],(Q2-Q1)*pow(4,-1,P)%P)
R3=(8*A[3]-Q3+3*Q2)*pow(48,-1,P)%P
assert np.count_nonzero(R3)>0
# The beta^2 term of routing is z^4, beta=z^2. Retain current-root routing and opaque pooling.
ci={c:i for i,c in enumerate(cs)};entries=[]
from math import comb
for i,f in enumerate(states(n)):
 nr=len(f);counts=Counter()
 for mask in range(1<<nr):
  aa=tuple(f[j] for j in range(nr) if mask>>j&1);bb=tuple(f[j] for j in range(nr) if not(mask>>j&1))
  coeff=sum(comb(len(aa),j)*comb(len(bb),4-j)*(-1)**(4-j) for j in range(5) if j<=len(aa) and 4-j<=len(bb))
  if coeff:counts[ci[(aa,bb)]]+=coeff
 entries.extend((i,j,m*pow(2,-nr,P)%P) for j,m in counts.items())
Rb2=sparse(entries,R.shape)
Z2=(Qc@(Qc@F.toarray()%P))%P
A22=(Rb2@Z2)%P
assert np.array_equal(A22,(Q2-A[2]-(Q@A[2])%P+2*A[3])%P)
np.savez_compressed(Path(__file__).with_name('full-cap12-identity-jets.npz'),Q=Q1,A2=A[2],A3=A[3],A4=A[4],A22=A22,R3=R3,P=P)
print(json.dumps({'status':'PASS','cap':n,'prime':P,'checks':['B(0)=I','B_u(0,0)=Q/2','B_uu(0,0)=(Q^2-Q)/4','full cubic R3 nonzero','direct beta^2 routing coefficient A22 matches endpoint/PDE formula'],'elapsed_seconds':time.time()-start,'scope':'Exact modular all forest-orbit source derivatives; inherited opaque/projective reconstruction. Not characteristic-zero sign, real branch feasibility, or original G3 closure.'},indent=2),flush=True)
