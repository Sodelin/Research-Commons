import numpy as np
from scipy.linalg import eigh
rng=np.random.default_rng(20261020)
def power(a,p):
 v,u=eigh(a);return (u*np.maximum(v,1e-15)**p)@u.conj().T
def ent(a):
 v=eigh(a,eigvals_only=True);v=v[v>1e-14];return -sum(v*np.log(v))
def tensor(a,n):
 o=np.ones((1,1));
 for _ in range(n):o=np.kron(o,a)
 return o
def calc(rs,p,n):
 R=[tensor(r,n) for r in rs];S=sum(x*r for x,r in zip(p,R));Sp=sum(x*np.kron(r,a) for x,r,a in zip(p,R,rs));si=power(S,-.5)
 w=np.array([[p[i]*p[j]*np.trace(R[i]@si@R[j]@si).real for j in range(len(p))]for i in range(len(p))]);roots=[power(r,.5)for r in rs];A=np.array([[np.trace(a@b).real for b in roots]for a in roots]);risk=2*np.sum(w*(1-A));delta=ent(Sp)-ent(S)-sum(x*ent(r)for x,r in zip(p,rs));return risk,delta
best=(0,None)
for d,n,m,count in [(2,1,6,500),(2,2,6,500),(2,3,8,200),(3,1,8,300),(3,2,8,100),(4,1,10,200)]:
 for trial in range(count):
  rs=[]
  for i in range(m):
   a=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));a=a@a.conj().T;a/=np.trace(a);rs.append(a)
  p=rng.dirichlet(np.ones(m));r,de=calc(rs,p,n);ratio=r/de
  if ratio>best[0]:best=(ratio,(d,n,m,trial,r,de))
 print(d,n,m,'best',best,flush=True)
