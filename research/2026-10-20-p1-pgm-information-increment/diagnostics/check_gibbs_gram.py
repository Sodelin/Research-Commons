import numpy as np
from scipy.linalg import eigh
from itertools import product
rng=np.random.default_rng(20261020)
def fun(a,f):
 v,u=eigh((a+a.conj().T)/2);return (u*f(v))@u.conj().T
def root(a):return fun(a,lambda v:np.sqrt(np.maximum(v,0)))
def ent(a):
 v=eigh((a+a.conj().T)/2,eigvals_only=True);v=v[v>1e-13];return -np.sum(v*np.log(v))
def kronpow(a,n):
 x=np.eye(1)
 for _ in range(n):x=np.kron(x,a)
 return x
pauli=[np.eye(2),np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
worst=1.;maxres=0.
for N,n,m in [(1,1,4),(1,2,4),(1,3,4),(2,1,4)]:
 Ps=[]
 for s in product(range(4),repeat=N):
  if not any(s):continue
  p=np.eye(1)
  for i in s:p=np.kron(p,pauli[i])
  Ps.append(p)
 for trial in range(20):
  rs=[]
  for i in range(m):
   h=sum(rng.uniform(-1,1)*p for p in Ps); r=fun(h,lambda v:np.exp(-.8*v));r/=np.trace(r);rs.append(r)
  weights=rng.dirichlet(np.ones(m));R=[kronpow(r,n)for r in rs];S=sum(p*r for p,r in zip(weights,R));si=fun(S,lambda v:v**(-.5));d=len(rs[0]);D=len(S)
  roots=[root(r)for r in rs];RR=[root(r)for r in R];A=np.concatenate([np.sqrt(p)*r for p,r in zip(weights,RR)],axis=1);G=A.conj().T@A;Groot=A.conj().T@si@A
  def phi(x):return np.block([[np.kron(x[i*D:(i+1)*D,j*D:(j+1)*D],roots[i]@roots[j])for j in range(m)]for i in range(m)])
  sigma=phi(np.eye(m*D));sm=fun(sigma,lambda v:v**(-.25));Y=sm@phi(Groot)@sm;x=np.trace(Y@Y).real
  w=np.array([[weights[i]*weights[j]*np.trace(R[i]@si@R[j]@si).real for j in range(m)]for i in range(m)])
  aff=np.array([[np.trace(a@b).real for b in roots]for a in roots]);x2=np.sum(w*aff)
  omega=sum(p*np.kron(a,b)for p,a,b in zip(weights,R,rs));delta=ent(omega)-ent(S)-sum(p*ent(r)for p,r in zip(weights,rs));out=phi(G)
  gap=delta+np.log(x);res=max(abs(x-x2),abs(ent(G)-ent(S)),abs(ent(out)-ent(omega)),np.linalg.norm(Groot@Groot-G),abs(w.sum()-1));maxres=max(maxres,res);worst=min(worst,gap)
  assert res<2e-10 and gap>-2e-10
 print('PASS N=%d k=%d beta=0.8 n=%d ensembles=20 all coefficients in [-1,1]'%(N,N,n))
print('80 admitted finite Gibbs priors; minimum inequality margin',worst,'maximum identity residual',maxres)
print('Floating-point diagnostics only; not uniform proof or a formal certificate.')
