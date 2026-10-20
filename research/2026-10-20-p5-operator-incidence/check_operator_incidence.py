import numpy as np
from scipy.linalg import expm
from itertools import product
rng=np.random.default_rng(20261020)
I=np.eye(2,dtype=complex); X=np.array([[0,1],[1,0]],complex); Y=np.array([[0,-1j],[1j,0]]); Z=np.diag([1,-1]).astype(complex)
ps=[X,Y,Z]
def kron(xs):
 r=np.array([[1]],complex)
 for x in xs:r=np.kron(r,x)
 return r
def comm(a,b):return a@b-b@a
def norm(a):return np.linalg.norm(a,2)
def herm(d):
 a=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));a=(a+a.conj().T)/2;return a/norm(a)
def embed(a,S,n):
 d=2**n;r=np.zeros((d,d),complex)
 for x in range(d):
  xb=[(x>>(n-1-i))&1 for i in range(n)]
  for y in range(d):
   yb=[(y>>(n-1-i))&1 for i in range(n)]
   if all(xb[i]==yb[i] for i in range(n) if i not in S):
    xx=sum(xb[i]<<(len(S)-1-j) for j,i in enumerate(S)); yy=sum(yb[i]<<(len(S)-1-j) for j,i in enumerate(S));r[x,y]=a[xx,yy]
 return r
count=0
for n in [2,3,4]:
 As=[[embed(a,[i],n) for a in ps] for i in range(n)]
 supports=[[i] for i in range(n)]+[[i,i+1] for i in range(n-1)]+([list(range(n))] if n>2 else [])
 terms=[(S,embed((.1+.2*rng.random())*herm(2**len(S)),S,n)) for S in supports]
 H=sum(a for S,a in terms); M=np.zeros((n,n))
 for S,a in terms:
  for i in S:
   for j in S:M[i,j]+=3*norm(a)
 for trial in range(5):
  F=herm(2**n); inf=np.array([sum(norm(comm(a,F)) for a in row) for row in As])
  lhs=np.array([sum(norm(comm(comm(H,a),F)) for a in row) for row in As])
  assert np.all(lhs<=M@inf+1e-10);count+=1
  t=.17; U=expm(-1j*t*H)
  moved=np.array([sum(norm(comm(U@a@U.conj().T-a,F)) for a in row) for row in As])
  assert np.all(moved<=(expm(t*M)-np.eye(n))@inf+1e-10);count+=1
  gamma=.7;tau=.03;omega=.4
  vals,V=np.linalg.eigh(H); dif=vals[:,None]-vals[None,:]
  k0=gamma/(1+1j*tau*omega)
  qs=[]
  for row in As:
   qrow=[]
   for a in row:
    aa=V.conj().T@a@V;K=V@(gamma*aa/(1+1j*tau*(omega+dif)))@V.conj().T;qrow.append(K-k0*a)
   qs.append(qrow)
  actual=np.array([sum(norm(comm(q,F)) for q in row) for row in qs])
  bound=gamma*tau*M@np.linalg.solve(np.eye(n)-tau*M,inf)
  assert np.all(actual<=bound+1e-10);count+=1
  flatA=[a for row in As for a in row]; flatQ=[q for row in qs for q in row]
  b=k0.real; g=8*b
  def Vcorr(G):return sum(comm(a,G)@q-q.conj().T@comm(a,G) for a,q in zip(flatA,flatQ))
  def D(G):return sum(2*b*(a@G@a-G) for a in flatA)
  def R(G):return 1j*comm(H,G)+D(G)+Vcorr(G)
  RF=R(F); deriv=0.
  for ap in flatA:
   G=1j*comm(ap,F); dG=1j*comm(ap,RF); es,vs=np.linalg.eigh(G); idx=np.argmax(abs(es)); vec=vs[:,idx]
   deriv+=np.sign(es[idx])*np.vdot(vec,dG@vec).real
   rem=sum(comm(comm(ap,aq),F)@q-q.conj().T@comm(comm(ap,aq),F)+comm(aq,F)@comm(ap,q)-comm(ap,q.conj().T)@comm(aq,F) for aq,q in zip(flatA,flatQ))
   assert norm(comm(ap,Vcorr(F))-Vcorr(comm(ap,F))-rem)<1e-10
  hs=max(sum(norm(a) for S,a in terms if i in S) for i in range(n)); k=max(map(len,supports));v=3*k*hs
  qbound=2*gamma*hs*tau;beta=12*gamma*k*hs*tau/(1-v*tau)
  I2=sum(norm(comm(aq,comm(ap,F))) for ap in flatA for aq in flatA)
  rhs=-(g-v-8*qbound-2*beta)*sum(inf)+2*qbound*I2
  assert deriv<=rhs+1e-9;count+=2
# Exact qubit noise intertwiner, all axes, arbitrary anisotropy.
bs=np.array([.17,.31,.53])
def noise(F,b):return sum(2*bj*(a@F@a-F) for a,bj in zip(ps,b))
for a in range(3):
 swapped=bs.copy(); others=[i for i in range(3) if i!=a];swapped[others]=swapped[others[::-1]]
 for F in [I,X,Y,Z]:
  assert norm(comm(ps[a],noise(F,bs))-noise(comm(ps[a],F),swapped))<1e-12;count+=1
print(f'PASS {count} finite numerical controls: general-operator local bound, unitary movement, complete exponential filters, and anisotropic noise intertwiner.')
print('Numerical diagnostics only; hand proofs and original thermal admission are not certified by these tests.')
