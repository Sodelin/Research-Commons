"""Bounded controls for actual-PGM distortion. Not a general proof.
Uses NumPy/SciPy already installed; no remote code or runtime installation.
"""
import numpy as np
from scipy.linalg import expm, eigh
from math import cosh, sqrt

I=np.eye(2,dtype=complex)
P=[np.array([[0,1],[1,0]],complex),np.array([[0,-1j],[1j,0]],complex),np.diag([1.,-1.]).astype(complex)]

def kronall(xs):
    a=np.array([[1.]],complex)
    for x in xs:a=np.kron(a,x)
    return a

def mf(a,f):
    z,u=eigh((a+a.conj().T)/2)
    assert z.min()>0
    return (u*f(z))@u.conj().T

def trace(a):return float(np.trace(a).real)
def tn(a):return float(np.abs(eigh((a+a.conj().T)/2,eigvals_only=True)).sum())
def qstate(h,beta):
    a=expm(-beta*sum((h[j]*P[j] for j in range(3)),start=np.zeros((2,2),complex)))
    return a/trace(a)

def pgm(states,p,n):
    rs=[kronall([r]*n) for r in states]
    s=sum((q*r for q,r in zip(p,rs)),start=np.zeros_like(rs[0]))
    inv=mf(s,lambda x:1/np.sqrt(x))
    w=np.array([[p[i]*p[j]*trace(rs[i]@inv@rs[j]@inv) for j in range(len(p))]for i in range(len(p))])
    assert np.max(np.abs(w-w.T))<2e-10
    assert np.max(np.abs(w.sum(axis=0)-p))<2e-10
    assert w.min()>-2e-10
    return rs,s,inv,w

def scalar(rs,s,inv,w,p,x):
    b=sum(p*x*x)
    B=sum((p[i]*x[i]*rs[i] for i in range(len(p))),start=np.zeros_like(s))
    z,u=eigh(s)
    B0=u.conj().T@B@u
    gain_opt=float(np.sum(2*np.abs(B0)**2/(z[:,None]+z[None,:])).real)
    gain_pgm=trace(B@inv@B@inv)
    direct=float(np.sum(w*(x[:,None]-x[None,:])**2))
    formula=2*(b-gain_pgm)
    opt=b-gain_opt
    assert abs(direct-formula)<2e-10
    assert direct<=2*opt+2e-10
    return direct

# Deterministic, noncommuting finite ensembles, including correlated two-site priors.
hs=np.array([[[.7,.2,-.3],[-.4,.6,.1]],[[.1,-.5,.6],[.5,-.2,.3]],[[-.6,.3,.2],[.2,.1,-.7]],[[0.,0.,0.],[.3,-.3,.4]]])
p=np.array([.1,.2,.3,.4])
cases=0; scalar_checks=0; max_scalar_ratio=0.; max_trace_ratio=0.; max_identity_err=0.
for beta in [.4,1.1]:
 for N in [1,2]:
  one=[[qstate(hs[i,b],beta) for b in range(N)] for i in range(4)]
  states=[kronall(x) for x in one]
  H=[sum((sum((hs[i,b,a]*kronall([P[a] if c==b else I for c in range(N)]) for a in range(3)),start=np.zeros_like(states[0])) for b in range(N)),start=np.zeros_like(states[0])) for i in range(4)]
  logstates=[mf(r,np.log) for r in states]
  means=np.array([[trace(one[i][b]@P[a]) for b in range(N) for a in range(3)] for i in range(4)])
  theta=hs[:,:N,:].reshape(4,3*N)
  distances=np.array([[tn(states[i]-states[j])**2 for j in range(4)] for i in range(4)])
  jeff=np.array([[trace((states[i]-states[j])@(logstates[i]-logstates[j])) for j in range(4)]for i in range(4)])
  bloch_dist=((means[:,None,:]-means[None,:,:])**2).sum(axis=2)
  L=cosh(sqrt(3)*beta)**2
  assert np.max(distances-jeff)<2e-10
  assert np.max(jeff-L*bloch_dist)<2e-10
  for n in [1,2,3]:
   rs,s,inv,w=pgm(states,p,n)
   risk=float(np.sum(w*distances))
   q=0.
   for a in range(3*N):
    val=scalar(rs,s,inv,w,p,means[:,a]);q+=val;scalar_checks+=1
    assert val<=2/n+2e-10
    max_scalar_ratio=max(max_scalar_ratio,n*val/2)
   assert q<=6*N/n+2e-10
   assert risk<=L*q+2e-10
   max_trace_ratio=max(max_trace_ratio,risk*n/(6*L*N))
   breg=beta*np.sum(w[:,:,None]*(theta[:,None,:]-theta[None,:,:])*(means[None,:,:]-means[:,None,:]))
   jeff_avg=np.sum(w*jeff)
   err=abs(breg-jeff_avg);max_identity_err=max(max_identity_err,err)
   assert err<2e-10
   cases+=1
print(f'PASS: {cases} deterministic noncommuting product-state PGM cases, n=1,2,3; N=1,2; beta=.4,1.1.')
print(f'PASS: {scalar_checks} scalar quadratic comparisons, including exact PGM formula and factor-two inequality to floating tolerance 2e-10.')
print('PASS: reversibility, stationary marginals, Gibbs Bregman identity, Pinsker/tensor Bloch bound and final full-trace risk bound in every case.')
print(f'Max absolute Bregman identity residual: {max_identity_err:.3g}')
print(f'Max ratio to scalar 2/n bound: {max_scalar_ratio:.6g}')
print(f'Max ratio to full trace bound 6 L_beta N/n: {max_trace_ratio:.6g}')
print('These floating finite controls support implementation consistency only; the parameterized statements are hand proofs.')
