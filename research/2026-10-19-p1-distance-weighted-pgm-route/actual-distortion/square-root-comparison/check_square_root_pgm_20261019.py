"""Bounded floating controls only; no optimum-Bures or all-size execution claim."""
from itertools import product
import numpy as np

SEED = 202610191956
rng = np.random.default_rng(SEED)
I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)
ATOL = 3e-10

def herm(a):
    return (a+a.conj().T)/2

def fun(a, f):
    e, u = np.linalg.eigh(herm(a))
    if np.min(e) < -ATOL:
        raise AssertionError(('negative PSD eigenvalue', np.min(e)))
    return (u*f(np.maximum(e, 0)))@u.conj().T

def sqrt(a):
    return fun(a, np.sqrt)

def power(a, n):
    out = np.ones((1, 1), dtype=complex)
    for _ in range(n):
        out = np.kron(out, a)
    return out

def paulis(N):
    out=[]
    for words in product([I,X,Y,Z],repeat=N):
        p=np.ones((1,1),complex)
        for a in words:
            p=np.kron(p,a)
        out.append(p)
    return out

def tr(a):
    z=np.trace(a)
    assert abs(z.imag)<ATOL
    return float(z.real)

def losses(r,s):
    sr,ss=sqrt(r),sqrt(s)
    aff=tr(sr@ss)
    fid=float(np.linalg.svd(sr@ss,compute_uv=False).sum())
    t=float(np.abs(np.linalg.eigvalsh(herm(r-s))).sum())
    assert fid*fid<=aff+ATOL and aff<=fid+ATOL
    H=2*(1-aff);B=2*(1-fid);T=t*t
    assert B<=H+ATOL and H<=2*B+ATOL and T<=4*B+ATOL
    return H,B,T

max_identity=0.
count=0
for N in [1,2]:
    d=2**N
    basis=paulis(N)
    for beta in [.4,1.1]:
        for n in [1,2,3] if N==1 else [1,2]:
            for trial in [0,1]:
                states=[]
                for j in range(3):
                    coefficients=rng.uniform(-.8,.8,len(basis)-1)
                    H=sum(c*p for c,p in zip(coefficients,basis[1:]))
                    e,u=np.linalg.eigh(H)
                    weights=np.exp(-beta*(e-e.min()))
                    states.append((u*(weights/weights.sum()))@u.conj().T)
                assert np.linalg.norm(states[0]@states[1]-states[1]@states[0])>1e-9
                pri=rng.uniform(.2,1.,3);pri/=pri.sum()
                R=[power(r,n) for r in states]
                S=sum(p*r for p,r in zip(pri,R))
                vals,vecs=np.linalg.eigh(herm(S))
                assert vals.min()>1e-12
                inv=(vecs*(vals**-.5))@vecs.conj().T
                effects=[p*inv@r@inv for p,r in zip(pri,R)]
                W=np.array([[pri[i]*tr(R[i]@effects[j]) for j in range(3)] for i in range(3)])
                assert np.max(np.abs(W-W.T))<ATOL
                assert np.max(np.abs(W.sum(axis=0)-pri))<ATOL
                target=np.array([[losses(r,s) for s in states] for r in states])
                risks=(W[:,:,None]*target).sum(axis=(0,1))
                roots=[sqrt(r) for r in states]
                labels=np.array([[tr(E@root)/np.sqrt(d) for E in basis] for root in roots])
                assert np.max(abs((labels*labels).sum(axis=1)-1))<ATOL
                V=0.;q_formula=0.
                for a in range(d*d):
                    x=labels[:,a]
                    b=float(pri@(x*x))
                    B=sum(p*xx*r for p,xx,r in zip(pri,x,R))
                    Bt=vecs.conj().T@B@vecs
                    Lt=2*Bt/(vals[:,None]+vals[None,:])
                    L=vecs@Lt@vecs.conj().T
                    V+=b-tr(B@L)
                    q_formula+=2*(b-tr(B@inv@B@inv))
                max_identity=max(max_identity,abs(risks[0]-q_formula))
                assert abs(risks[0]-q_formula)<ATOL
                assert risks[0]<=2*V+ATOL
                # ONE common projective measurement and state estimator for every label.
                size=d**n
                G=rng.normal(size=(size,size))+1j*rng.normal(size=(size,size))
                U=np.linalg.qr(G)[0]
                obs=[np.outer(U[:,a],U[:,a].conj()) for a in range(size)]
                joint=np.array([[pri[i]*tr(R[i]@E) for E in obs] for i in range(3)])
                risk_est=np.zeros(3)
                for a in range(size):
                    mass=joint[:,a].sum()
                    post=joint[:,a]/mass
                    C=sum(p*r for p,r in zip(post,roots))
                    sigma=C@C/tr(C@C)
                    for i in range(3):
                        risk_est+=joint[i,a]*np.array(losses(states[i],sigma))
                assert V<=risk_est[0]+ATOL
                assert risks[0]<=2*risk_est[0]+ATOL
                assert risks[1]<=4*risk_est[1]+ATOL
                assert risks[2]<=16*risk_est[1]+ATOL
                count+=1
print('PASS: admitted noncommuting Gibbs ensembles:',count)
print('N=1,2; all one- or two-body Pauli coefficients in [-0.8,0.8]; beta=0.4,1.1.')
print('n=1,2,3 for N=1; n=1,2 for N=2; same n-copy PGM and common estimator.')
print('Checked full-coordinate Parseval, scalar aggregate, and H/B/full-trace inequalities.')
print('Maximum PGM Hilbert-risk identity residual:',format(max_identity,'.17g'))
print('Tolerance:',ATOL,'; RNG seed:',SEED)
print('These are floating-point controls, not computation of optimal Bures risk or a general proof.')
