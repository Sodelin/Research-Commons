"""Exact symbolic checks for P5 candidate24; no numerical quadrature or theorem prover.
Uses arbitrary real r0,e,r,f,d,t with the exact KMS substitution Im D=-t*r.
The bath integral positivity and operator-norm estimates are hand obligations.
"""
import hashlib
import json
from pathlib import Path
import platform
import sympy as s

I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); Y=s.Matrix([[0,-s.I],[s.I,0]]); Z=s.diag(1,-1)
kron=s.kronecker_product
II=s.eye(4)
P=(kron(Z,I)+kron(X,X))/s.sqrt(2)
Q=(kron(Z,I)-kron(X,X))/s.sqrt(2)
T=kron(Y,X)
U=kron(I,X); V=kron(Z,Z)
r0,e,r,f,d,t=s.symbols('r0 e r f d t', real=True)
k0=r0+s.I*e; C=r+s.I*f; D=d-s.I*t*r
basis=[II,P,Q,T]
axes=[[kron(A,I) for A in [X,Y,Z]],[kron(I,A) for A in [X,Y,Z]]]
checks=[]
def equal(label,lhs,rhs):
    diff=lhs-rhs
    ok=all(s.simplify(x)==0 for x in diff) if isinstance(diff,s.MatrixBase) else s.simplify(diff)==0
    if not ok: raise AssertionError((label,diff))
    checks.append(label)

def channel(A,rho):
    Ac=(A+P*A*P)/2; Aa=(A-P*A*P)/2
    K=k0*Ac+C*Aa-s.I*D*P*Aa
    return s.expand(K*rho*A-A*K*rho+A*rho*K.conjugate().T-rho*K.conjugate().T*A)

def group(j,rho):
    return sum((channel(A,rho) for A in axes[j]),s.zeros(4))

def twirl(rho): return (rho+U*rho*U+V*rho*V+U*V*rho*V*U)/4

for name,B in zip(['I','P','Q','T'],basis):
    equal(name+' Hermitian',B.conjugate().T,B)
    equal(name+' square',B*B,II)
for i,B in enumerate(basis):
    for j,Cb in enumerate(basis): equal(f'orthogonal {i} {j}',s.trace(B*Cb),4 if i==j else 0)
for name,W in [('U',U),('V',V)]:
    equal(name+' fixes H',W*P*W,P)
    for j,As in enumerate(axes):
        for k,A in enumerate(As):
            sign=s.simplify(s.trace(W*A*W*A)/4)
            assert sign in [-1,1]
            equal(f'{name} channel sign {j} {k}',W*A*W,sign*A)
equal('anticommuting U V',U*V,-V*U)
paulis=[I,X,Y,Z]
expected_kept={(0,0),(3,0),(1,1),(2,1)}
for i,A in enumerate(paulis):
    for j,B in enumerate(paulis):
        E=kron(A,B)
        equal(f'twirl {i} {j}',twirl(E),E if (i,j) in expected_kept else s.zeros(4))

mat1=s.Matrix([[0,0,0,0],[-8*r*t,-8*r,0,0],[0,0,-4*(r+r0),4*d],[0,0,-4*d,-4*(r+r0)]])
mat2=s.Matrix([[0,0,0,0],[-4*r*t,-4*r,4*r0,0],[4*r*t,4*r,-4*r0,0],[4*(e-f),-4*d,-4*d,-4*(r+r0)]])
for site,M in enumerate([mat1,mat2]):
    for j,B in enumerate(basis):
        expected=sum((M[i,j]*basis[i] for i in range(4)),s.zeros(4))
        equal(f'full grouped image {site+1} {j}',group(site,B),expected)
rhoG=(II-t*P)/4
Delta=f-t*d-e
equal('D1 Gibbs residual',group(0,rhoG),s.zeros(4))
equal('D2 Gibbs residual',group(1,rhoG),-Delta*T)
equal('Hamiltonian Gibbs residual',P*rhoG-rhoG*P,s.zeros(4))
equal('transverse determinant',s.Matrix([[-(r+r0),d],[-d,-(r+r0)]]).det(),(r+r0)**2+d**2)

# Frozen six-channel map is c times this unscaled map.
for i,A in enumerate(paulis):
    for j,B in enumerate(paulis):
        E=kron(A,B); w=int(i!=0)+int(j!=0)
        frozen=sum((a*E*a-E for As in axes for a in As),s.zeros(4))
        equal(f'frozen weight eigenvalue {i} {j}',frozen,-4*w*E)

a=s.symbols('a', positive=True)
c=s.pi**2/(768*s.sqrt(2)*a); lam=c/100
gamma=2*s.sqrt(2)*c/s.pi; tau=2*a/s.pi; b0=s.pi/(4*s.sqrt(2))
h=2*lam; omega=s.sqrt(2)*lam
equal('explicit gamma tau',gamma*tau,s.Rational(1,192))
equal('explicit b0 gamma',b0*gamma,c/2)
equal('explicit margin',8*b0*gamma-2*h-24*2*2**2*gamma*h*tau,197*c/50)
equal('explicit delta',2*omega*(1+24*gamma*tau),9*s.sqrt(2)*c/400)
assert s.Rational(1,192)<s.Rational(1,96)
assert s.Rational(1,50)<s.Rational(1,2)
assert (s.Rational(9,400)**2)*2<(s.Rational(4,3)**2)
checks.extend(['small bath box','small Hamiltonian box','faithful stationary bound'])

proof=Path(__file__).with_name('P5-COMMON-KMS-WEIGHT-OBSTRUCTION-24.md')
result={
 'status':'PASS',
 'checks':checks,
 'check_count':len(checks),
 'python_version':platform.python_version(),
 'sympy_version':s.__version__,
 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'candidate_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),
 'D1':str(mat1), 'D2':str(mat2),
 'scope':'Exact finite symbolic identities and explicit parameter arithmetic; not a formal proof, numerical integration, all-observable norm scan, or independent implementation of the hand theorem.'
}
print(json.dumps(result,indent=2))
