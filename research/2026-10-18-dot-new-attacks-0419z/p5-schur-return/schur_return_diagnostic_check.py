"""Bounded exact algebra for SCHUR-RETURN-DIAGNOSTIC-0428Z.md.
Not verification of the analytic semigroup/measurement argument or full P5.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); Y=s.Matrix([[0,-s.I],[s.I,0]]); Z=s.diag(1,-1)
k=s.kronecker_product; II=s.eye(4)
P=(k(Z,I)+k(X,X))/s.sqrt(2)
Q=(k(Z,I)-k(X,X))/s.sqrt(2)
T=k(Y,X)
r0,e,r,f,d,th,om=s.symbols('r0 e r f d theta Omega',real=True)
k0=r0+s.I*e; C=r+s.I*f; D=d-s.I*th*r
axes=[k(A,I) for A in (X,Y,Z)]+[k(I,A) for A in (X,Y,Z)]
checks=[]
def eq(label,lhs,rhs):
    diff=lhs-rhs
    entries=list(diff) if isinstance(diff,s.MatrixBase) else [diff]
    if not all(s.simplify(x)==0 for x in entries): raise AssertionError((label,diff))
    checks.append(label)
def R(F):
    out=-s.I*om*(P*F-F*P)
    for A in axes:
        Ac=(A+P*A*P)/2; Aa=(A-P*A*P)/2
        K=k0*Ac+C*Aa-s.I*D*P*Aa
        out+=K*F*A-A*K*F+A*F*K.adjoint()-F*K.adjoint()*A
    return out
V=-12*r*th*P+4*r*th*Q+4*(e-f)*T
v2=16*(10*r*r*th*th+(e-f)**2)
eq('actual full drift',R(II),V)
eq('drift square',V*V,v2*II)
eq('maxmixed initial derivative',R(II/4),V/4)
for i,A in enumerate((P,Q,T)):
    eq(f'Pauli square {i}',A*A,II)
    for j,B in enumerate((P,Q,T)):
        if i!=j: eq(f'anticommutator {i} {j}',A*B+B*A,s.zeros(4))
    image=R(A)
    projected=sum((s.trace(B*image)/4*B for B in (P,Q,T)),s.zeros(4))
    eq(f'actual invariant algebra {i}',image,projected)

c=s.symbols('c',positive=True)
delta=9*s.sqrt(2)*c/400
g=4*c-delta
assert s.simplify(c/25-delta)>0
assert s.simplify(s.Rational(1,4)-delta/(2*g))>0
checks+=['delta below c/25','uniform actual trajectory positivity margin']
eq('radial derivative lower constant',s.Rational(194,225)/s.Rational(16,15),s.Rational(97,120))
assert s.Rational(97,120)>s.Rational(1,2)
checks.append('radial derivative exceeds v/2')
q=s.symbols('q',real=True)
mu2=(1+q)/2*(1-q)**2+(1-q)/2*(-1-q)**2
mu4=(1+q)/2*(1-q)**4+(1-q)/2*(-1-q)**4
eq('Bernoulli variance',mu2,1-q*q)
eq('Bernoulli fourth moment',mu4,1+2*q*q-3*q**4)
eq('fourth moment global upper certificate',s.Rational(4,3)-mu4,3*(q*q-s.Rational(1,3))**2)
eq('Holder lower constant',(s.Rational(3,4))**s.Rational(3,2)/s.sqrt(3),s.Rational(3,8))
eq('time integral lower constant',s.Rational(3,8)*s.Rational(1,2)*s.Rational(1,16),s.Rational(3,256))
eq('root actual frozen rate',sum((c*(A*Z*A-Z) for A in (X,Y,Z)),s.zeros(2)),-4*c*Z)

# Upper-triangular actual-projection algebra, independent of block entries.
c1,c2,d11,d12,d21,d22=s.symbols('c1 c2 d11 d12 d21 d22')
Af=s.Matrix([[0,c1,c2],[0,d11,d12],[0,d21,d22]])
Pf=s.diag(1,0,0); Qf=s.eye(3)-Pf
Cf=Pf*Af*Qf; Df=Qf*Af*Qf
eq('no scalar-to-fast injection',Qf*Af*Pf,s.zeros(3))
for n in range(5): eq(f'actual Schur return coefficient {n}',Cf*(Df**n)*Qf,Pf*(Af**(n+1)))

path=Path(__file__)
print(json.dumps({'status':'PASS','check_count':len(checks),'checks':checks,'sympy_version':s.__version__,
 'checker_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
 'scope':'Exact finite algebra only. Analytic all-time and all-N arguments are hand proofs.'},indent=2))
