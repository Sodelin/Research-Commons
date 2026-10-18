"""Exact diagnostics for a conditional-qubit angular-prior route.
Not an all-copy bound, physical simulation, or full P1 theorem.
"""
import itertools
import sympy as s
r,c=s.symbols('r c', real=True)
x=s.symbols('x', real=True)
I=s.eye(2)
P=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
C=sum((s.kronecker_product(a,a) for a in P),s.zeros(4))
u=s.Matrix([0,0,1]); v=s.Matrix([x,0,c])
rotations=[]
for perm in itertools.permutations(range(3)):
 for signs in itertools.product((-1,1),repeat=3):
  R=s.zeros(3)
  for j in range(3): R[perm[j],j]=signs[j]
  if R.det()==1: rotations.append(R)
assert len(rotations)==24

def bloch(z): return (I+r*sum((z[i]*P[i] for i in range(3)),s.zeros(2)))/2
light=sum((s.kronecker_product(bloch(R*u),bloch(R*v)) for R in rotations),s.zeros(4))/24
expected=(s.eye(4)+r*r*c*C/3)/4
assert (light-expected).applyfunc(s.simplify)==s.zeros(4)
M0=s.eye(4)/4+r*r*C/24
M1=s.eye(4)/4+r*r*c*C/24
Delta=M1-M0
chi=s.factor(s.trace(Delta*M0.inv()*Delta))
assert s.factor(chi-r**4*(1-c)**2/((6+r*r)*(2-r*r)))==0
rho=bloch(u); sigma=bloch(v)
# Unit v means x^2+c^2=1; determinant is the same as rho.
assert s.factor(sigma.det().subs(x*x,1-c*c)-(1-r*r)/4)==0
fid=s.factor(s.trace(rho*sigma)+(1-r*r)/2)
assert s.factor(fid-(1-r*r*(1-c)/2))==0
# Time reversal iY conjugation sends every Hermitian Pauli to its negative.
Y=P[1]; U=s.I*Y
for a in P: assert U*a.conjugate()*U.inv()==-a
# Explicit second-spin example checks the two-weight sign.
U2=s.kronecker_product(U,U)
for a,b in itertools.product([I]+P, repeat=2):
 w=int(a!=I)+int(b!=I)
 T=s.kronecker_product(a,b)
 assert U2*T.conjugate()*U2.inv()==(-1)**w*T
print('PASS: 24 proper signed-permutation rotations give the exact two-copy twirl.')
print('PASS: angular chi-square = r^4(1-c)^2 / ((6+r^2)(2-r^2)).')
print('PASS: squared qubit fidelity = 1-r^2(1-c)/2.')
assert s.Rational(9,16)*s.Rational(1,3)/s.Rational(1,2) >= s.Rational(1,4)
assert s.Rational(1,4)/12 == s.Rational(1,48)
assert s.Rational(1,4)*s.Rational(1,48) == s.Rational(1,192)
print('PASS: one- and two-qubit antiunitary Pauli-weight signs.')
print('PASS: rational constants in the two-count mass-denominator lower bound.')
print('Scope: exact finite algebra only; no all-count prior bound, physical simulation, or full P1 result.')
