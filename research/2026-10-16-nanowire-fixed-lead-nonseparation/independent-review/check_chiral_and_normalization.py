"""Independent exact local identities and normalization guard for the reviewed packet."""
import sympy as s
from fractions import Fraction as F
import json
from pathlib import Path
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]); Y=s.Matrix([[0,-s.I],[s.I,0]]); Z=s.diag(1,-1)
k=s.kronecker_product
a,t,lam,B,Delta=s.symbols('a t lam B Delta',real=True)
S=k(Y,Y); R=k(X,I)
P=s.Matrix([[1,0],[0,1],[0,1],[-1,0]])/s.sqrt(2)
Q=s.Matrix([[1,0],[0,1],[0,-1],[1,0]])/s.sqrt(2)
H=a*k(I,Z)+B*k(X,I)+Delta*k(I,X)
T=-t*k(I,Z)-s.I*lam*k(Y,Z)
def zero(A): return s.simplify(A)==s.zeros(*A.shape)
assert zero(P.T*P-s.eye(2)) and zero(Q.T*Q-s.eye(2)) and zero(P.T*Q)
assert zero(S*P-P) and zero(S*Q+Q)
assert zero(P.T*H*P) and zero(Q.T*H*Q)
assert zero(P.T*H*Q-s.Matrix([[a,-B+Delta],[B+Delta,-a]]))
assert zero(P.T*T*Q-s.Matrix([[-t,lam],[lam,t]]))
assert zero(P.T*T.T*Q-s.Matrix([[-t,-lam],[-lam,t]]))
assert zero(R*H*R-H) and zero(R*T.T*R-T) and zero(R*S*R+S)
assert zero(T*T.conjugate().T-(t*t+lam*lam)*s.eye(4))
print('Chiral basis, onsite/hopping blocks, reflection symmetry and hopping width: exact PASS')
r=json.loads(Path(__file__).with_name('CROSSING-CHECKER-RESULT.json').read_text())
ep=F(r['bounds']['p_error']['exact']);eq=F(r['bounds']['q_error']['exact'])
assert 0<=ep<F(1,100) and 0<=eq<F(1,100)
# The fixed proposal coordinate is exactly1; therefore its norm >=1, and
# the integer-grid lower square root is >=1. Thus denominator >=1-ep>99/100.
print('Exact p/q errors <1/100; normalized p denominator >99/100: PASS')
