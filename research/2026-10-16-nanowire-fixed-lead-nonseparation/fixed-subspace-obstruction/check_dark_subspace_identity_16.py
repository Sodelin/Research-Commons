"""Own exact local-matrix controls for candidate16; not a proof of all collisions."""
import sympy as s
X=s.Matrix([[0,1],[1,0]])
Y=s.Matrix([[0,-1],[1,0]]) # -i sigma_y
Tz=s.diag(1,-1); Tx=X; I=s.eye(2)
Z=s.kronecker_product(X,I)
SO=s.kronecker_product(Y,Tz)
R1=s.kronecker_product(I,Tz);R2=s.kronecker_product(I,Tx)
comm=lambda a,b:a*b-b*a
assert comm(Z,comm(Z,SO))==4*SO
assert comm(Z,R1)==s.zeros(4) and comm(Z,R2)==s.zeros(4)
assert SO.det()!=0 and R1.det()!=0
print('PASS exact spin/Nambu double commutator, onsite commutation, invertible neighbor factors; SymPy',s.__version__)
print('Scope: local algebra supporting the fixed-subspace argument, not a global collision search.')
