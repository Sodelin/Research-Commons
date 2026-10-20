import sympy as s
from itertools import product
import json
I=s.eye(2); X=s.Matrix([[0,1],[1,0]]);Y=s.Matrix([[0,-s.I],[s.I,0]]);Z=s.diag(1,-1)
axes=[X,Y,Z]; basis=[s.kronecker_product(a,b) for a,b in product([I,X,Y,Z], repeat=2)]
As=[[s.kronecker_product(a,I) if i==0 else s.kronecker_product(I,a) for a in axes]for i in range(2)]
b=[[s.Rational(1,7),s.Rational(2,7),s.Rational(4,7)],[s.Rational(3,11),s.Rational(5,11),s.Rational(7,11)]]
def c(A,B):return A*B-B*A
def noise(F,bs):return sum((2*bs[i][a]*(As[i][a]*F*As[i][a]-F) for i in range(2) for a in range(3)),s.zeros(4))
def zero(A):return A==s.zeros(4)
counts={'intertwiner':0,'projected_hamiltonian':0,'projected_jacobi':0,'local_isotropic_damping':0}
for i in range(2):
 for a in range(3):
  S=As[i][a]; P=lambda F:(F-S*F*S)/2
  swap=[row.copy() for row in b]; others=[j for j in range(3)if j!=a];swap[i][others[0]],swap[i][others[1]]=swap[i][others[1]],swap[i][others[0]]
  for F in basis:
   G=c(S,F)
   assert zero(c(S,noise(F,b))-noise(G,swap));counts['intertwiner']+=1
   local=sum((2*(A*G*A-G)for A in As[i]),s.zeros(4))
   assert zero(local+8*G);counts['local_isotropic_damping']+=1
   for H in basis:
    He=(H+S*H*S)/2
    assert zero(P(c(H,G))-c(He,G));counts['projected_hamiltonian']+=1
    assert zero(c(S,c(H,F))-c(He,G)-P(c(c(S,H),F)));counts['projected_jacobi']+=1
# An explicit witness that unprojected H leaves the anti-commuting range.
S=As[0][2]; H=As[0][0]; G=As[0][1]
assert not zero((c(H,G)-S*c(H,G)*S)/2-c(H,G))
print(json.dumps({'status':'PASS','exact_checks':counts,'total':sum(counts.values()),'unprojected_hamiltonian_range_failure_confirmed':True,'scope':'Exact two-qubit Pauli-basis identities; does not certify general differential estimates or full P5.'},indent=2))
