"""Exact SymPy identity check only; no separator or global forcing computation."""
import sympy as s
q,p,g=s.symbols('q p g'); rs=[]
for n in (2,3,4):
 poly=s.expand(sum(s.binomial(n,j)*g**j*(1-g)**(n-j)*q**(-j*(n-j)) for j in range(n+1)))
 r=s.factor(s.rem(poly,g*g-g+p,g));assert not r.has(g);rs.append(r)
M=s.Matrix([[-q*s.diff(r,q)/r,s.diff(r,p)/r,n*(n-1)] for n,r in zip((2,3,4),rs)])
wanted=24*p*q*(2*p+q)*(4*p-1)*(q-1)**4/((2*p*q-2*p-q)*(3*p*q*q-3*p-q*q)*(2*p*p*q**4-8*p*p*q+6*p*p-4*p*q**4+4*p*q+q**4))
assert s.factor(M.det()-wanted)==0
for n,r in zip((2,3,4),rs):
 assert s.factor(s.diff(r,p)/r-8*(-q*s.diff(r,q)/r)+2*n*(n-1)).subs(p,s.Rational(1,4)).simplify()==0
print('PASS: exact n=2,3,4 tangent determinant and fair derivative identities.')
print('Determinant:',s.factor(wanted))
print('No numerical separator, QE search, global rival classification or Lean build executed.')
