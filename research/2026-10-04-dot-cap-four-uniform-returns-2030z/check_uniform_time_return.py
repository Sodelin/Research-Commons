"""Exact finite coefficient identities for the uniform-time cap-four return candidate. Not a full G3 theorem."""
import sympy as S
from pathlib import Path
import json
T,L=S.symbols('T L');w=S.symbols('w1:4');order=6

def tr(expr):return S.Poly(S.expand(expr),T).truncate if False else S.Add(*(c*T**p[0] for p,c in S.Poly(S.expand(expr),T).terms() if p[0]<=order))
def lg(expr):
 u=tr(expr-1);power=1;out=0
 for k in range(1,order+1):power=tr(power*u);out+=S.Rational((-1)**(k-1),k)*power
 return tr(out)
def B(a,v):
 m=1-a*T;d=v*T**3
 return [1-a*T/2,tr((m**3+3*m+3*m*d)/4),tr((2*m**6+30*m**4*d+30*m**2*d**2+2*d**3+8*m**3+24*m*d+6*m**2-6*d)/16), (a**3/S.Integer(12)-v/2)*T**3+a*v*T**4/4]
bs=[B(S.Integer(a),v) for a,v in zip([1,2,1],w)]
z=1-L*T
q1,q2,q3=[b[0] for b in bs];r1,r2,r3=[b[2] for b in bs];c1,c2,c3=[b[3] for b in bs]
D=tr(c1+tr(r1*z**6*c2)+tr(r1*z**6*r2*z**6*c3))
C=tr(c1*z*q2*z*q3+r1*z**6*c2*z*q3+r1*z**6*r2*z**6*c3)
H=tr(D-C)
l3=tr(sum(lg(b[1])-3*lg(b[0]) for b in bs))
new4=tr(sum(lg(b[2])-4*lg(b[1])+6*lg(b[0]) for b in bs))
F=[C/T**3,H/T**4,new4/T**4]
f=[[S.expand(a).coeff(T,k) for k in range(3)] for a in F]
base=S.Matrix([r[0] for r in f]);A=base.jacobian(w)
w0=S.solve(list(base),w)
sub=lambda x:S.factor(x.subs(w0))
v0=S.Matrix([w0[x] for x in w])
ft1=S.Matrix([r[1] for r in f]);ft2=S.Matrix([r[2] for r in f])
v1=S.simplify(-A.inv()*ft1.subs(w0))
v2=S.simplify(-A.inv()*(ft2.subs(w0)+ft1.jacobian(w).subs(w0)*v1))
g=[S.expand(l3/T**3).coeff(T,k) for k in range(3)]
out=S.factor(g[2].subs(w0)+(S.Matrix([g[1]]).jacobian(w).subs(w0)*v1)[0]+(S.Matrix([g[0]]).jacobian(w)*v2)[0])
expected_w=[(26*L+15)/(12*(4*L+3)),S.Rational(7,12),(13*L+12)/(6*(4*L+3))]
assert all(S.cancel(v0[i]-expected_w[i])==0 for i in range(3))
assert S.cancel(A.det()+3*(4*L+3)/16)==0
assert S.cancel(g[0].subs(w0))==0
assert S.cancel(g[1].subs(w0)+(S.Matrix([g[0]]).jacobian(w)*v1)[0])==0
assert S.cancel(out-3*(180*L**2+270*L-47)/64)==0
# The leading root is positive and simple by these exact identities.
ell=(S.sqrt(2965)-45)/60
assert S.simplify(180*ell**2+270*ell-47)==0
assert 2965>45**2
result={'status':'EXACT_SYMBOLIC_IDENTITIES_PASS','source_contract':'actual full cap-four independent quotient; g=1/2',
'w0':[str(S.factor(x)) for x in v0],'A':[[str(x) for x in row] for row in A.tolist()],
'detA':str(S.factor(A.det())),'leading_remaining_defect_T5':str(out),
'leading_positive_root':'(sqrt(2965)-45)/60','coefficient_T3_zero':True,'coefficient_T4_zero':True,
'role':'Finite rational coefficient identities supporting the separate analytic implicit-function proof; no finite screen extrapolation.'}
Path(__file__).with_name('UNIFORM-TIME-IDENTITY-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
