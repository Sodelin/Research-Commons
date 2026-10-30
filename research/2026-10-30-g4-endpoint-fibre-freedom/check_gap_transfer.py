import sympy as s
import json
z,ar,al,ad,br,bl,bd=s.symbols('z ar al ad br bl bd',positive=True)
checks=[]
for r in [4,5,6]:
 lam=lambda n:n*(n-1)//2
 A=s.Matrix([[ar,ad],[0,al]]);B=s.Matrix([[br,bd],[0,bl]])
 Einv=s.diag(z**(-lam(r)),z**(-lam(r-2)))
 E=s.diag(z**lam(r),z**lam(r-2))
 result=(Einv*A*E*B)[0,1]
 expected=ar*bd+z**(-(2*r-3))*ad*bl
 assert s.simplify(result-expected)==0
 assert s.simplify((Einv*A*E*B)[0,0]-ar*br)==0
 assert s.simplify((Einv*A*E*B)[1,1]-al*bl)==0
 checks.append(r)
# Physical controls on lead and moved-to-gap survival, with both signs of t.
for zz in [s.Rational(4,5),s.Rational(5,4)]:
 lead=s.Rational(1,2)/zz;gap=s.Rational(1,2)*zz
 assert 0<lead<1 and 0<gap<1 and lead*gap==s.Rational(1,4)
# Two cut tangent columns: first Dev4=0, first Dev5!=0, second Dev4!=0.
x,y,w=s.symbols('x y w',nonzero=True)
J=s.Matrix([[0,x],[y,w]])
assert J.det()==-x*y
print(json.dumps(dict(status='PASS',exact_gap_identity_arities=checks,positive_duration_controls=['z=4/5','z=5/4'],two_cut_determinant=str(J.det()),scope='Exact symbolic composition and physical gap controls. Source diagonals/defects use inherited receiver; full target-fibre insertion is hand IFT, not numerically constructed.'),indent=2))
