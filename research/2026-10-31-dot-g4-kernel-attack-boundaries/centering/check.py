import sympy as s, json
from pathlib import Path

def mul(g,h):
 t,x,z,w=g; a,y,v,r=h
 return s.Matrix([t+a,x+y,z+v+x*a,w+r+2*x*v+x*x*a])
def U(a,u): return s.Matrix([a,a*u,a*a*u/2,a**3*u*u/3])
g=s.Matrix(s.symbols('t x z w')); h=s.Matrix(s.symbols('a y v r')); k=s.Matrix(s.symbols('b j l n'))
assoc=all(s.expand(e)==0 for e in mul(mul(g,h),k)-mul(g,mul(h,k)))
a,u,v,w=s.symbols('a u v w'); F=mul(mul(U(a,u),U(s.Integer(1),v)),U(s.Integer(1),w))
J=F.jacobian([a,u,v,w]).subs({a:1,u:1,v:2,w:3})
det=J.det()
e=s.symbols('e'); D=lambda z:s.Matrix([e*z[0],e*z[1],e**2*z[2],e**3*z[3]])
dilation=all(s.expand(v)==0 for v in D(mul(g,h))-mul(D(g),D(h)))
x,t=s.symbols('x t'); X=lambda z:s.Matrix([0,z,0,0]); T=lambda z:s.Matrix([z,0,0,0])
comm=mul(mul(mul(X(x),T(t)),X(-x)),T(-t))
expected=s.Matrix([0,0,x*t,x*x*t])
out={'associativity':assoc,'three_unit_jacobian':[[str(z) for z in row] for row in J.tolist()],'determinant':str(det),'dilation_automorphism':dilation,'signed_commutator':list(map(str,comm)),'signed_commutator_verified':all(s.expand(v)==0 for v in comm-expected),'status':'exact rational/polynomial controls; not an actual forest-kernel experiment'}
assert assoc and det==4 and dilation and out['signed_commutator_verified']
Path(__file__).with_name('CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
