"""Exact routing-sum/Jacobian checks, not a full forest compiler or G3 solver."""
from pathlib import Path
import json
import sympy as s

x,y,g=s.symbols('x y g')
v=1-g
variables=(x,y,g)
def lam(n): return n*(n-1)//2
def p(n,z): return (z**lam(n-1)-z**lam(n))/s.Integer(n-1)
def a(n,z):
    rates=[lam(n-2),lam(n-1),lam(n)]
    return sum(z**j/s.prod(k-j for k in rates if k!=j) for j in rates)
def diagonal(r):
    return s.Poly(sum(s.binomial(r,k)*g**k*v**(r-k)*x**lam(k)*y**lam(r-k) for k in range(r+1)),x,y,g).as_expr()
def triple(r):
    return s.Poly(sum(s.binomial(r-3,k)*(g**(k+3)*v**(r-3-k)*a(k+3,x)*y**lam(r-3-k)+v**(k+3)*g**(r-3-k)*a(k+3,y)*x**lam(r-3-k)) for k in range(r-2)),x,y,g).as_expr()
def cherries(r):
    same=2*sum(s.binomial(r-4,k)*(g**(k+4)*v**(r-4-k)*a(k+4,x)*y**lam(r-4-k)+v**(k+4)*g**(r-4-k)*a(k+4,y)*x**lam(r-4-k)) for k in range(r-3))
    opposite=2*g**2*v**2*sum(s.binomial(r-4,k)*g**k*v**(r-4-k)*p(k+2,x)*p(r-k-2,y) for k in range(r-3))
    return s.Poly(same+opposite,x,y,g).as_expr()
b={r:diagonal(r) for r in range(2,7)}
d={r:s.Poly(cherries(r)-2*triple(r),x,y,g).as_expr() for r in (5,6)}
boundary={x:s.Integer(0),y:s.Integer(1),g:s.Rational(1,2)}
interior={x:s.Rational(1,4096),y:s.Rational(4095,4096),g:s.Rational(1,2)}
def log_derivative(poly,t,point):
    return s.diff(poly,t).subs(point)/poly.subs(point)
def matrix_at(point):
    # P=log(b5/b2), Q=log(b6/b4), R=log|D5*b4/(2*D6*b2)|.
    weights=[[(b[5],1),(b[2],-1)],[(b[6],1),(b[4],-1)],[(d[5],1),(d[6],-1),(b[4],1),(b[2],-1)]]
    return s.Matrix([[sum(c*log_derivative(poly,t,point) for poly,c in row) for t in variables] for row in weights])
j0=matrix_at(boundary)
expected=s.Matrix([[s.Rational(4,3),s.Rational(19,3),-s.Rational(16,3)],[s.Rational(33,35),s.Rational(249,35),-s.Rational(132,35)],[s.Rational(17,30),s.Rational(19,15),-s.Rational(22,15)]])
assert j0==expected
assert j0.det()==s.Rational(492,175)
j1=matrix_at(interior)
det=s.factor(j1.det())
assert det!=0
assert d[5].subs(interior)<0 and d[6].subs(interior)<0
assert all(0<b[r].subs(interior)<1 for r in b)
assert (b[5]*b[4]-b[2]*b[6]).subs(interior)<0
fair={x:s.Rational(1,2),y:s.Rational(1,2),g:s.Rational(1,2)}
assert (b[5]*b[4]-b[2]*b[6]).subs(fair)==s.Rational(3483,8388608)
report={"scope":"Exact polynomial routing sums and three-coordinate Jacobian only; composition and topology counts require hand proof. No original G3 solver or legal observation/alphabet guard.","sympy_version":s.__version__,"boundary_matrix":[[str(z) for z in row] for row in j0.tolist()],"boundary_det":str(j0.det()),"strict_point":{str(k):str(v) for k,v in interior.items()},"padding":{"u":"1/2","w":"1/2","fixed_product":"1/4","fourth_log_coordinate_derivative":"18"},"strict_matrix":[[str(z) for z in row] for row in j1.tolist()],"strict_det":str(det),"strict_det_sign":int(s.sign(det)),"D5":str(d[5].subs(interior)),"D6":str(d[6].subs(interior)),"checks":"PASS"}
out=Path(__file__).with_suffix('.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print('PASS: boundary Jacobian = specified table, determinant 492/175')
print('PASS: explicit strict point x=1/4096, y=4095/4096, g=1/2')
print('Strict determinant sign:',s.sign(det))
print('Strict determinant numerator/denominator bit lengths:',int(s.numer(det)).bit_length(),int(s.denom(det)).bit_length())
print('PASS: D5,D6 negative; all b2...b6 strictly between zero and one')
print('PASS: both signs of dilation-ratio difference certified exactly')
print('Exact rational certificate written:',out.name)
