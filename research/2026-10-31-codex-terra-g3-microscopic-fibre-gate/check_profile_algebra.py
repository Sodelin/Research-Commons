"""Check only polynomial changes of variables; no source-bank execution."""
import sympy as s

X, Y, A, z, y = s.symbols('X Y A z y')
f4 = X**2*(X-1)*(2*X**3-24*X**2*Y-X**2+24*X*Y**2+6*X*Y-X+6*Y)
f5 = X**2*(5*X**6-80*X**5*Y+140*X**4*Y**2-25*X**4-48*X**3*Y**3
    +300*X**3*Y+25*X**3-300*X**2*Y**2-250*X**2*Y+200*X*Y**2-5*X+30*Y)
g4 = s.factor((2*f4/X).subs({X:z/2,Y:y/(2*z)}))
g5 = s.factor((2*f5/X).subs({X:z/2,Y:y/(2*z)}))
assert s.denom(g4) == 8 and s.denom(g5) == 64
assert s.expand(g4.subs(z,0)+3*y*(y+1)) == 0
assert s.expand(g5.subs(z,0)-5*y*(5*y+3)) == 0
G1 = 2*A**3+X**3-6*Y*X**2-2*A-X
G2 = 2*f4.subs({X:A,Y:0})+f4
G3 = 2*f5.subs({X:A,Y:0})+f5
fair1 = (2*A)**2-4
bias1 = (2*X)**2-6*(4*X*Y)-4
assert s.expand(2*A*fair1+X*bias1-4*G1) == 0
assert s.expand(2*A*g4.subs({z:2*A,y:0})+X*g4.subs({z:2*X,y:4*X*Y})-2*G2) == 0
assert s.expand(2*A*g5.subs({z:2*A,y:0})+X*g5.subs({z:2*X,y:4*X*Y})-2*G3) == 0
assert s.expand(g4.subs({z:2,y:0})) == 0
assert s.expand(g5.subs({z:2,y:0})) == 0
H, h, n = s.symbols('H h n', positive=True)
L, T = H/4, 3*H/4
assert s.simplify((6/L)*s.Rational(2,45)-4/(5*T)) == 0
for r in (1, 2, 3):
    rate = 10-r*(r-1)//2
    assert s.simplify((6/L)*s.Rational(2,3)/(3*rate)-4/(rate*T)) == 0
assert s.simplify((n*s.Rational(1,4)*(2*h)**5/(H*h**4)).subs(H,4*n*h)-2) == 0
print('PASS: both scaled normal transforms and singular-boundary polynomials')
print('PASS: exact weighted three-equation identities and reference zero')
print('PASS: four endpoint coefficients and reference source-cost ratio')
print('Input: saved displayed polynomials only; no archive, source engine or grid')
