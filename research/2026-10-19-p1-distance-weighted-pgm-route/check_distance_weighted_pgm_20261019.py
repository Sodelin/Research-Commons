"""Bounded controls for the authored PGM route check; not a P1 certificate."""
import sympy as s
import mpmath as mp

u=s.symbols('u', real=True)
d=s.sqrt(1-2*u*u)
off=((1+d)/s.sqrt(2+2*d)-1)/2
assert s.simplify(s.limit(off/u**2,u,0)) == -s.Rational(1,8)
print('EXACT: v=0 square-root off-diagonal coefficient = -1/8')

X=s.Matrix([[0,1],[1,0]])
Z=s.diag(1,-1)
I=s.eye(2)
for r in [s.Rational(0),s.Rational(1,2),s.Rational(3,5),s.Rational(1)]:
    states=[(I+r*Z)/2,(I+r*X)/2,(I-r*Z)/2]
    uu=s.sqrt(2/(3+r)); vv=s.sqrt(2/(3-r))
    B=(uu+vv)/2*I+(uu-vv)/2*X
    effects=[s.simplify(B*q*B) for q in states]
    assert s.simplify(sum(effects,s.zeros(2))-I)==s.zeros(2)
    actual=s.simplify(s.trace(states[0]*effects[2]))
    expected=3/(9-r*r)-r*r/s.sqrt(9-r*r)
    assert s.simplify(actual-expected)==0
print('EXACT: four qubit PGM normalization/probability controls passed')

mp.mp.dps=160
theta=mp.pi/8
b=mp.cos(theta); c=mp.cos(2*theta)
assert b**4>c>0
print('NUMERICAL: theta=pi/8, accuracy a=1; neighbors below a, endpoints above a')
assert 2*mp.sin(theta)<1<2*mp.sin(2*theta)
for n in [1,2,10,50,100,300]:
    uu=b**n; vv=c**n
    G=mp.matrix([[1,uu,vv],[uu,1,uu],[vv,uu,1]])
    eig,Q=mp.eigsy(G)
    assert min(eig)>-mp.mpf('1e-145')
    root=Q*mp.diag([mp.sqrt(max(mp.mpf(0),z)) for z in eig])*Q.T
    dd=mp.sqrt(max(mp.mpf(0),1+vv-2*uu**2))
    formula=((1+vv+dd)/mp.sqrt(2+vv+2*dd)-mp.sqrt(1-vv))/2
    assert abs(root[2,0]-formula)<mp.mpf('1e-145')
    p=formula**2
    print('n=%d p/c^n=%s p/b^(4n)=%s' %
          (n,mp.nstr(p/c**n,14),mp.nstr(p/b**(4*n),14)))
print('PASS: finite controls only; general inequalities and Gibbs admission are hand arguments')
