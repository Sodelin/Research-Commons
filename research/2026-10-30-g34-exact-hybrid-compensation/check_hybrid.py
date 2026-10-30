import sympy as s
x,y=s.Integer(21),s.Integer(17)
Q=s.Integer(0);a=s.Integer(1);b=s.Integer(1)
L=s.Integer(0);energy=s.Integer(0);residual=s.Integer(0)
for i,q in enumerate([s.Rational(1,2),s.Rational(3,4)]):
    f=lambda k:(1-q**k)/k
    t=b/a; c=Q+a/x
    interval_energy=(x-y)*t/2*(c*c*(q**(-(x-y))-1)/(x-y)-2*c*a/x*f(y)+(a/x)**2*f(x+y))
    energy+=interval_energy
    L+=Q*b*f(y)+a*b*(f(y)-f(x+y))/x
    Q+=a*f(x);a*=q**x;b*=q**y
    u,v,z,da,db=s.symbols(f'u{i} v{i} z{i} da{i} db{i}',nonzero=True)
    alpha=a*u;beta=b*v;Z=a*b*z;t=b/a
    e=beta-t*alpha;delta=Z-alpha*beta/2
    residual+=e*(Q+alpha/2)+delta
    L+=Z+Q*beta
    Q+=alpha
    a*=da;b*=db
    energy+=(b/a-t)*Q**2/2
assert s.cancel(L-(b/a*Q**2/2-energy+residual))==0
print('PASS exact hybrid identity, two finite ordinary gaps and two fully symbolic scalar source jumps/diagonal ratios; not physical source realization')
