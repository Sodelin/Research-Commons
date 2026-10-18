"""Bounded exact identities only; not a replacement for the all-count proof."""
import sympy as s
from itertools import product
th,z,ell,d,mu=s.symbols('theta z ell delta mu', real=True)
f=30*th**2*(1-th)**2
h=(3-5*th)/(1-th)
assert s.integrate(f,(th,0,1))==1
assert s.integrate(f*h,(th,0,1))==0
assert s.integrate(s.cancel(f*h*h),(th,0,1))==15
assert s.integrate(s.cancel(f*th**2/(1-th)),(th,0,1))==1
assert s.limit(th*f,th,0)==0 and s.limit(th*f,th,1)==0
for allocations in [(1,1),(1,-1),(-1,-1)]:
    for bits in product([0,1],repeat=2):
        alt=0
        for sig,flip in product([-1,1],repeat=2):
            ps=[ell+sig*eps*d for eps in allocations]
            if flip==-1: ps=[1-p for p in ps]
            alt += s.prod(p if x else 1-p for p,x in zip(ps,bits))/4
        corr=(1-2*ell)**2+4*d*d*allocations[0]*allocations[1]
        signs=[2*x-1 for x in bits]
        assert s.expand((1-th)/4+th*alt-(1+th*corr*signs[0]*signs[1])/4)==0
n=s.symbols('n', integer=True, nonnegative=True)
assert s.expand(n**2*(n-1)**2-(n*(n-1)*(n-2)*(n-3)+4*n*(n-1)*(n-2)+2*n*(n-1)))==0
u=s.symbols('u')
pgf=s.exp(2*mu**2*(u-1))
moment=sum(c*u**j*s.diff(pgf,u,j) for j,c in [(4,1),(3,4),(2,2)])
expected=s.exp(4*mu**2)*(1296*mu**8+864*mu**6+72*mu**4)
assert s.simplify(moment.subs(u,3)-expected)==0
assert 4*1377*8==44064
assert 3840*8==30720
print('PASS: Beta normalization, zero score mean, score norm15, endpoint terms, theta integral1.')
print('PASS: all three two-copy allocations, all four outcomes, fixed shared flip/sign.')
print('PASS: falling-factorial and Poisson weighted-tail identities and constants.')
print('Scope: exact finite symbolic controls only; no full-P1 or physical execution claim.')
