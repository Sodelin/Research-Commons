"""Check only root-count diagonal/chi jets; no forest-source bank."""
import sympy as s

u,r,beta=s.symbols('u r beta')
p=(1+r)/2
v=(1-beta)/4
q=s.exp(-u)
chi=v*(1-q)**2*((1-q)-(5+q)*beta)/3
expected={4:2*v*beta*(13*beta+3),5:90*v*beta**2,
          6:10*v*beta*(23*beta-3)}
for n in (4,5,6):
    lam=n*(n-1)//2
    raw=sum(s.binomial(n,j)*p**j*(1-p)**(n-j)
       *q**(j*(j-1)//2+(n-j)*(n-j-1)//2) for j in range(n+1))
    truncated=s.series(raw,u,0,4).removeO().expand()
    as_r=s.Poly(truncated,r)
    assert all(power[0]%2==0 for power,_ in as_r.terms())
    br=sum(co*beta**(power[0]//2) for power,co in as_r.terms())
    b2=s.series(q+2*v*(1-q),u,0,4).removeO()
    jet=s.series(s.log(br)-lam*s.log(b2)
        +s.Rational(3,2)*s.binomial(n,3)*chi,u,0,4).removeO().expand()
    assert all(s.factor(jet.coeff(u,j))==0 for j in (0,1,2))
    assert s.factor(jet.coeff(u,3)-expected[n])==0
    print(f'PASS: n={n}, cubic remainder =',s.factor(expected[n]))
print('Actual-binomial diagonal jets only; no forest bank or parameter grid')
