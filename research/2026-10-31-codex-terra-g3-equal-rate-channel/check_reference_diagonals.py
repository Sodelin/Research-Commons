"""Fair reference diagonals through cubic order and one scalar integral."""
import sympy as s

h,T,a=s.symbols('h T a',positive=True)
t=s.exp(-h)
x=t/(2-t)
b=t**2*(2-t)
for n in (4,5,6):
    lam=n*(n-1)//2
    raw=sum(s.binomial(n,j)*x**(j*(j-1)//2+(n-j)*(n-j-1)//2)
            for j in range(n+1))/2**n
    diag=s.series((t*b)**lam*raw,h,0,4).removeO()
    lognorm=s.series(s.log(diag)+3*lam*h,h,0,4).removeO().expand()
    assert s.simplify(lognorm+s.binomial(n,3)*h**3)==0
integral=-s.exp(-T)*s.integrate(s.exp(-9*a)*(2*a+4*T/3),(a,0,T))/3
closed=-s.Rational(2,243)*((1+6*T)*s.exp(-T)-(1+15*T)*s.exp(-10*T))
assert s.simplify(integral-closed)==0
print('PASS: log D_r(S) = -binom(r,3) h^3 + O(h^4), r=4,5,6')
print('PASS: fair-power diagonal-correction limit equals stated closed function')
print('No source bank, parameter grid, or full forest generator')
