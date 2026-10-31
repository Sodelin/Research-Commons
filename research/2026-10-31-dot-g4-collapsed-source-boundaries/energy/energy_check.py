import sympy as s,json
x=s.symbols('x');r=(3*x*x-s.Rational(1,64))/2;k=-x**3/6+x/384+s.Rational(23,368640);b=x+s.Rational(1,4);mu=s.Rational(743,10560)
F=s.cancel(3*(6*k-2*mu*r)**2/(16*b)-mu*r*r)
print('F=',s.factor(F));print('poly=',s.Poly(F,x))
m1=-s.Rational(493,7680);m2=s.Rational(1,192);m3=-s.Rational(103,163840)
D=38063308800;P=s.Poly(F*D,x);low=P.coeff_monomial(x**3)*m3+P.coeff_monomial(x**2)*m2+P.coeff_monomial(x)*m1+P.coeff_monomial(1)
m4=m3*m3/m2;upper=s.factor((low+P.coeff_monomial(x**4)*m4)/D)
print('low=',low,'m4lower=',m4,'upper=',upper)
assert low==s.Rational(542646221,2560)
assert upper==-s.Rational(12455183,3118146256896)
# exact literal finite source witness, demonstrating nonempty hypothesis domain
from fractions import Fraction as Q
ns=[427,9216,437];ts=[-s.Rational(7,32),-s.Rational(15,256),-s.Rational(1,32)]
for f in [r,k,-96*k-s.Rational(1,256)*(1-s.Rational(1,10)+s.Rational(1,240))-8*b*r]:assert sum(n*f.subs(x,t) for n,t in zip(ns,ts))==0
print('actual 10080-cell linked source sums PASS')
word=[0]+[1]*9216+[2]*437+[0]*426
rs=[r.subs(x,t)for t in ts];bs=[b.subs(x,t)for t in ts];S=0;clock=0
for j,i in enumerate(word[:-1]):
 S+=rs[i];clock+=(1+bs[word[j+1]])*S
assert clock==-s.Rational(10077749325,65536)
assert clock+s.Rational(10077749325,4192)*rs[0]==0
print('actual 10080-cell order and positive first-gap correction PASS')
