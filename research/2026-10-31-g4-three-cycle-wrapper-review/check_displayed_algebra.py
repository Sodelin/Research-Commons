# Independent scalar check of DISPLAYED hand formulas only; no forest/source bank.
import sympy as s
x,g,P1,P3,ES,ns=s.symbols('x g P1 P3 ES ns')
w=g*(1-g);Du=1-g+g*x;Dv=1-(1-g)*(1-x)
s1=g*x*x+1-g;s1m=(1-g)*x*x+g
cx=(x-x**3)/2;tx=(1-x)**2*(2+x)/6
U=P1/Du;dB=P3*Du/(x*P1);nU=ES*P1/(P3*Du*s1);nB=ns/(x**3*nU)
cB=(dB-nB)/2;tB=(nB-3*dB+2)/6;cU=(U-nU)/2;tU=(nU-3*U+2)/6
DE=U*(tB*Du+cB*(g*cx+(1-g)*(1-x))+nB*(1-g)*tx)+cU*(cB*x*s1+nB*(1-g)*cx)
K0=P1/3-P3/4-ES/4+ns/4;K1=-P3*ns/(12*ES)
assert s.factor(DE-K0-K1*s1*s1m/x**2)==0
DC=g*cB*(tx+(1-U)*cx)+tU*(cB*x*s1+nB*(1-g)*cx)
mirror=-(1-2*g)*(P3*ns/(P1*ES))*w*(1-x)**3*(1+x)*(1+x+x*x)/(6*x**3)
assert s.factor(DC-DC.subs(g,1-g)-mirror)==0
u,n,d=s.symbols('u n d')
et=d*(g*(tx+cx*(1-u)+x**3*(n-3*u+2)/6)+(1-g)*x*(n-3*u+2)/6)
eS=d*x*s1*n
assert s.factor(6*et-eS-d*(2*Dv-3*u*x))==0
print('PASS C3, C4a elimination, mirror identity from displayed scalar expressions')
print('No source engine, bank, physical execution or transitive supplier verification')
