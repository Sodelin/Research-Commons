from fractions import Fraction as F
from pathlib import Path
import json
R=Path(__file__).resolve().parent
L=(1,3,6,10,15,21,28);r=F(1,2);p=F(1,1000000)
def solve(A,b):
 A=[[F(x) for x in row]+[F(v)] for row,v in zip(A,b)];n=len(A)
 for j in range(n):
  i=next(i for i in range(j,n) if A[i][j]);A[j],A[i]=A[i],A[j]
  z=A[j][j];A[j]=[x/z for x in A[j]]
  for i in range(n):
   if i!=j:
    z=A[i][j];A[i]=[x-z*y for x,y in zip(A[i],A[j])]
 return [A[i][-1] for i in range(n)]
def D(q):return [1-q**k for k in L]
def Dp(q):return [-k*q**(k-1) for k in L]
dot=lambda a,b:sum(x*y for x,y in zip(a,b))
c0=solve([[1]+[0]*6,[1]*7,list(L),D(r),Dp(r),D(r*r),Dp(r*r)],[-1,0,0,0,0,0,0])
C=dot(c0,D(r**3));assert C>0
f=[1-p+p*r**k for k in L]
Hp=[(1-r**k)/x for k,x in zip(L,f)]
Hq_over_p=[-k*r**(k-1)/x for k,x in zip(L,f)]
M=[[1]+[0]*6,[1]*7,list(L),Hp,Hq_over_p,D(r*r),Dp(r*r)]
b=[F(-1),F(0),F(0),F(0),F(0),F(3,2)*C*p,F(0)]
c=solve(M,b);assert all(dot(row,c)==v for row,v in zip(M,b))
Hpp=dot(c,[(1-r**k)**2/x**2 for k,x in zip(L,f)])
Hpq=dot(c,[-k*r**(k-1)/x**2 for k,x in zip(L,f)])
Hqq=dot(c,[-p*k*(k-1)*r**(k-2)/x+p*p*k*k*r**(2*k-2)/x**2 for k,x in zip(L,f)])
det=Hpp*Hqq-Hpq*Hpq;assert Hpp>0 and det>0
print('PASS exact rational critical equations at p=1/1000000,q=1/2')
print('PASS Hessian positive definite: Hpp>0, Hpp Hqq-Hpq²>0')
# Exact strict rare positivity: F_c=(1-q)^2 Q, rational Sturm via SymPy.
import sympy as S
z=S.symbols('z');poly=S.Poly(sum(S.Rational(x.numerator,x.denominator)*(1-z**k) for k,x in zip(L,c)),z)
Q=poly.exquo(S.Poly(z*(z-1)**2,z));assert Q.eval(0)>0 and Q.eval(1)>0 and Q.count_roots(0,1)==0
print('PASS active-killing normal: c.1=0; rare F_c(q)>0 for0<q<1; degree25 quotient positive on[0,1]')
# Atanh enclosure, eight terms; exact positive off-unit critical value.
lo=F(0);hi=F(0)
for coef,x in zip(c,f):
 t=(1-x)/(1+x);low=2*sum((t**(2*j+1)/F(2*j+1) for j in range(8)),F(0));up=low+2*t**17/(17*(1-t*t))
 lo+=coef*(low if coef>=0 else up);hi+=coef*(up if coef>=0 else low)
assert 0<lo<=hi
print('PASS exact 8-term atanh interval gives0<lower<=c.H<=upper')
(R/'active-killing-minimum-certificate.json').write_text(json.dumps({'Lambda':L,'p':str(p),'q':str(r),'c0':[str(x) for x in c0],'C':str(C),'c':[str(x) for x in c],'Hessian':[str(Hpp),str(Hpq),str(Hqq)],'determinant':str(det),'Q_ascending':[str(x) for x in reversed(Q.all_coeffs())],'score_lower':str(lo),'score_upper':str(hi)},indent=2)+'\n')
