"""Bounded exact symbolic audit of the variable-N normal residual.

This checks the coefficient identity only. It does not execute source
localization, IFT bounds, a cutoff, a radius, or an actual finite witness.
"""
import sympy as S

e,u,tau=S.symbols('e u tau', real=True)
tp,tr=S.symbols('t_P t_r', real=True)
tx,ty=S.symbols('t_p t_q', real=True)
P2,R2,x2,y2=S.symbols('P2 R2 x2 y2', real=True)
k=tau-S.Rational(1,2)
P=u-e*k*u**2*tp+e**2*P2
Rshift=-e*k*u*tr+e**2*R2
X=-e*k*u**2*tx+e**2*x2
Y=-e*k*u**2*ty+e**2*y2
Frr,F3,F4=S.symbols('Frr F3 F4', real=True)
Bxx,Bxy,Byy=S.symbols('Bxx Bxy Byy', real=True)
# F(r)=F'(r)=F(s)=F'(s)=0. Thus F(R)=Frr*(R-r)^2/2
# through order e^2. The coefficient -e*P^2*F(R^2)/2 is O(e^3).
head=(Bxx*X**2+2*Bxy*X*Y+Byy*Y**2)/2
primary=P*Frr*Rshift**2/2+e**2*P**3*F3/3
secondary=-e**2*tau**2*u**4*F4/2
actual=S.expand(head+primary+secondary).coeff(e,2)
expected=u**3*(F3/3+Frr*tr**2*k**2/2+u*((Bxx*tx**2+2*Bxy*tx*ty+Byy*ty**2)*k**2/2-F4*tau**2/2))
assert S.expand(actual-expected)==0
assert not (actual.free_symbols & {tp,P2,R2,x2,y2})
print('PASS exact epsilon^2 normal residual and cancellation of higher implicit jets')

C0,C1,C2,C3=S.symbols('C0 C1 C2 C3', real=True)
Lu=u**3*(C0+C1*k**2+u*(C2*k**2-C3*tau**2))
assert S.expand(S.diff(Lu,tau)/u**3-(2*C1*k+u*(2*C2*k-2*C3*tau)))==0
assert S.expand((Lu.subs(tau,1)-Lu.subs(tau,S.Rational(3,4)))/u**3-(S.Rational(3,16)*C1+u*(S.Rational(3,16)*C2-S.Rational(7,16)*C3)))==0
print('PASS derivative and exact endpoint gap coefficients')

# Constructing literal N factors is exactly the displayed analytic block.
# Verify its coefficients as a formal scalar log-series, before projection.
z,q,l=S.symbols('z q l')
scalar=(S.log(1+e*P)-S.log(1+e*P*z))/e
# Replace P by a fresh independent symbol for this identity.
P0=S.symbols('P0')
scalar=(S.log(1+e*P0)-S.log(1+e*P0*z))/e
series=S.series(scalar,e,0,3).removeO().expand()
expected_scalar=P0*(1-z)-e*P0**2*(1-z**2)/2+e**2*P0**3*(1-z**3)/3
assert S.expand(series-expected_scalar)==0
print('PASS literal integer-block log-series coefficients')
print('SCOPE: symbolic identities only; analytic/source provider claims require hand review')
