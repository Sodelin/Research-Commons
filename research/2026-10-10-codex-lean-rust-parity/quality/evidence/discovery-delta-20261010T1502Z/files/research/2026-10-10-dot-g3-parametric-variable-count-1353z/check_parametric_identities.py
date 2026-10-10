"""Exact identities for the parameterized certificate theorem.
No new certificate instance, radius, RCF search or source witness is executed.
The head quadratic coefficient Qh stands for t_ret^T Hess(c.B) t_ret
in arbitrary finite head dimension; no fixed number of heads is substituted.
"""
import sympy as S
r,e,u,tau = S.symbols('r e u tau', real=True)
tP,tr,P2,R2,Qh,Frr,F3,F4=S.symbols('tP tr P2 R2 Qh Frr F3 F4',real=True)
k=tau-S.Rational(1,2)
P=u-e*k*u*u*tP+e*e*P2
Rdelta=-e*k*u*tr+e*e*R2
head=e*e*k*k*u**4*Qh/2
primary=P*Frr*Rdelta**2/2+e*e*P**3*F3/3
secondary=-e*e*tau*tau*u**4*F4/2
coefficient=S.expand(head+primary+secondary).coeff(e,2)
expected=u**3*(F3/3+Frr*tr**2*k*k/2+u*(Qh*k*k/2-F4*tau*tau/2))
assert S.expand(coefficient-expected)==0
assert not coefficient.has(tP,P2,R2)
print('PASS arbitrary-head quadratic-form residual and higher-jet cancellation')
C0,C1,C2,C3=S.symbols('C0 C1 C2 C3',real=True)
Lu=u**3*(C0+C1*k*k+u*(C2*k*k-C3*tau*tau))
assert S.expand(S.diff(Lu,tau)-u**3*(2*C1*k+u*(2*C2*k-2*C3*tau)))==0
assert S.expand((Lu.subs(tau,1)-Lu.subs(tau,S.Rational(3,4)))/u**3-(3*C1+u*(3*C2-7*C3))/16)==0
print('PASS derivative and endpoint gap with unrestricted C3 sign')
Kr=3*(1-r)-(1-r**3)
assert S.factor(Kr)==(r-1)**2*(r+2)
assert S.expand(Kr-(1-r)**2*(r+2))==0
print('PASS rational-residue numeric base inversion exponent')
v,P0,R,l=S.symbols('v P0 R l')
# Elementary rational integral: change of endpoints reconstructs the two logs.
x,y=S.symbols('x y',positive=True)
assert S.simplify(S.diff(S.log(1+e*P0*(y+v*(x-y)))/(e*P0*(x-y)),v)-1/(1+e*P0*(y+v*(x-y))))==0
print('PASS removable-block rational-integral antiderivative')
print('SCOPE: exact algebra only; source, analytic and finite-verifier claims require hand review')
