"""One exact 5/6-root EPPF comparison; no full source bank or grid."""
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import hashlib
import sympy as s

here=Path(__file__).resolve().parent
provider=here.parent/'2026-10-31-codex-terra-g4-retained-e-review'/'reviewed-sources'/'explore_exact_cell_residual.py'
assert hashlib.sha256(provider.read_bytes()).hexdigest()=='57dbab7215b5615c2993922da260b8b65a4f9e03559d5055cdfae1c0c58d15db'
spec=spec_from_file_location('pinned_eppf_provider',provider)
m=module_from_spec(spec);spec.loader.exec_module(m)
q,r,beta,d=s.symbols('q r beta d')
p=(1+r)/2
P=m.partition_probability

def to_beta(expr):
    poly=s.Poly(s.expand(expr),r)
    assert all(power[0]%2==0 for power,_ in poly.terms())
    return s.factor(sum(coeff*beta**(power[0]//2) for power,coeff in poly.terms()))

A4=to_beta(3*P((2,2),p,q,q)-2*P((3,1),p,q,q))
A5=to_beta(3*P((2,2,1),p,q,q)-2*P((3,1,1),p,q,q))
A6=to_beta(3*P((2,2,1,1),p,q,q)-2*P((3,1,1,1),p,q,q))
deletion=to_beta(-2*P((3,2,1),p,q,q)+2*P((4,1,1),p,q,q)-3*P((2,2,2),p,q,q))
v=(1-beta)/4
b2=q+2*v*(1-q)
chi=v*(1-q)**2*((1-q)-(5+q)*beta)/3
A5_saved=q*(1-beta)*(1-q)**2*((1-q)*(q**2+3*q+1)-beta*(3*q**3+6*q**2+14*q+7))/40
assert s.factor(A4-s.Rational(3,2)*chi)==0
assert s.factor(A5-A5_saved)==0
assert s.factor(A6-A5-deletion)==0

# J_n=b2^(-lambda_n) A_n for the LEFT pair-normalized bare cell.
numer=s.factor(A6-b2**5*A5)
fair=q*(q-1)**6*(7*q**4+17*q**3+32*q**2+7*q-7)/8960
assert s.factor(numer.subs(beta,0)-fair)==0
quot=s.cancel((numer/(v*(1-q)**3)).subs(q,1-d))
assert s.denom(quot)==1 or not s.denom(quot).has(d,beta)
assert s.factor(quot.subs(d,0)+6*beta**2)==0
rest=s.Poly(s.expand(quot+6*beta**2),d,beta)
for (pow_d,pow_beta),coeff in rest.terms():
    if pow_beta==0: assert pow_d>=3
    elif pow_beta==1: assert pow_d>=2
    else: assert pow_d>=1
print('PASS: original equal-arm A4=(3/2)chi, saved A5, and exact A6-A5 deletion')
print('PASS: left-normalized J6-J5 fair numerator =',s.factor(fair))
print('PASS: N/(v*d^3)=-6 beta^2 + O[d*(beta^2+beta*d+d^2)] as a polynomial')
print('Provider SHA-256 verified; direct symbolic 5/6-root EPPF only; no bank/grid')
