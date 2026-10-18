"""Finite controls for the accompanying all-dimension hand-proof candidate.

Exact rational matrix identities are separated from floating-point diagnostics.
No sampling experiment, large-N verification, or certified numerical bound.
"""
from fractions import Fraction
import sympy as s
import numpy as np
from scipy.linalg import expm, eigvalsh

I = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)

def tensor(a, b):
    return s.kronecker_product(a, b)

def loss(v):
    h = (v + v.conjugate().T)/2
    return tensor(h, I)-tensor(I, h)+(tensor(v.conjugate().T*v, I)+tensor(I,v*v.conjugate().T))/2

def expectation(r, a):
    return s.simplify(s.trace(r*a))

states = [(I+u*X+v*Z)/2 for u,v in [
    (s.Rational(0),s.Rational(0)),
    (s.Rational(1,3),s.Rational(1,4)),
    (s.Rational(-1,2),s.Rational(1,3)),
    (s.Rational(3,5),s.Rational(4,5)),
]]
vs = [Z/2, (X+s.I*Z)/4, s.Matrix([[s.Rational(1,4),s.I/3],[s.Rational(1,5),-s.Rational(1,6)]]),
      (I+X+s.I*Y)/5, (2*X-Z+s.I*I)/6]
exact_moments=0
numeric_exp=0
for rho in states:
    omega=tensor(rho,rho)
    for v in vs:
        # Frobenius norm bounds the operator norm by one for these controls.
        assert expectation(I,v.conjugate().T*v)<=1
        d=loss(v)
        q=expectation(rho,(v.conjugate().T*v+v*v.conjugate().T)/2)
        assert expectation(omega,d)==q
        assert q>=0
        assert expectation(omega,d*d)<=6*q
        exact_moments+=1
        dn=np.array(d).astype(complex)
        on=np.array(omega).astype(complex)
        value=np.trace(on@expm(-dn/12)).real
        assert value<=1+1e-12
        numeric_exp+=1

# Rational, noncommuting inverse-Jensen checks. Positivity is checked using
# all principal minors, not a floating eigenvalue tolerance.
def psd_exact(a):
    from itertools import combinations
    assert a==a.conjugate().T
    return all(s.simplify(a.extract(ix,ix).det())>=0
               for r in range(1,a.rows+1) for ix in combinations(range(a.rows),r))

q1=s.Matrix([[2,s.Rational(1,3)],[s.Rational(1,3),1]])
q2=s.Matrix([[1,s.I/4],[-s.I/4,3]])
assert q1*q2 != q2*q1
inverse_checks=0
for p in [s.Rational(1,7),s.Rational(1,2),s.Rational(5,6)]:
    avg=p*q1+(1-p)*q2
    gap=p*q1.inv()+(1-p)*q2.inv()-avg.inv()
    assert psd_exact(gap)
    # Adding a positive discarded component decreases the inverse.
    extra=s.Matrix([[s.Rational(1,2),s.Rational(1,4)],[s.Rational(1,4),s.Rational(1,2)]])
    assert psd_exact(avg.inv()-(avg+extra).inv())
    inverse_checks+=2

# The deterministic witness-rescaling identity for unequal, noncommuting states.
rho=states[1]
sigma=(I-s.Rational(2,5)*Y+s.Rational(1,5)*Z)/2
omega=tensor(rho,sigma)
scaling_checks=0
for v in vs:
    f=expectation(omega,loss(v))
    q=(expectation(rho,v.conjugate().T*v)+expectation(sigma,v*v.conjugate().T))/2
    for a in [s.Rational(1,2),s.Rational(1,3),s.Rational(3,4)]:
        assert expectation(omega,loss(a*v))==s.simplify(a*f-a*(1-a)*q)
        scaling_checks+=1

# Numeric noncommuting mixture controls for n=1,2,3. These are diagnostics.
rho=np.array((I+s.Rational(3,5)*Z)/2).astype(complex)
sigma=np.array((I-s.Rational(3,5)*Z)/2).astype(complex)
omega=np.kron(rho,sigma)
d_ops=[np.array(loss(v)).astype(complex) for v in [-Z/2,-X/3,(Y+Z/5)/3]]
weights=np.array([0.3,0.2,0.5])
def power_tensor(a,n):
    ans=np.ones((1,1),complex)
    for _ in range(n): ans=np.kron(ans,a)
    return ans
mixture_checks=0
for n in [1,2,3]:
    terms=[power_tensor(expm(-d/12),n) for d in d_ops]
    a=sum(p*t for p,t in zip(weights,terms))
    eye=np.eye(a.shape[0])
    tau=4
    resolvent=np.linalg.inv(a+tau*eye)
    effect=eye-tau*resolvent
    assert min(eigvalsh(effect))>=-1e-11
    assert max(eigvalsh(effect))<=1+1e-11
    # Retain the first two noncommuting exponential terms as an arbitrary
    # positive subset: this checks the matrix inequality, not goodness of both.
    p=weights[:2].sum()
    rhs=sum((weights[j]/p)*np.linalg.inv(p*terms[j]+tau*eye) for j in [0,1])
    assert min(eigvalsh(rhs-resolvent))>=-1e-11
    test_mean=np.trace(power_tensor(omega,n)@effect).real
    assert 0<=test_mean<=1
    mixture_checks+=1

print(f"PASS: {exact_moments} exact rational null moment identities/bounds")
print(f"PASS: {inverse_checks} exact rational noncommuting inverse comparisons")
print(f"PASS: {scaling_checks} exact rational witness-normalization identities")
print(f"DIAGNOSTIC PASS: {numeric_exp} floating null exponential moments")
print(f"DIAGNOSTIC PASS: {mixture_checks} noncommuting finite-copy smooth effects")
print("Finite controls supplement the hand proof; no all-N numerical certificate.")
