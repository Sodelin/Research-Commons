"""Exact neutral-corner check for the tail-class correction; no source solve."""
import sympy as S
e,q=S.symbols('e q',positive=True)
L=21
p=1-e
f1=1-p+p*q
fL=1-p+p*q**L
j=fL/f1**L-1
assert S.simplify(j.subs(e,0))==0
coef=S.simplify(S.diff(j,e).subs(e,0))
assert S.simplify(coef-(q**(-L)-L/q+L-1))==0
z=(1-e)/e
assert S.limit(z,e,0,dir='+')==S.oo
print('PASS p->1: normalized defect tends to zero while odds diverge')
print('PASS first defect coefficient q^(-21)-21/q+20')
print('SCOPE: the q-only weak-class condition is impossible; small odds belong in its premise')
