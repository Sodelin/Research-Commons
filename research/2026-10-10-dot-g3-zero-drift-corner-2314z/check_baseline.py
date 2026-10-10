#!/usr/bin/env python3
"""Exact local baseline-normal screen; no nonlinear classification check."""
import json
import sympy as s
from pathlib import Path
L=[1,3,6,10,15,21,28]
J=s.Matrix([[l,1,*sum(([((1-q**l)/(1-p+p*q**l)),(-p*l*q**(l-1)/(1-p+p*q**l))] for p,q in [(s.Rational(1,2),s.Rational(1,2)),(s.Rational(1,2),s.Rational(1,3))]),[]),-int(l==1)] for l in L])
b=J.inv()[0,:]
assert b*J==s.Matrix([[1,0,0,0,0,0,0]])
r=s.symbols('r')
B=s.expand(sum(b[i]*(1-r**l) for i,l in enumerate(L)))
Q=s.cancel(B/(r**3*(1-r)))
assert Q.is_polynomial(r)
Q=s.Poly(Q,r)
assert Q.eval(0)>0 and Q.eval(1)>0
assert Q.count_roots(0,1)==0
assert b[0]==0 and b[1]<0
print('PASS: full seven-column rank; baseline row identities')
print('PASS: B(r)=r^3(1-r)Q(r), deg Q=',Q.degree())
print('PASS: exact Sturm Q>0 on [0,1]')
print('baseline coefficient at exponent3:',b[1])
print('endpoint B/(1-r) at1:',Q.eval(1))
out={'Lambda':L,'b':[str(x) for x in b],'Q_low_to_high':[str(Q.nth(i)) for i in range(Q.degree()+1)]}
Path(__file__).with_name('baseline-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
