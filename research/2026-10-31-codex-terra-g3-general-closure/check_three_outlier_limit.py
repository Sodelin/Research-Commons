#!/usr/bin/env python3
"""Exact-rational root and continuation diagnostic, not a Lean proof.

Reuses the SHA-pinned source polynomial limits, verifies three limiting
equations and certifies a common real root by a rational contraction bound.
The full finite-word/implicit-function argument is hand-derived separately.
"""
import base64
import hashlib
import io
import json
import tarfile
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

here=Path(__file__).resolve().parent
archive=here.parent/'2026-10-25-g3-fair-joint-rigidity'/'SOURCE-v2.tar.gz.base64'
raw=base64.b64decode(archive.read_bytes(),validate=False)
assert hashlib.sha256(raw).hexdigest()=='baafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6'
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as tf:
    cert=json.load(tf.extractfile('public-ready-fair-joint-v2/biased-joint-normal/JOINT-SCALED-CERTIFICATE.json'))['results']
z,y,A,X,Y,J,K,L=sp.symbols('z y A X Y J K L')
raw4=sp.sympify(cert['F4']['scaled_limit'],locals={'z':z,'y':y}).subs({z:1-X,y:Y})
raw5=sp.sympify(cert['F5']['scaled_limit'],locals={'z':z,'y':y}).subs({z:1-X,y:Y})
c4,c5=sp.Rational(275625,176),sp.Rational(4254271875,4)
f4=X**2*(X-1)*(2*X**3-24*X**2*Y-X**2+24*X*Y**2+6*X*Y-X+6*Y)
f5=X**2*(5*X**6-80*X**5*Y+140*X**4*Y**2-25*X**4-48*X**3*Y**3+300*X**3*Y+25*X**3-300*X**2*Y**2-250*X**2*Y+200*X*Y**2-5*X+30*Y)
assert sp.expand(raw4-c4*f4)==0 and sp.expand(raw5-c5*f5)==0
G=sp.Matrix([
    2*A**3+X**3-6*Y*X**2-2*A-X,
    2*f4.subs({X:A,Y:0})+f4,
    2*f5.subs({X:A,Y:0})+f5,
])
vars=(A,X,Y)
center=[F(98998234685932211,10**18),F(1215040573006347054,10**18),F(43203775357220560,10**18)]
radius=[F(1,10**7)]*3
as_sp=lambda a:sp.Rational(a.numerator,a.denominator)
subs=dict(zip(vars,map(as_sp,center)))
Jac=G.jacobian(vars)
inv=Jac.subs(subs).inv()
f0=G.subs(subs)
step=inv*f0
box=[(c-r,c+r) for c,r in zip(center,radius)]

def add(a,b): return a[0]+b[0],a[1]+b[1]
def mul(a,b):
    q=[u*v for u in a for v in b]
    return min(q),max(q)
def poly_iv(expr):
    acc=(F(0),F(0))
    for powers,coeff in sp.Poly(sp.expand(expr),*vars).terms():
        c=F(int(sp.numer(coeff)),int(sp.denom(coeff)))
        v=(c,c)
        for iv,p in zip(box,powers):
            for _ in range(p):v=mul(v,iv)
        acc=add(acc,v)
    return acc
def abs_upper(iv):return max(abs(iv[0]),abs(iv[1]))

T=sp.eye(3)-inv*Jac
rows=[]
for i in range(3):
    residual=abs(F(int(sp.numer(step[i])),int(sp.denom(step[i]))))
    variation=sum(abs_upper(poly_iv(T[i,j]))*radius[j] for j in range(3))
    bound=residual+variation
    assert bound<radius[i],(i,float(bound),float(radius[i]))
    rows.append(float(bound/radius[i]))
print('PASS exact SHA and both inherited scaled-polynomial identities')
print('PASS rational contraction on the three-variable box; relative bounds',rows)
print('PASS A in',float(box[0][0]),float(box[0][1]),'X in',float(box[1][0]),float(box[1][1]),'Y in',float(box[2][0]),float(box[2][1]))

# For bias in the middle, J, K and L are the first three gap exponents.
# The fifth-order cap4 residual is (3/16)*(D0+Dk*K).
D0=(18*A**4-8*A**3*J-4*A**3*K-4*A**3*L+10*A**3*X+6*A**3-12*A**2
    +10*A*X**3-60*A*X**2*Y-12*A*X-4*A-4*J*X**3+24*J*X**2*Y
    -4*K*X**3+24*K*X**2*Y+4*X**4-24*X**3*Y+3*X**3-18*X**2*Y-3*X**2-2*X)
Dk=sp.diff(D0,K)
D0=sp.expand(D0.subs({J:sp.Rational(1,2),K:0,L:sp.Rational(1,10)}))
iv0=poly_iv(D0)
ivden=poly_iv(-Dk)
assert iv0[0]>0 and ivden[0]>0
kiv=(iv0[0]/ivden[1],iv0[1]/ivden[0])
assert F(15,100)<kiv[0]<=kiv[1]<F(16,100)
phase=(2*box[0][0]+box[1][0],2*box[0][1]+box[1][1])
assert F(14,10)<phase[0]<phase[1]<F(15,10)
assert phase[0] > F(1,2)+F(1,10)+kiv[1]
print('PASS exact interval K=D0/(-Dk):',float(kiv[0]),float(kiv[1]))
print('PASS phase 2A+X lies in',float(phase[0]),float(phase[1]),'and leaves positive tail')
