"""Independent exact coefficients for the analytic same-cap return branch.
Uses truncated coefficient vectors, logarithms from P*(log P)'=P',
and chronological source multiplication rather than the author's log series.
"""
from pathlib import Path
import json, hashlib, math
import sympy as S
N=6
t,L=S.symbols('t L');ws=S.symbols('w1:4')
def coeff(expr):return [S.expand(expr).coeff(t,k) for k in range(N+1)]
def add(a,b):return [S.expand(x+y) for x,y in zip(a,b)]
def scale(a,c):return [S.expand(c*x) for x in a]
def mul(a,b):return [S.expand(sum(a[j]*b[i-j] for j in range(i+1))) for i in range(N+1)]
def log(a):
 assert a[0]==1
 out=[S.Integer(0)]
 for n in range(1,N+1):
  out.append(S.expand(a[n]-sum(k*out[k]*a[n-k] for k in range(1,n))/n))
 return out
zero=[S.Integer(0)]*(N+1)
def route(k,a,w):
 # Derive the symmetric polynomial directly from iid routing.
 m,h=S.symbols('m h')
 e=S.expand(sum(S.binomial(k,r)*(m-h)**(r*(r-1)//2)*(m+h)**((k-r)*(k-r-1)//2) for r in range(k+1))/2**k)
 out=0
 for (j,),c in S.Poly(e,h).terms():
  assert j%2==0
  out+=c.subs(m,1-a*t)*(w*t**3)**(j//2)
 return coeff(out)
def bare(a,w):
 a=S.Integer(a)
 # Independent expansion of C from the bare source identity.
 h=S.symbols('h')
 ce=S.expand(((a*t+h)**3+(a*t-h)**3)/24-h*h/2)
 ce=ce.subs(h*h,w*t**3)
 return [route(k,a,w) for k in (2,3,4)]+[coeff(ce),zero[:]]
def edge(z):return [coeff(z**p) for p in (1,3,6)]+[zero[:],zero[:]]
def compose(k,l):
 return [mul(k[j],l[j]) for j in range(3)]+[
 add(mul(l[0],k[3]),mul(k[2],l[3])),
 add(add(k[4],mul(add(coeff(1),scale(l[0],-1)),k[3])),mul(k[2],l[4]))]
bs=[bare(a,w) for a,w in zip((1,2,1),ws)]
body=bs[0]
for factor in (edge(1-L*t),bs[1],edge(1-L*t),bs[2]):body=compose(body,factor)
U=add(log(body[1]),scale(log(body[0]),-3))
V=add(add(log(body[2]),scale(log(body[1]),-4)),scale(log(body[0]),6))
raw=(body[3],body[4],V,U)
orders=(3,4,4,3)
for v,n in zip(raw,orders):
 assert all(S.expand(v[k])==0 for k in range(n))
F=S.Matrix([[v[orders[i]+j] for j in range(3)] for i,v in enumerate(raw[:3])])
G=[U[3+j] for j in range(3)]
F0=F[:,0];A=F0.jacobian(ws)
expected=S.Matrix([
 S.Rational(5,6)-sum(ws)/2,
 (2*L+S.Rational(3,2))*(S.Rational(1,12)-ws[0]/2)+(L+S.Rational(1,2))*(S.Rational(2,3)-ws[1]/2),
 S.Rational(27,8)-3*ws[0]/2-3*ws[1]-3*ws[2]/2])
assert all(S.expand(x)==0 for x in F0-expected)
assert S.cancel(A.det()+3*(4*L+3)/16)==0
w0=S.simplify(A.inv()*(-F0.subs(dict.fromkeys(ws,0))))
expectedw=S.Matrix([(26*L+15)/(12*(4*L+3)),S.Rational(7,12),(13*L+12)/(6*(4*L+3))])
assert all(S.cancel(x)==0 for x in w0-expectedw)
subs=dict(zip(ws,w0));at=lambda x:x.subs(subs)
assert all(S.diff(F0[i],v,u)==0 for i in range(3) for v in ws for u in ws)
assert all(S.diff(G[0],v,u)==0 for v in ws for u in ws)
v1=S.simplify(-A.inv()*at(F[:,1]))
v2=S.simplify(-A.inv()*(at(F[:,2])+at(F[:,1].jacobian(ws))*v1))
R0=S.cancel(at(G[0]))
R1=S.cancel(at(G[1])+(S.Matrix([G[0]]).jacobian(ws)*v1)[0])
R2=S.factor(at(G[2])+(at(S.Matrix([G[1]]).jacobian(ws))*v1)[0]+(S.Matrix([G[0]]).jacobian(ws)*v2)[0])
assert R0==R1==0
assert S.cancel(R2-3*(180*L**2+270*L-47)/64)==0
ell=(S.sqrt(2965)-45)/60
assert S.simplify(R2.subs(L,ell))==0 and 2965>45**2
assert S.cancel(S.diff(R2,L)-3*(360*L+270)/64)==0
result={'status':'PASS','method':'iid source routing; coefficient-vector chronological composition; logarithm derivative recurrence; symbolic IFT jets',
'vanishing_orders':list(orders),'det_DwF':str(S.factor(A.det())),
'w0':[str(S.factor(z)) for z in w0],'R0':str(R0),'R1':str(R1),'R2':str(R2),
'log_coefficient_convention':'ordinary Taylor coefficients, including factorial normalization',
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'scope':'exact finite symbolic identities supporting the separate two-IFT proof; no numerical small-time extrapolation or all-cap conclusion'}
Path(__file__).with_name('INDEPENDENT-UNIFORM-TIME-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

