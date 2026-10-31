"""Exact displayed-polynomial checks only; no forest engine or parameter search."""
import sympy as S
import json
d,z,y,x=S.symbols('d z y x')
eta=(3*(z-d)**2-d**3)/2
K=d**3/6-d**4/6+d**5/15-d**6/90
delta=K+z**3/3-d*z**2/2-z*eta/3
A=d**4*(1-2*d/5+d**2/15)
I=-A-8*z*eta-96*delta
P=6*y**3+12*y**2+2*d*y-3*d+2*d**2-d**3/3
assert S.simplify(-(I+60*delta).subs(z,d*(1+y))/d**3-P)==0
assert S.expand(P.subs({d:3*x*x,y:-x})-3*x*x*(1-x)*(3*x**3+3*x*x-3*x+1))==0
assert S.expand(P.subs({d:3*x*x,y:x})-P.subs({d:3*x*x,y:-x})-24*x**3)==0
assert S.simplify((I+60*delta).subs({d:S.Rational(1,2),z:S.Rational(13,20)}))==-S.Rational(1501,24000)
rows=[]
sums=[0,0,0]
for t,n in [(S.Rational(-7,32),427),(S.Rational(-15,256),9216),(S.Rational(-1,32),437)]:
 sub={d:S.Rational(1,4),z:t+S.Rational(1,4)}
 vals=[S.factor(f.subs(sub)) for f in (eta,delta,I)]
 sums=[a+n*b for a,b in zip(sums,vals)]
 rows.append({'t':str(t),'count':n,'r':str(vals[0]),'q':str(vals[2]+60*vals[1])})
assert sums==[0,0,0]
print(json.dumps({'status':'PASS','method':'exact rational polynomial identities only','actual_three_node_rows':rows,'sums_r_k_i':list(map(str,sums))},indent=2))
