import json,sympy as s
from pathlib import Path
root=Path(__file__).resolve().parent
x,b=s.symbols('x beta');j=json.load(open(root/'coefficients.json'))
P={f:{k:s.sympify(v['polynomial'],locals={'x':x,'beta':b}) for k,v in o.items()} for f,o in j.items()}
C={f:s.factor(P[f]['3'].subs(b,0)) for f in P}
for f in P:
 assert P[f]['0']==P[f]['1']==0
 assert s.factor(P[f]['2']+6*b*(1-b)*C[f])==0
expected={'f4':(3,s.Rational(275625,176)),'f5':(5,-s.Rational(21271359375,4))}
for f,(power,value) in expected.items():
 assert s.rem(s.Poly(C[f],x),s.Poly((1-x)**power,x))==0
 assert s.cancel(C[f]/(1-x)**power).subs(x,1)==value
ratio=-expected['f4'][1]/expected['f5'][1]
assert ratio==s.Rational(1,3395700)
A=s.Rational(826875,88);B=s.Rational(85085437500)*ratio
H=s.Matrix([[A,2*A],[2*A,B]])
assert B/A==s.Rational(8,3)
assert H.det()/A**2==-s.Rational(4,3)
v=s.Matrix([-2,1]);assert (v.T*H*v)[0]/A==-s.Rational(4,3)
out={'status':'PASS','identities':['[a^0]f_j=[a^1]f_j=0','[a^2]f_j=-6 beta(1-beta) [a^3]f_j(beta=0)'], 'fair_cubic_weak_limits':{f:{'epsilon_order':p,'coefficient':str(v)} for f,(p,v) in expected.items()},'forced_epsilon_squared_coefficient_ratio':str(ratio),'normalized_hessian':[[str(z/A) for z in row] for row in H.tolist()],'normalized_determinant':str(H.det()/A**2),'admissible_negative_direction':[-2,1],'normalized_direction_hessian':str((v.T*H*v)[0]/A),'limitations':'Coefficient algebra and limiting Hessian only; inherited source bank and reference contact identities; no full-word obstruction.'}
json.dump(out,open(root/'obstruction-check.json','w'),indent=2);print(json.dumps(out,indent=2))
