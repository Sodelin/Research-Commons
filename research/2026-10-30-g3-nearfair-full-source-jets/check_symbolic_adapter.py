import sympy as s,json
from pathlib import Path
u,k,l=s.symbols('u k l');Q,A3,A4=s.symbols('Q A3 A4',commutative=False)
A2=(Q**2-Q)/4;A22=Q**2-A2-Q*A2+2*A3
b2=(1-(k*u+l*u**2))/2+(1+k*u+l*u**2)*s.exp(-u)/2
t=s.series(-s.log(b2),u,0,5).removeO()
B=[1,Q/2,A2/2+k*Q/2,A3/6+k*(Q*A2/2-A3)+l*Q/2,A4/24+k*(Q*A3/6-A4/3)+l*(Q*A2/2-A3)+k*k*A22/2]
E=s.expand(sum((-Q)**m*s.series(t**m,u,0,5).removeO()/s.factorial(m) for m in range(5)))
E=[E.coeff(u,i) for i in range(5)];R=[s.expand(sum(E[j]*B[i-j] for j in range(i+1))) for i in range(5)]
R3=(8*A3-Q**3+3*Q**2)/48
assert R[0]==1 and R[1]==R[2]==0
assert s.expand(R[3]-(1-6*k)*R3)==0
R4=A3/36-A4/72+Q/576+Q*A3/36+5*Q**2/384+Q**3/576-Q**4/384
assert s.expand(R[4].subs(k,s.Rational(1,6))-(R4-6*l*R3))==0
out={'status':'PASS','pair_time_through_order4':str(t),'fair_A2':str(A2),'beta_squared_coefficient_in_B_uu':str(A22),'cubic_identity':'normalized B=I+(1-6*k)*u^3*R3+O(u^4)','R3':str(R3),'critical_quartic_identity':'normalized B=I+u^4*(R4-6*l*R3)+O(u^5), beta=u/6+l*u^2','R4':str(R4),'scope':'Noncommutative polynomial algebra conditional on inherited complete-source routing/PDE identities; no source integration.'}
Path(__file__).with_name('symbolic-adapter-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
