import sympy as s,json
from pathlib import Path
p,a,q,beta=s.symbols('p a q beta')
d2=p*p*a+(1-p)**2*q+2*p*(1-p)
d3=p**3*a**3+(1-p)**3*q**3+3*p*p*(1-p)*a+3*p*(1-p)**2*q
r=d3/d2**3
first=s.factor(s.diff(r,p).subs(p,0))
coeff=s.expand((d3-d2**3).subs(q,1-beta*p)).coeff(p,3)
expected=(1-a)**2*(a+2)+3*beta**2-6*beta*(1-a)
b=(a+q-2)/q-2*(1-q)**2/q**2
clock=s.simplify(s.diff(s.log(d2),p,2).subs(p,0)/2-b)
assert s.simplify(first-3*(1/q-1)**2)==0
assert s.expand(coeff-expected)==0
assert clock==0
assert s.expand(expected.subs(beta,1-a)+(1-a)**3)==0
out={'ratio_first_derivative':str(first),'coupled_cubic':str(s.factor(coeff)),'clock_second_coefficient_identity':True,'coupled_negative_choice':True,'status':'exact scalar polynomial/rational controls; operator identities reviewed from current-root subset grammar, no forest bank execution'}
Path(__file__).with_name('CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
