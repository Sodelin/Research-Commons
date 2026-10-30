import sympy as s,json
from pathlib import Path
w,x,b=s.symbols('w x beta',positive=True)
ell=s.log(((1-b)*w+1+b)/2)
D=lambda f:s.diff(f,w)*w
ref_u=s.simplify(D(ell).subs({w:1/x,b:0}))
ref_b=s.simplify(s.diff(ell,b).subs({w:1/x,b:0}))
dust_u=s.simplify(D(ell).subs(w,1))
assert ref_u==1/(1+x)
assert ref_b==-(1-x)/(1+x)
assert dust_u==(1-b)/2
pair_rate=(1+b)/2
assert s.simplify(dust_u+pair_rate)==1
out={'status':'PASS','reference_pair_loss_u_derivative':str(ref_u),'reference_pair_loss_beta_derivative':str(ref_b),'dust_pair_loss_u_derivative':str(dust_u),'dust_full_generator_multiplier':str(pair_rate),'scope':'Exact clock derivatives and pair-routing probability, not a solved full-commutator jet.'}
Path(__file__).with_name('clock-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
