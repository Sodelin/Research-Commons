import sympy as s,json
from pathlib import Path
b=s.symbols('beta');Q,A3=s.symbols('Q A3',commutative=False)
A20=(Q**2-Q)/4;A21=Q*A20-2*A3;A22=Q**2-A20-A21
A2=A20+b*A21+b*b*A22
rate=(1+b)/2
normalized_second=s.expand(A2/2-rate**2*Q**2/2+(1-b*b)*Q/8)
R3=(8*A3-Q**3+3*Q**2)/48
assert s.expand(normalized_second+6*b*(1-b)*R3)==0
out={'status':'PASS','complete_normalized_second_coefficient':'-6*beta*(1-beta)*R3','R3':'(8*A3-Q^3+3*Q^2)/48','premises':['complete pair-routing first rate (1+beta)Q/2','complete fair-bias PDE','second source derivative polynomial in beta of degree <=2','deterministic beta=1 source is ordinary'],'scope':'Noncommutative exact algebra supporting full-matrix analytic endpoint factor; no real spectral sign assumption.'}
Path(__file__).with_name('full-factor-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
