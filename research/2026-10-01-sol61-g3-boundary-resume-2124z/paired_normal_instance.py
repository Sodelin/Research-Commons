"""Exact algebraic signature predicate check without huge minimal polynomials."""
import json
import math
from pathlib import Path
import sympy as S

root=Path(__file__).parent
certificate=json.loads((root/'paired-normal-certificate.json').read_text())
la=[1,3,6,10,15,21]
E=[S.Rational(l+2)-S.Rational(1,2)**(l-1) for l in la]
N=certificate['algebraic_input']['N']
b=1-S.Rational(1,2)**N
Cstar=S.Rational(certificate['constants']['C_star'])
assert 0<Cstar<1 and 0<b<1 and all(x>0 for x in E) and b*b>1-Cstar/2
rows=[]
for name in ['F0','F1']:
    rec=certificate['normal_records'][name]
    c=[S.Rational(x) for x in rec['c']]
    den=S.ilcm(*(S.denom(x) for x in c))
    raw=[int(den*x) for x in c]
    common=math.gcd(*raw)
    row=[x//common for x in raw]+[0]*(len(la)-len(raw))
    assert sum(row[i]*E[i] for i in range(6))==0
    assert sum(row[i]*la[i] for i in range(6))==0
    rows.append({'normal':name,'primitive_integer_row':row,
                 'signed_monomial_exponent_identity':True})
assert E[0]==2 and E[1]==S.Rational(19,4) and E[1]!=3*E[0]
out={'status':'PASS exact algebraic predicate',
     'b':f'1-2^(-{N})','signature_rational_exponents':[str(x) for x in E],
     'primitive_integer_normal_rows':rows,
     'm2_formula':'b^2','rational_cutoff_formula':'1-C_star/2',
     'all_signature_coordinates_strictly_between_zero_and_one':True,
     'cutoff_comparison_verified':True,
     'nonbaseline_witness':{'lambda':3,'m3_exponent':str(E[1]),
           'm2_cubed_exponent':str(3*E[0])},
     'scope':'The finite algebraic predicate is verified symbolically. Global source NO, closure and ordinary interior use the separate hand proof. No huge minimal polynomial or field product expanded.'}
(root/'paired-normal-instance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','N':N,'signed_monomial_rows':rows,
                  'cutoff':True,'nonbaseline':True}))
