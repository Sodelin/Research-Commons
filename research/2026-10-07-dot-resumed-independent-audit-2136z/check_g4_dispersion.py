"""Independent exact dispersion identity, using the frozen fifth arrays."""
import contextlib
import io
import json
import pathlib
import runpy
from fractions import Fraction as F

with contextlib.redirect_stdout(io.StringIO()):
    e = runpy.run_path(str(pathlib.Path(__file__).with_name('check_g4_common_scale.py')))

def add(*ps):
    out = {}
    for p in ps:
        for k,v in p.items(): out[k] = out.get(k,F(0)) + v
    return {k:v for k,v in out.items() if v}

def mul(p,q):
    out = {}
    for (i,j),a in p.items():
        for (k,l),b in q.items():
            key=(i+k,j+l)
            out[key]=out.get(key,F(0))+a*b
    return {k:v for k,v in out.items() if v}

alpha={(4,0):F(-5,6),(3,0):F(5,2),(2,0):F(-5,6)}
beta={(1,0):F(15,2),(2,0):F(15),(3,0):F(-5,2)}
gamma={(3,0):F(-5,48),(2,0):F(5,8),(1,0):F(-5,16)}
eta={(0,2):F(3,2),(3,0):F(-1,2)}
delta={(0,3):F(-1,6),(3,1):F(1,6),(5,0):F(1,15),(6,0):F(-1,90)}
I={(0,3):F(4),(1,2):F(-12),(3,1):F(-12),(4,0):F(3),(5,0):F(-6),(6,0):F(1)}
C={(i+5,0):v/F(144) for i,v in e['P'].items()}
identity=add(C,{(0,4):F(5,24)},mul(alpha,eta),mul(beta,delta),mul(gamma,I))
assert identity == e['dt']
assert F(2,48)==F(1,24) and F(2)*F(5,24)==F(5,12)
print(json.dumps({
 'status':'PASS bounded exact dispersion identity',
 'input_sha256':e['expected_hash'],
 'full_bivariate_identity_checked':True,
 'positive_remainder':'d^5 P(d)/144 + 5 t^4/24',
 'twice_remainder_lower_bound':'d^5/24 + 5 t^4/12',
 'scientific_source_rerun':False,
 'parameter_search':False,
 'scope':'Exact identity and constants; hand review supplies actual-source applicability and necessary-only interpretation.'
},indent=2))
