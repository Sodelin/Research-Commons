"""Exact fifth-arity negative control for the SAME certified three-cell witness.
Replays the exact source box verifier. Does not search for another source.
"""
from pathlib import Path
from fractions import Fraction as R
import importlib.util, json, math, hashlib
HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('source_certificate',HERE/'verify_three_cell_certificate.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
v=[z.v for z in m.v]
def b5(x,y):
 return (x**10+y**10+5*x**6+5*y**6+10*x**3*y+10*x*y**3)/32
body5=b5(v[0],v[1])*v[6]**10*b5(v[2],v[3])*v[7]**10*b5(v[4],v[5])
q=m.body(m.v)[0].v
difference=(body5-q**10)/(32*q)**10
lo,hi=R(-2,10**19),R(-1,10**19)
assert lo<difference.a<=difference.b<hi
receipt={'status':'PASS','scope':'only the same cap-four-return witness; first separating interface arity is five',
 'certificate_sha256':hashlib.sha256((HERE/'THREE-CELL-EXACT-CERTIFICATE.json').read_bytes()).hexdigest(),
 'source_verifier_sha256':hashlib.sha256((HERE/'verify_three_cell_certificate.py').read_bytes()).hexdigest(),
 'fifth_verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'strict_rational_lower_bound':str(lo),'strict_rational_upper_bound':str(hi),
 'exact_interval_is_between_bounds':True,
 'coordinate':'b5(padded source) - (1/32)^10',
 'display_interval':[float(difference.a),float(difference.b)],
 'arithmetic':'exact rational interval operations; display decimals are not acceptance tests'}
(HERE/'FIFTH-ARITY-VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
