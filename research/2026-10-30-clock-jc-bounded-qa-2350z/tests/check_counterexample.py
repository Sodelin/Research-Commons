"""Exact rational arithmetic supporting the accompanying analytic hand argument.
Does not numerically approximate exponentials or claim a Lean proof.
"""
from fractions import Fraction as Q
import pathlib,hashlib,json,datetime
rate=kill=Q(8,3)
time_log2_coefficient=Q(3,16)
assert (rate+kill)*time_log2_coefficient==1
# Analytic premise justified in the note: exp(-log(2))=1/2.
e=Q(1,2);ratio=rate/(rate+kill)
w1=e+ratio*(1-e);w2=e*e+ratio*(1-e*e)
product=w1*w1;resolved=e*w1+ratio*(1-e)
assert (w1,w2,product,resolved,w2-product)==(Q(3,4),Q(5,8),Q(9,16),Q(5,8),Q(1,16))
p=pathlib.Path(__file__).resolve()
r={'status':'PASS_RATIONAL_ARITHMETIC_WITH_STATED_ANALYTIC_PREMISE','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'rate':str(rate),'jc_kill':str(kill),'t_over_log2':str(time_log2_coefficient),'W_t':str(w1),'W_2t':str(w2),'invalid_scalar_product':str(product),'correct_endpoint_resolved_sum':str(resolved),'difference':str(w2-product),'script_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'limits':'Analytic exponential expectation derived in companion hand note; this script checks rational substitutions only. No full scientific theorem or kernel verification.'}
(p.parent.parent/'evidence/COUNTEREXAMPLE-ARITHMETIC.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
