#!/usr/bin/env python3
"""Independent direct-factorial exact controls. Does not execute or build Rust."""
import hashlib, importlib.util, json, math, pathlib, sys
from fractions import Fraction as F

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path(__file__).resolve().parent
sys.dont_write_bytecode = True
source = ROOT/'reference/count_certificate.py'
expected = '4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4'
def require(p, message):
    if not p: raise RuntimeError(message)
require(hashlib.sha256(source.read_bytes()).hexdigest() == expected, 'reference hash')
spec=importlib.util.spec_from_file_location('reference', source)
ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)

# Evaluate t_i from a**i / i!, independent of the producer recurrence.
def direct(a, e, budget=None):
    for k in range(256 if budget is None else budget):
        s=sum((a**i/F(math.factorial(i)) for i in range(k+1)), F(0))
        t=a**(k+1)/F(math.factorial(k+1))
        d=2*t/(s+2*t)
        if k+2 >= 2*a and d <= e:
            return dict(status='CERTIFIED',law='normalized_prefix',a=str(a),epsilon=str(e),K=k,S=str(s),T=str(t),U=str(s+2*t),delta=str(d),inspected=k+1)
    require(budget is not None, 'independent bound exhausted; inconclusive')
    return dict(status='RESOURCE_LIMIT',law='normalized_prefix',a=str(a),epsilon=str(e),inspected=budget,next_K=budget)

inputs={(F(n,d),e) for n in range(0,25) for d in range(1,8) for e in [F(1,2), F(1,10),F(1,1000),F(9,10)]}
# Exact guard boundary (a=(K+2)/2), delta boundary, and rational sides.
for k in range(10):
    for a in [F(k+2,2), F(k+2,2)-F(1,101), F(k+2,2)+F(1,101)]:
        s=sum((a**i/F(math.factorial(i)) for i in range(k+1)), F(0))
        t=a**(k+1)/F(math.factorial(k+1))
        d=2*t/(s+2*t)
        for e in [d, d-F(1,10**20), d+F(1,10**20)]:
            if 0<e<1: inputs.add((a,e))

checks=weights_checks=tail_checks=0
for a,e in sorted(inputs):
    expected_answer=direct(a,e)
    k=expected_answer['K']
    for budget in dict.fromkeys([None,0,k,k+1,k+2]):
        want=expected_answer if budget is None or budget>k else direct(a,e,budget)
        got=ref.certify(a,e,max_steps=budget)
        require(got==want, f'reference output mismatch {(a,e,budget)}')
        checks+=1
    q=tuple(a**i/F(math.factorial(i))/F(expected_answer['S']) for i in range(k+1))
    require(ref.weights(a,k)==q, f'weights mismatch {(a,k)}')
    require(sum(q)==1 and all(w>=0 for w in q), 'weights not probability')
    # For any finite extension, the exact omitted fraction and TV distance
    # agree. This is a finite control, not a numerical evaluation of exp(a).
    terms=[a**i/F(math.factorial(i)) for i in range(k+21)]
    total=sum(terms,F(0));tail=sum(terms[k+1:],F(0));t=terms[k+1]
    require(tail<=2*t, 'finite geometric bound failure')
    omitted=tail/total
    require(omitted<=F(expected_answer['delta']), 'finite delta upper bound failure')
    p=[t/total for t in terms]
    distance=sum((abs(p[i]-(q[i] if i<len(q) else 0)) for i in range(len(p))),F(0))/2
    require(distance==omitted, 'finite normalized-prefix TV identity failure')
    tail_checks+=1;weights_checks+=1

# Resource limits must not certify even the trivial zero-rate case at budget 0.
require(ref.certify(F(0),F(1,2),max_steps=0)['status']=='RESOURCE_LIMIT','zero budget')
# Explicit Python bool quirks in *both* relevant APIs.
require(ref.weights(F(1),False)==(F(1),),'Python False cutoff behavior')
require(ref.weights(F(1),True)==(F(1,2),F(1,2)),'Python True cutoff behavior')
require(ref.certify(F(0),F(1,2),max_steps=False)['status']=='RESOURCE_LIMIT','Python False budget')
require(ref.certify(F(0),F(1,2),max_steps=True)['status']=='CERTIFIED','Python True budget')

snapshot={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'Cargo.toml',ROOT/'src/lib.rs',ROOT/'src/main.rs',ROOT/'src/parse.rs',source,ROOT/'scripts/check.py']}
report={'status':'PASS','reference_sha256':expected,'distinct_input_pairs':len(inputs),'direct_factorial_reference_comparisons':checks,'exact_weights_checks':weights_checks,'finite_extension_tail_and_tv_checks':tail_checks,'python_bool_domain_checks':4,'rust_execution':'NOT_PERFORMED_BY_REVIEWER','formal_verification':'NOT_CLAIMED','source_snapshot_sha256':snapshot}
(OUT/'independent-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2,sort_keys=True))
