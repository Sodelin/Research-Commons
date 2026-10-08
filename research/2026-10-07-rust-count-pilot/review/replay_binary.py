#!/usr/bin/env python3
"""Read-only replay of a frozen Rust binary against independently computed exact results."""
import datetime, hashlib, json, math, os, pathlib, statistics, subprocess
from fractions import Fraction as F

ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path(__file__).resolve().parent
BINARY=ROOT/'target/release/count-certificate'
EXPECTED_BINARY='5f8afd1557623ebf889b2d2e6fdbcf84a8c5a75e55993e32600fb54ecad700d1'
EXPECTED_SOURCES={'src/lib.rs':'6f9ee623a64b356b7c28a09a91de3eff50425c67d3555ff43752023355e18ce0','src/main.rs':'f0be18f30dbbcf665ab61f079def331530f19a2c5a68b05d329078dbfd91c313','src/parse.rs':'e7e19824f70eff90ba638241bd0a3369fda755c40753ee6f856c88a40e293cf8','scripts/check.py':'63abbf8ff1951fe25d6c2d2fef8497f6d409c7c61901a17a72f88dbf23cf02c4','Cargo.lock':'6b82f1a74bedde4d31df8cc90c2dbd50b132feae8779df6c20ce898e77b46c25'}

def require(p,m):
    if not p: raise RuntimeError(m)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def check_snapshot():
    require(sha(BINARY)==EXPECTED_BINARY,'binary snapshot mismatch')
    for path,digest in EXPECTED_SOURCES.items(): require(sha(ROOT/path)==digest,'source snapshot mismatch '+path)
check_snapshot()
check=json.loads((ROOT/'evidence/check-report.json').read_text())
require(check['binary_sha256']==EXPECTED_BINARY,'receipt binary mismatch')
require(check['rust_build']==check['rust_tests']==check['differential']=='PASS','receipt lacks success')
require(check['cargo_lock_sha256']==EXPECTED_SOURCES['Cargo.lock'],'receipt lock mismatch')
for path,digest in check['source_sha256'].items(): require(EXPECTED_SOURCES[path]==digest,'receipt source mismatch')
require(sha(ROOT/'evidence/corpus.jsonl')==check['corpus_sha256'],'corpus hash mismatch')
require(sha(ROOT/'reference/count_certificate.py')==check['reference_sha256'],'reference hash mismatch')

def expected(a,e,budget,weights):
    for k in range(200 if budget is None else budget):
        ts=[a**i/F(math.factorial(i)) for i in range(k+2)]
        s=sum(ts[:-1],F(0));t=ts[-1];u=s+2*t;d=2*t/u
        if k+2>=2*a and d<=e:
            r=dict(K=k,S=str(s),T=str(t),U=str(u),a=str(a),delta=str(d),epsilon=str(e),inspected=k+1,law='normalized_prefix',status='CERTIFIED')
            if weights: r['weights']=[str(v/s) for v in ts[:-1]]
            return r
    require(budget is not None,'independent search bound inconclusive')
    return dict(a=str(a),epsilon=str(e),inspected=budget,law='normalized_prefix',next_K=budget,status='RESOURCE_LIMIT')

def call(args):
    return subprocess.run([os.fsencode(BINARY)]+[a if isinstance(a,bytes) else str(a).encode() for a in args],capture_output=True,timeout=10,cwd=OUT)

rows=[]
inputs=[(F(0),F(1,2)),(F(1),F(2,3)),(F(1),F(2,3)-F(1,10**30)),(F(1),F(1,2)),(F(2),F(9,10)),(F(41,7),F(1,10**5)),(F(2**160+1,2**160),F(1,100)),(F(1,2**160+1),F(1,2**180))]
for a,e in inputs:
    k=expected(a,e,None,False)['K']
    for budget in dict.fromkeys([0,k,k+1,None]):
        for weights in [False,True]:
            args=[str(a),str(e)]
            if budget is not None: args+=['--max-steps',str(budget)]
            if weights: args+=['--weights']
            r=call(args);want=expected(a,e,budget,weights)
            exact=(json.dumps(want,sort_keys=True)+'\n').encode()
            require(r.returncode==0 and r.stderr==b'' and r.stdout==exact,'replay mismatch '+str(args))
            rows.append({'argv':args,'status':want['status'],'stdout_sha256':hashlib.sha256(r.stdout).hexdigest()})
for a,e in [(' +.5E+0 ','0.5000'),('1E0000000000002','9e-1'),('0002/0004','+0.5'),('1.','6.666666666666666666666666667e-1')]:
    args=[a,e,'--max-steps=300','--weights'];r=call(args);want=expected(F(a),F(e),300,True)
    require(r.returncode==0 and not r.stderr and r.stdout==(json.dumps(want,sort_keys=True)+'\n').encode(),'parser replay mismatch')
    rows.append({'argv':args,'status':want['status'],'stdout_sha256':hashlib.sha256(r.stdout).hexdigest()})
invalid=[[b'\xff',b'1/2'],['-1','1/2','--max-steps','0'],['0','1','--max-steps','0'],['1','1/2','--max-steps','-0'],['1_0','1/2'],['1','1/2','--weights','--weights'],['1e4097','1/2'],['1' *4097,'1/2']]
invalid_rows=[]
for args in invalid:
    r=call(args)
    require(r.returncode==2 and not r.stdout and r.stderr,'invalid input contract mismatch')
    invalid_rows.append({'argv_repr':repr(args),'exit_code':r.returncode,'stderr':r.stderr.decode()})
# Huge natural budget is a typed transport case that terminates immediately at a=0.
r=call(['0','1/2','--max-steps','1'+'0'*100])
require(r.returncode==0 and not r.stderr and json.loads(r.stdout)==expected(F(0),F(1,2),None,False),'huge natural budget mismatch')
check_snapshot()
benchmark=json.loads((ROOT/'evidence/benchmark-report.json').read_text())
require(benchmark['binary_sha256']==EXPECTED_BINARY,'benchmark binary mismatch')
medians=[]
for w in benchmark['workloads']:
    item={'argv':w['argv']}
    for engine in ['python','rust']:
        samples=w['samples'][engine]
        require(len(samples)==benchmark['repetitions'],'benchmark count mismatch')
        median=statistics.median(s['wall_seconds'] for s in samples)
        require(median==w['summary'][engine]['wall_seconds']['median'],'benchmark median mismatch')
        item[engine+'_median_ms']=1000*median
    medians.append(item)
report={'status':'PASS','completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binary_sha256':EXPECTED_BINARY,'binary_bytes':BINARY.stat().st_size,'source_sha256':EXPECTED_SOURCES,'author_receipt_hashes_verified':True,'independent_exact_output_replays':len(rows),'invalid_transport_domain_replays':len(invalid_rows),'extra_huge_natural_budget_replays':1,'non_utf8_fix_independently_reproduced':True,'rust_build_by_reviewer':'NOT_PERFORMED','author_build_evidence':'10 unit tests and locked/offline release build logs inspected; receipt and binary identities matched','benchmark_medians_verified':medians,'benchmark_limit':'Full CLI including startup; no core-kernel speed or memory advantage established','valid_replays':rows,'invalid_replays':invalid_rows}
(OUT/'binary-replay-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['valid_replays','invalid_replays']},indent=2,sort_keys=True))
