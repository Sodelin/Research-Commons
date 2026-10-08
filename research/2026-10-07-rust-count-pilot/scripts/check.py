#!/usr/bin/env python3
"""Bounded reference and candidate check runner. Never installs software.

A missing candidate is reported UNEXECUTED, never PASS. Writes evidence only
under this package. Use --reference-only before a Rust toolchain is available.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / 'reference/count_certificate.py'
EXPECTED_SHA256 = '4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4'
EXPECTED_BLOB = '85935eb2c7b07c111b5a5bb54004e7f101b4dc1a'


def load_reference():
    source = REFERENCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == EXPECTED_SHA256, 'Reference SHA-256 mismatch'
    assert hashlib.sha1(b'blob '+str(len(source)).encode()+b'\0'+source).hexdigest() == EXPECTED_BLOB
    spec = importlib.util.spec_from_file_location('frozen_count_reference', REFERENCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def independent_check(result, a, epsilon, budget, include_weights):
    """Direct factorial formula; no call to either producer recurrence."""
    assert result['a'] == str(a) and result['epsilon'] == str(epsilon)
    assert result['law'] == 'normalized_prefix'
    assert type(result['inspected']) is int
    if result['status'] == 'RESOURCE_LIMIT':
        assert budget is not None and result['inspected'] == budget and result['next_K'] == budget
        assert set(result) == {'status','law','a','epsilon','inspected','next_K'}
        inspected = budget
    else:
        assert result['status'] == 'CERTIFIED'
        k = result['K']
        assert type(k) is int and k >= 0 and result['inspected'] == k + 1
        assert budget is None or k + 1 <= budget
        terms = [a ** i / math.factorial(i) for i in range(k+2)]
        s, t = sum(terms[:-1]), terms[-1]
        u = s + 2*t
        d = 2*t/u
        assert (result['S'],result['T'],result['U'],result['delta']) == tuple(map(str,(s,t,u,d)))
        assert k + 2 >= 2*a and d <= epsilon
        expected_keys = {'status','law','a','epsilon','K','S','T','U','delta','inspected'}
        if include_weights:
            w = [Fraction(x) for x in result['weights']]
            assert w == [x/s for x in terms[:-1]] and sum(w) == 1
            assert all(x >= 0 for x in w)
            expected_keys.add('weights')
        assert set(result) == expected_keys
        inspected = k
    # Both a success and a limit must preserve first-cutoff semantics.
    for j in range(inspected):
        s = sum(a**i / math.factorial(i) for i in range(j+1))
        t = a**(j+1) / math.factorial(j+1)
        assert not (j+2 >= 2*a and 2*t/(s+2*t) <= epsilon)


def build_corpus(ref):
    inputs = [(Fraction(0),Fraction(1,2)), (Fraction(1),Fraction(2,3)),
              (Fraction(1),Fraction(1,2)), (Fraction(2),Fraction(9,10)),
              (Fraction(1,1000),Fraction(1,10**30)),
              (Fraction(10),Fraction(1,10**20)),
              (Fraction(25),Fraction(999,1000)),
              (Fraction(2**160+1,2**160),Fraction(1,100)),
              (Fraction(1,2**160+1),Fraction(1,2**180)),
              (Fraction(3,2),Fraction(1,2**80))]
    rng = random.Random(20261007)
    for _ in range(80):
        inputs.append((Fraction(rng.randrange(0,61),rng.randrange(1,13)),
                       Fraction(rng.randrange(1,1000),1001)))
    # Generate exact delta equality and immediate sides without using ref.
    for a in [Fraction(1,2),Fraction(1),Fraction(2),Fraction(7,3)]:
        for k in range(8):
            if k+2 < 2*a: continue
            s = sum(a**i / math.factorial(i) for i in range(k+1))
            t = a**(k+1) / math.factorial(k+1)
            delta = 2*t/(s+2*t)
            inputs.extend((a,e) for e in (delta,delta-Fraction(1,10**12),delta+Fraction(1,10**12)) if 0<e<1)
    cases=[]
    for a,e in inputs:
        answer=ref.certify(a,e)
        k=answer['K']
        for budget in dict.fromkeys([None,0,k,k+1,k+2]):
            for with_weights in [False,True]:
                result=ref.certify(a,e,max_steps=budget)
                if with_weights and result['status']=='CERTIFIED':
                    result['weights']=list(map(str,ref.weights(a,result['K'])))
                independent_check(result,a,e,budget,with_weights)
                cases.append({'a':str(a),'epsilon':str(e),'max_steps':budget,
                              'weights':with_weights,'expected':result})
    # Common accepted CLI grammar, always interpreted exactly.
    for a,e in [('0.0','5e-1'),('+1.25E+0','0.001'),('.125','1e-20'),('1.','0.999'),
                ('0002/0004','+0.5'),(' 1/2 ',' 1e-3 '),('1e0000000000002','0.9')]:
        aa,ee=Fraction(a),Fraction(e)
        result=ref.certify(aa,ee,max_steps=300)
        independent_check(result,aa,ee,300,False)
        cases.append({'a':a,'epsilon':e,'max_steps':300,'weights':False,'expected':result})
    return cases


def reference_invalid_checks(ref):
    checks=0
    for a,e in [(-1,Fraction(1,2)),(Fraction(-1),Fraction(1,2)),(Fraction(0),Fraction(0)),
                (Fraction(0),Fraction(1)),(Fraction(0),Fraction(2)),(Fraction(0),0.5),
                (True,Fraction(1,2))]:
        try: ref.certify(a,e)
        except (TypeError,ValueError): checks+=1
        else: raise AssertionError('reference accepted invalid exact input')
    for budget in [-1,0.5,'1']:
        try: ref.certify(Fraction(0),Fraction(1,2),max_steps=budget)
        except ValueError: checks+=1
        else: raise AssertionError('reference accepted invalid budget')
    # Python bool-as-int is real reference behavior, intentionally absent from Rust's typed API.
    assert ref.certify(Fraction(0),Fraction(1,2),max_steps=False)['status']=='RESOURCE_LIMIT'
    assert ref.certify(Fraction(0),Fraction(1,2),max_steps=True)['status']=='CERTIFIED'
    checks+=2
    for a,k in [(Fraction(-1),0),(Fraction(0),-1),(1,0),(Fraction(0),0.5)]:
        try: ref.weights(a,k)
        except ValueError: checks+=1
        else: raise AssertionError('reference accepted invalid weight input')
    return checks


def mutation_checks(cases):
    """Show that checker rejects changed exact results, not just valid fixtures."""
    success=next(c for c in cases if c['a']=='1' and c['epsilon']=='1/2' and c['max_steps'] is None and c['weights'])
    mutations=[]
    for key in ['S','T','U','delta']:
        bad=dict(success['expected']); bad[key]=str(Fraction(bad[key])+1); mutations.append(bad)
    for key in ['K','inspected']:
        bad=dict(success['expected']); bad[key]+=1; mutations.append(bad)
    bad=dict(success['expected']);bad['weights']=['1','0'];mutations.append(bad)
    bad=dict(success['expected']);bad['law']='residual_lumped';mutations.append(bad)
    for result in mutations:
        try: independent_check(result,Fraction(success['a']),Fraction(success['epsilon']),None,True)
        except (AssertionError,KeyError): pass
        else: raise AssertionError('checker accepted mutation')
    return len(mutations)


def command(args, timeout=60):
    return subprocess.run(args,cwd=ROOT,text=True,encoding='utf-8',capture_output=True,
                          timeout=timeout,check=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference-only',action='store_true')
    parser.add_argument('--build',action='store_true',help='Run cargo test/build offline and locked; installs nothing')
    parser.add_argument('--binary',type=Path)
    args=parser.parse_args()
    report={'started_utc':datetime.now(timezone.utc).isoformat(), 'python':sys.version,
            'reference_sha256':EXPECTED_SHA256,
            'rust_build':'UNEXECUTED','rust_tests':'UNEXECUTED','differential':'UNEXECUTED',
            'formal_verification':'NOT_CLAIMED','performance':'UNMEASURED'}
    evidence=ROOT/'evidence';evidence.mkdir(exist_ok=True)
    try:
        ref=load_reference()
        cases=build_corpus(ref)
        checks=reference_invalid_checks(ref)
        mutations=mutation_checks(cases)
        corpus_bytes=('\n'.join(json.dumps(c,sort_keys=True) for c in cases)+'\n').encode()
        (evidence/'corpus.jsonl').write_bytes(corpus_bytes)
        report.update(reference_checks='PASS',corpus_cases=len(cases),
                      reference_invalid_checks=checks,checker_mutations=mutations,
                      corpus_sha256=hashlib.sha256(corpus_bytes).hexdigest())
        if args.reference_only:
            report['blocker']='Rust candidate not executed in reference-only mode.'
        else:
            binary=args.binary.resolve() if args.binary else ROOT/'target/release/count-certificate'
            if args.build:
                if not shutil.which('cargo'): raise RuntimeError('cargo is unavailable; Rust checks UNEXECUTED')
                for name,cmd in [('rust_tests',['cargo','test','--offline','--locked','--all-targets']),
                                 ('rust_build',['cargo','build','--offline','--locked','--release'])]:
                    output=command(cmd,timeout=180)
                    (evidence/(name+'.log')).write_text(output.stdout+output.stderr)
                    report[name]='PASS' if output.returncode==0 else 'FAIL'
                    if output.returncode: raise RuntimeError(name+' failed; see log')
                report['rustc']=command(['rustc','--version','--verbose']).stdout.strip()
                report['cargo']=command(['cargo','--version']).stdout.strip()
                report['cargo_lock_sha256']=hashlib.sha256((ROOT/'Cargo.lock').read_bytes()).hexdigest()
                report['build_flags']=['--offline','--locked','--release']
                report['rustflags']=os.environ.get('RUSTFLAGS','')
                report['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'src').glob('*.rs'))}
            if not binary.is_file(): raise RuntimeError('candidate binary missing; differential checks UNEXECUTED')
            report['binary_sha256']=hashlib.sha256(binary.read_bytes()).hexdigest()
            report['binary_path']=str(binary.relative_to(ROOT)) if binary.is_relative_to(ROOT) else str(binary)
            report['differential']='RUNNING'
            started=time.monotonic()
            for c in cases:
                cli=[str(binary),c['a'],c['epsilon']]
                if c['max_steps'] is not None: cli += ['--max-steps',str(c['max_steps'])]
                if c['weights']: cli += ['--weights']
                output=command(cli,timeout=15)
                assert output.returncode==0,(c,output.returncode,output.stderr)
                assert output.stderr=='',(c,output.stderr)
                assert json.loads(output.stdout)==c['expected'],(c,output.stdout)
                assert output.stdout==json.dumps(c['expected'],sort_keys=True)+'\n',(c,output.stdout)
                independent_check(json.loads(output.stdout),Fraction(c['a']),Fraction(c['epsilon']),c['max_steps'],c['weights'])
            invalid=[[],['1'],['1','1/2','extra'],['-1','1/2'],['0','0'],['0','1'],['0','2'],
                     ['nan','1/2'],['1/0','1/2'],['--unknown'],['1','1/2','--max-steps'],
                     ['1','1/2','--max-steps','-1'],['1','1/2','--max-steps','1.0'],
                     ['1','1/2','--weights','--weights'],['1','1/2','--max-steps=1','--max-steps=2'],
                     ['1e4097','1/2'],['1e-4097','1/2'],['1_000','1/2'],['١','1/2'],
                     ['1'*4097,'1/2'],['1 / 2','1/2'],['1','1/2','--max-steps','-0']]
            for cli in invalid:
                output=command([str(binary)]+cli,timeout=5)
                assert output.returncode==2 and not output.stdout and output.stderr,(cli,output)
            output=command([os.fsencode(binary),b'\xff',b'1/2'],timeout=5)
            assert output.returncode==2 and not output.stdout and output.stderr
            for a in ['1e4096','1e-4096','1'*4096]:
                output=command([str(binary),a,'1/2','--max-steps','0'],timeout=5)
                assert output.returncode==0 and json.loads(output.stdout)['status']=='RESOURCE_LIMIT'
            output=command([str(binary),'0','1/2','--max-steps','1'+'0'*100],timeout=5)
            assert output.returncode==0 and json.loads(output.stdout)['K']==0
            report.update(differential='PASS',candidate_invalid_checks=len(invalid),
                          candidate_extra_boundary_checks=5,
                          differential_elapsed_seconds=time.monotonic()-started)
    except Exception as error:
        if report['differential']=='RUNNING': report['differential']='FAIL'
        report['failure']=f'{type(error).__name__}: {error}'
        report['finished_utc']=datetime.now(timezone.utc).isoformat()
        (evidence/'check-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
        print(json.dumps(report,indent=2,sort_keys=True))
        return 1
    report['finished_utc']=datetime.now(timezone.utc).isoformat()
    (evidence/'check-report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))
    return 0

if __name__=='__main__':
    sys.dont_write_bytecode=True
    raise SystemExit(main())
