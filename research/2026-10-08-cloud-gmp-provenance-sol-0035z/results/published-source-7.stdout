#!/usr/bin/env python3
"""Finite exact differential checks from one authenticated source byte buffer."""
import argparse
from collections import Counter
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import random
import resource
import signal
import subprocess
import sys
import time
import types

ORACLE_SHA = 'c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'
SEED = 202610072354


def child_limits():
    resource.setrlimit(resource.RLIMIT_CPU, (45, 45))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024**2, 16 * 1024**2))


def typed(token):
    kind, value = token.split(':', 1)
    if kind == 'i': return int(value)
    if kind == 'q': return F(value)
    if kind == 'b': return value == 'true'
    if kind == 'f': return float(value)  # Refusal type fixture, never certification arithmetic.
    if kind == 's': return value
    raise ValueError('unknown fixture tag')


def oracle_record(module, command):
    t = command.split()
    op = t[0]
    try:
        if op == 'exp': result = module.exp_neg(typed(t[1]), typed(t[2]))
        elif op == 'point': result = module.Interval.point(F(t[1]))
        else:
            a = module.Interval(F(t[1]), F(t[2]))
            if op in ('add', 'sub', 'mul', 'intersects'):
                b = module.Interval(F(t[3]), F(t[4]))
                result = {'add': lambda: a+b, 'sub': lambda: a-b,
                          'mul': lambda: a*b, 'intersects': lambda: a.intersects(b)}[op]()
            elif op == 'neg': result = -a
            elif op == 'width': result = a.width
            elif op == 'unit': result = a.unit_intersection()
            elif op == 'dyadic': result = a.dyadic(int(t[3]))
            else:
                scalar = F(t[3])
                result = {'div': lambda: a/scalar, 'contains': lambda: a.contains(scalar),
                          'add_scalar': lambda: a+scalar, 'radd': lambda: scalar+a,
                          'sub_scalar': lambda: a-scalar, 'rsub': lambda: scalar-a,
                          'mul_scalar': lambda: a*scalar, 'rmul': lambda: scalar*a}[op]()
        if isinstance(result, module.Interval):
            return {'status': 'ok', 'kind': 'interval', **result.record()}
        if isinstance(result, bool): return {'status': 'ok', 'kind': 'boolean', 'value': result}
        return {'status': 'ok', 'kind': 'rational', 'value': str(result)}
    except Exception as error:
        return {'status': type(error).__name__, 'message': str(error), 'phase': 'primitive'}


def fixtures():
    rng = random.Random(SEED)
    cases = []
    def add(command, category): cases.append({'command': command, 'category': category})
    # Independently chosen sign quadrants, point/touching/disjoint boundaries.
    intervals = [(F(-2), F(-1)), (F(-1), F(2)), (F(0), F(0)),
                 (F(1, 3), F(2, 3)), (F(1), F(1)), (F(2), F(3))]
    for _ in range(100):
        intervals.append(tuple(sorted((F(rng.randint(-100, 100), rng.randint(1, 37)),
                                       F(rng.randint(-100, 100), rng.randint(1, 37))))))
    huge = 1 << 4097
    intervals.extend([(F(-huge, 3), F(huge, 7)),
                      (F(-1, huge+3), F(1, huge+3))])
    for i, (lo, hi) in enumerate(intervals):
        a = f'{lo} {hi}'
        b = intervals[(i*17+3) % len(intervals)]
        for op in ('add', 'sub', 'mul', 'intersects'):
            add(f'{op} {a} {b[0]} {b[1]}', 'interval-sign-products')
        for op in ('neg', 'width', 'unit'): add(f'{op} {a}', 'interval-basic-unit')
        scalar = F(rng.randint(-17, 17), rng.randint(1, 19))
        for op in ('div', 'contains', 'add_scalar', 'radd', 'sub_scalar', 'rsub', 'mul_scalar', 'rmul'):
            add(f'{op} {a} {scalar}', 'interval-scalar')
        add(f'contains {a} {lo}', 'closed-endpoints')
        add(f'contains {a} {hi}', 'closed-endpoints')
        add(f'dyadic {a} {rng.choice([0,1,2,8,64,192,257,4097])}', 'signed-dyadic')
    for a in intervals[:6]:
        for b in intervals[:6]:
            add(f'mul {a[0]} {a[1]} {b[0]} {b[1]}', 'all-sign-quadrants')
            add(f'intersects {a[0]} {a[1]} {b[0]} {b[1]}', 'closed-intersection')
    for command in ('point -0', 'point 0006/3', 'point -12/6', 'dyadic -1/3 -1/3 0',
                    'dyadic -2/3 1/3 1', 'dyadic -1 1 -1', 'div -1 1 0',
                    'div 2 1 0', 'unit -2 -1', 'unit 2 3', 'point 7/21'):
        add(command, 'interval-refusal-and-canonical')
    epsilon = F(1, 8192)
    for bits in (8,9,16,32,64,128,191,192):
        xs = [F(0), F(1,1000003), F(1,2), F(1)-epsilon, F(1), F(1)+epsilon,
              F(2)-epsilon, F(2), F(2)+epsilon, F(4)-epsilon, F(4), F(4)+epsilon,
              F(8)-epsilon, F(8), F(bits)-epsilon, F(bits), F(bits)+epsilon]
        for x in xs: add(f'exp q:{x} i:{bits}', 'exp-halving-shortcut-boundaries')
        add(f'exp i:0 i:{bits}', 'exp-integer-zero')
    for _ in range(180):
        bits = rng.choice([8,16,32,64,128,192])
        x = F(rng.randint(0, (bits+3)*37), rng.randint(1, 37))
        add(f'exp q:{x} i:{bits}', 'exp-rational-sample')
    for bits in (8,64,192):
        add(f'exp i:{huge} i:{bits}', 'no-256-2048-input-cap')
        add(f'exp q:1/{huge+3} i:{bits}', 'no-256-2048-input-cap')
    add(f'exp q:{(1<<257)-1}/{1<<258} i:192', 'no-256-input-cap-series')
    add(f'exp q:{huge-1}/{huge} i:8', 'no-2048-input-cap-series')
    bad_bits = ['i:-1','i:0','i:7','i:193',f'i:{1<<3000}',
                'q:64','b:true','b:false','f:64.0','s:64']
    for x in ('i:0','q:-1/3','i:1000'):
        for bits in bad_bits: add(f'exp {x} {bits}', 'exp-refusal-before-shortcut')
    for x in ('b:true','b:false','f:0.0','f:nan','s:0','s:1/2'):
        for bits in ('i:64','i:7','b:true'):
            add(f'exp {x} {bits}', 'exp-x-type-refusal-first')
    # Explicit transport contract, separate from source primitive comparison.
    parser_cases = [
        ('point 1/0', 'DomainError', 'integer or rational n/d string required'),
        ('point +1', 'DomainError', 'integer or rational n/d string required'),
        ('dyadic 0 1 65537', 'ResourceBound', 'probe dyadic shift exceeds65536'),
        ('point '+('0'*8193), 'ResourceBound', 'probe numeric text exceeds8192 characters'),
        ('point '+('0'*65536), 'ResourceBound', 'probe line exceeds65536 bytes'),
        ('point 1 extra', 'DomainError', 'probe argument count'),
    ]
    for command, status, message in parser_cases:
        cases.append({'command': command, 'category': 'separate-parser-contract',
                      'parser_expected': {'status': status,'message': message,'phase': 'parser'}})
    add('point 1', 'stream-recovery-after-parser-refusals')
    return cases


def properties(command, record):
    if record['status'] != 'ok' or record['kind'] != 'interval': return 0
    lo, hi, width = F(record['lower']), F(record['upper']), F(record['width'])
    assert lo <= hi and width == hi-lo
    checks = 2
    t = command.split(); op = t[0]
    if op == 'mul':
        a, b, c, d = map(F, t[1:]); products = [a*c,a*d,b*c,b*d]
        assert lo == min(products) and hi == max(products); checks += 2
    if op == 'div':
        a,b,scalar = map(F,t[1:]); endpoints=[a/scalar,b/scalar]
        assert lo == min(endpoints) and hi == max(endpoints); checks += 2
    if op == 'dyadic':
        a,b = map(F,t[1:3]); bits=int(t[3]); scale=1<<bits
        assert lo <= a <= b <= hi
        assert (lo*scale).denominator == (hi*scale).denominator == 1
        assert width <= b-a+F(2,scale); checks += 3
    if op == 'exp':
        x,bits = typed(t[1]),typed(t[2]); bound=F(1,1<<bits)
        assert 0 <= lo <= hi <= 1 and width <= bound; checks += 2
        if x == 0: assert lo == hi == 1; checks += 1
        if x >= bits: assert lo == 0 and hi == bound; checks += 2
    return checks


def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--probe',required=True)
    parser.add_argument('--output',required=True); args=parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CPU,(90,90))
    resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
    signal.alarm(120)
    packet=Path(__file__).resolve().parents[1]; output=Path(args.output); output.mkdir(parents=True,exist_ok=True)
    buffer=(packet/'reference/certified_forward.py').read_bytes()
    assert len(buffer)==6604 and hashlib.sha256(buffer).hexdigest()==ORACLE_SHA
    module=types.ModuleType('pinned_forward_c8487100'); sys.modules[module.__name__]=module
    exec(compile(buffer,'sha256:'+ORACLE_SHA,'exec'),module.__dict__)
    start=time.monotonic(); cases=fixtures()
    input_bytes=('\n'.join(c['command'] for c in cases)+'\n').encode()
    (output/'differential-inputs.txt').write_bytes(input_bytes)
    expected=[c.get('parser_expected') or oracle_record(module,c['command']) for c in cases]
    child=subprocess.run([args.probe],input=input_bytes,capture_output=True,
                         preexec_fn=child_limits,timeout=60)
    (output/'probe-output.jsonl').write_bytes(child.stdout)
    records=[json.loads(line) for line in child.stdout.splitlines()]
    failures=[]; checks=0
    if child.returncode != 0 or len(records)!=len(cases):
        failures.append({'process_returncode':child.returncode,'records':len(records),'expected_records':len(cases),'stderr':child.stderr.decode()})
    for i,(case,want,got) in enumerate(zip(cases,expected,records)):
        if got!=want: failures.append({'index':i,'command':case['command'],'expected':want,'actual':got})
        else:
            try: checks+=properties(case['command'],got)
            except AssertionError: failures.append({'index':i,'command':case['command'],'property_failure':True})
    report={'status':'PASS' if not failures else 'FAIL','oracle_sha256':ORACLE_SHA,'oracle_bytes':len(buffer),
            'oracle_execution':'one hash-verified byte buffer compiled in memory; primitive methods only, no parameter parser',
            'seed':SEED,'case_count':len(cases),'categories':dict(Counter(c['category'] for c in cases)),
            'exact_status_counts':dict(Counter(r['status'] for r in records)),
            'exact_property_assertions':checks,'cpp_returncode':child.returncode,
            'primitive_comparison_cases':sum('parser_expected' not in c for c in cases),
            'separate_parser_contract_cases':sum('parser_expected' in c for c in cases),
            'input_sha256':hashlib.sha256(input_bytes).hexdigest(),
            'cpp_output_sha256':hashlib.sha256(child.stdout).hexdigest(),
            'limits':{'harness_cpu_seconds':90,'harness_wall_seconds':120,
                      'harness_address_space_bytes':512*1024**2,
                      'cpp_cpu_seconds':45,'cpp_wall_seconds':60,'cpp_address_space_bytes':256*1024**2},
            'elapsed_seconds':round(time.monotonic()-start,3),
            'no_float_certification':True,'float_values_only_used_as_refusal_type_fixtures':True,
            'failure_count':len(failures),'failures':failures[:10],
            'scope':'interval/exp_neg primitives only; finite differential evidence, not full330-feature/inverse/confidence or formal proof'}
    (output/'differential.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2)); return bool(failures)


if __name__=='__main__': raise SystemExit(main())
