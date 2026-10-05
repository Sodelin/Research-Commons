"""Declared arithmetic constraints from already published forward outputs; no simulation."""
import json
from fractions import Fraction as F
from pathlib import Path
import filter_core as c
REFERENCE=c.BASE.parent/'msci-330-feature-public-20261005-1039z/evaluator/CONTROL-RESULTS.json'
REFERENCE_SHA='acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a'

def reference(fixture='distinct_rates'):
    r,_=c.read_json(REFERENCE,REFERENCE_SHA);return r['fixtures'][fixture]

def request_dict(fixture='distinct_rates',kind='contains',**overrides):
    ref=reference(fixture);p={k:F(v) for k,v in ref['parameters'].items()}
    centre=(p['h'],p['t1']-p['h'],p['t0']-p['t1'],p['rA'],p['rB'],p['rC'],p['rAB'],p['rR'],p['g'])
    if kind=='separated':centre=(F(1,8),F(1,8),F(1,8),*centre[3:]);radii=(F(1,1<<20),)*9
    else:radii=(F(1,512),)*3+(F(1,128),)*5+(F(1,512),)
    box=tuple((x-r,x+r) for x,r in zip(centre,radii))
    if kind=='unsupported':
        q=2**129+1;box=((F(1,16)+F(1,q),F(1,16)+F(1,q-2)),*box[1:])
    if kind=='point':box=tuple((x,x) for x in centre)
    if kind=='broad':box=((F(1,16),F(1,8)),)*3+((F(1),F(5)),)*5+((F(1,5),F(4,5)),)
    if kind not in {'contains','separated','unsupported','point','broad'}:raise c.Invalid('undeclared fixture kind')
    features={pair:[{'k':row['k'],'bounds':[row['mean_interval']['lower'],row['mean_interval']['upper']]} for row in ref['features'][pair]] for pair in c.PAIRS}
    budget=dict(max_evaluations=8,max_splits=8,max_depth=8,wall_ms=10000,recovery_wall_ms=10000,recovery_max_witnesses=32,precision_bits=64,cell_mesh='0');budget.update(overrides)
    return {'schema':'bounded-msci-filter-request-v1','model':c.MODEL,'quantity':c.QUANTITY,'box':c.box_record(box),'features':features,'budget':budget,'provenance':{'kind':'published_deterministic_arithmetic_fixture','reference_sha256':REFERENCE_SHA,'fixture':fixture,'box_kind':kind,'statistical_coverage_claimed':False}}

def write_request(path,d):
    raw=c.canonical(d)
    with Path(path).open('xb') as out:out.write(raw)
    return c.sha(raw)
