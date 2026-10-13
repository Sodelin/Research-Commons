"""Exact transcription control only; no universal derivative/local theorem check."""
from __future__ import annotations
import importlib.util
import json
from pathlib import Path
from fractions import Fraction
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[3]
PROVIDER = ROOT / 'research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py'
spec = importlib.util.spec_from_file_location('g4_forest_provider', PROVIDER)
fa = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fa)
alg = fa.ForestAlgebra(4)
polys = alg.cell_polynomials('independent')

def reduced(poly, g_order=0):
    out=defaultdict(Fraction)
    for (ex,ey,eg,ea),c in poly.items():
        if eg < g_order:
            continue
        coeff = c
        for j in range(g_order):
            coeff *= eg-j
        out[ex+ey] += coeff * Fraction(1,2)**(eg-g_order)
    return {e:c for e,c in out.items() if c}

b=[reduced(p) for p in polys]
bgg=[reduced(p,2) for p in polys]
qgen=tuple(-sum(Fraction(e)*c for e,c in fa.edge_polynomials(k)[f].items())
           for k,f in alg.coords)
lhs=[defaultdict(Fraction) for _ in alg.coords]
for i,j,z in alg.table:
    for e,c in b[j].items():
        lhs[z][e] += qgen[i]*c
rhs=[]
for bp,gp in zip(b,bgg):
    exponents=set(bp)|set(gp)
    rhs.append({e:-2*e*bp.get(e,0)+Fraction(1,8)*gp.get(e,0)
                for e in exponents})
failed=[]
for c,lp,rp in zip(alg.coords,lhs,rhs):
    if any(lp.get(e,0)!=rp.get(e,0) for e in set(lp)|set(rp)):
        failed.append(repr(c))
assert not failed, failed
shape_examples=[]
for i,(k,f) in enumerate(alg.coords):
    if k==4 and len(f)==2:
        sizes=sorted(len(fa.leaves(t)) for t in f)
        if sizes in ([1,3],[2,2]) and not any(x['root_leaf_sizes']==sizes for x in shape_examples):
            shape_examples.append({'forest':repr(f),'root_leaf_sizes':sizes,
               'Q_times_B_polynomial':{str(e):str(c) for e,c in sorted(lhs[i].items()) if c}})
result={'status':'PASS','arithmetic':'exact rational coefficient identities in q',
        'cap':4,'full_forest_coordinates_checked':alg.dim,
        'identity':'Q*B = 2 B_t - B_p/4 = 2 B_t + B_gg/8 at equal arms and g=1/2',
        'shape_examples':shape_examples,
        'scope':'Transcription control of inherited all-cap WF identity only; no hierarchy derivative, local theorem, G4 closure, or Lean verification.'}
Path(__file__).with_name('FAIR-FULL-GENERATOR-CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
