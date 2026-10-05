"""Exact finite-algebra certificate for an all-word natural-source quotient.
No numerical sign sampling and no source-attainment conclusion.
"""
from pathlib import Path
import json,pickle,hashlib
from fractions import Fraction as Q
from probe_first_composable_blocks import Algebra,F
p=Path(__file__).parent
c=pickle.loads((p/'first-composable-working-cache.pkl').read_bytes())
a=Algebra(6);assert a.coords==c['coords'] and a.tab==c['table']
raw=json.loads((p/'FIRST-BLOCK-ROWS-WORKING.json').read_text())
rows={name:tuple(Q(next((r for r,k,s in raw[name] if (k,s)==co),'0')) for co in a.coords) for name in ['a64','b42','c62']}
def ip(row,v):return sum((x*y for x,y in zip(row,v)),Q(0))
def matrix(v):
 d={k:v[a.ix[k,'|'.join(['o']*k)]] for k in [2,4,6]}
 return ((d[6],ip(rows['a64'],v),ip(rows['c62'],v)),(Q(0),d[4],ip(rows['b42'],v)),(Q(0),Q(0),d[2]))
def mm(x,y):return tuple(tuple(sum((x[i][k]*y[k][j] for k in range(3)),Q(0)) for j in range(3)) for i in range(3))
mons=sorted(set().union(*(set(q) for q in c['polys'])))
coeff=[tuple(q.get(mon,Q(0)) for q in c['polys']) for mon in mons]
idem=[a.idem(r) for r in range(1,7)]
gens=coeff+idem
sp=F.Span(a.d);sp.add(a.unit)
for v in gens:sp.add(v)
passes=[]
while True:
 old=len(sp)
 for v in list(sp.original):
  for w in gens:
   sp.add(a.mul(v,w));sp.add(a.mul(w,v))
 passes.append([old,len(sp)])
 if len(sp)==old:break
# The complete generator coefficient family leaves the computed space invariant.
for v in sp.original:
 for w in gens:assert sp.contains(a.mul(v,w)) and sp.contains(a.mul(w,v))
# Bilinear verification on a FULL basis makes this a homomorphism on its whole algebra.
for v in sp.original:
 for w in sp.original:assert matrix(a.mul(v,w))==mm(matrix(v),matrix(w))
for v in coeff:assert ip(rows['c62'],v)==Q(3,4)*ip(rows['a64'],v)
for v in idem:assert all(ip(row,v)==0 for row in rows.values())
out={'status':'EXACT_ALL_WORD_QUOTIENT_CERTIFICATE_PASS','source':'natural INDEPENDENT current-root routing; same parameters at all arities; actual forest graft algebra','cap':6,'full_labelled_coordinates':sum(map(len,a.full.values())),'exchangeable_coordinates':a.d,'coefficient_generators':len(gens),'invariant_source_span_dimension':len(sp),'closure_passes':passes,'basis_pair_homomorphism_checks':len(sp)**2,'generator_invariance_checks':2*len(sp)*len(gens),'bare_cell_identity':'c=3a/4','ordinary_diagonal_exponents':[15,6,1],'recurrence':raw['allword_recurrence'],'limits':'This certifies an exact quotient and parameter-family signs. It is not a finite-word budget, arbitrary-cap theorem, positive return, or G3/G4 recognizer.'}
(p/'FIRST-BLOCK-QUOTIENT-VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
