#!/usr/bin/env python3
"""Exact arithmetic and small recurrence transcription checks, not a proof."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
S=203*5**6
E=sum(15**m for m in range(6))
D=3*S*S+S
M=64*E*(6*E)**3
K=2*M*(2*D+1)
L=1024*(K-1)
assert L==748902056957898604139213494218915309705755648

def convolve(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out

checks=0
# Equal bases deliberately repeated; base=1 included.
for bases in [(F(1),),(F(2,3),F(2,3)),(F(1),F(2,5),F(3,7))]:
    for d in range(4):
        annih=[F(1)]
        for base in bases:
            for _ in range(d+1):annih=convolve(annih,[-base,F(1)])
        assert annih[-1]==1
        order=len(annih)-1
        def f(n):return sum((j+1)*(n+2*j+1)**d*base**n for j,base in enumerate(bases))
        values=[f(n) for n in range(order)]
        for n in range(8):
            nxt=-sum(annih[i]*values[n+i] for i in range(order))
            values.append(nxt)
            assert nxt==f(n+order)
            assert sum(annih[i]*f(n+i) for i in range(order+1))==0
            checks+=1
result={'status':'PASS','S':S,'E':E,'F':D,'M':M,'K':K,'L_bound':L,
        'exact_recurrence_checks':checks,'includes_coincident_bases_and_base_one':True,
        'limits':'Supplementary finite arithmetic and recurrence controls; all-contract validity requires the reviewed hand proof.'}
Path(__file__).with_name('BOUND-CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
