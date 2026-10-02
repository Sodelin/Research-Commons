#!/usr/bin/env python3
"""Independent exact finite CParty-band geometry check; no source/energy claim."""
from itertools import combinations
from pathlib import Path
import json
SEQ = 'GGAAGCGCAACC'
PAIRS = ((0,7),(1,5),(4,11),(6,10))
SCAFFOLD = frozenset((PAIRS[0],PAIRS[1]))
EXTENSION = frozenset((PAIRS[2],PAIRS[3]))

def cross(p,q):
    a,b=p; c,d=q
    return a<c<b<d or c<a<d<b

def nested(p,q):
    a,b=p; c,d=q
    return a<c<d<b or c<a<b<d

def band_core(B):
    if not B or not all(nested(p,q) for p,q in combinations(B,2)):
        return False
    outside=set(PAIRS)-set(B)
    if not all(len({cross(p,q) for p in B})==1 for q in outside):
        return False
    # Use the paper's MEMBER-WISE crossing requirement, independently of
    # the Lean draft's common-external-neighbor wording.
    return all(any(cross(p,q) for q in PAIRS) for p in B)

cores=[frozenset(B) for r in range(1,len(PAIRS)+1) for B in combinations(PAIRS,r) if band_core(B)]
bands=[B for B in cores if not any(B<C for C in cores)]
adj={i:{j for j,C in enumerate(bands) if i!=j and any(cross(p,q) for p in B for q in C)} for i,B in enumerate(bands)}
components=[]; unseen=set(adj)
while unseen:
    root=min(unseen); comp={root}; stack=[root]
    while stack:
        for j in adj[stack.pop()]-comp:
            comp.add(j); stack.append(j)
    unseen-=comp; components.append(sorted(comp))

def coverage(strict):
    return [[sum(any((a<k<b if strict else a<=k<=b) for a,b in bands[i]) for i in comp)
             for k in range(len(SEQ))] for comp in components]
strict=coverage(True); inclusive=coverage(False)
canonical={('A','U'),('U','A'),('C','G'),('G','C'),('G','U'),('U','G')}
endpoints=[x for p in PAIRS for x in p]
assert len(set(endpoints))==len(endpoints)
assert all((SEQ[a],SEQ[b]) in canonical and a<b and b-a>=4 for a,b in PAIRS)
assert not any(cross(p,q) for P in [SCAFFOLD,EXTENSION] for p,q in combinations(P,2))
assert set(x for p in SCAFFOLD for x in p).isdisjoint(x for p in EXTENSION for x in p)
assert len(bands)==4 and all(len(B)==1 for B in bands)
assert len(components)==1 and max(strict[0])==2 and max(inclusive[0])==3
colors={PAIRS[0]:0,PAIRS[1]:0,PAIRS[2]:1,PAIRS[3]:1}
assert all(colors[next(iter(bands[i]))]!=colors[next(iter(bands[j]))] for i in adj for j in adj[i])
result={'status':'PASS_EXACT_GEOMETRY_REGRESSION','sequence':SEQ,'zero_based_pairs':[list(p) for p in PAIRS],
'scaffold':[list(p) for p in sorted(SCAFFOLD)],'extension':[list(p) for p in sorted(EXTENSION)],
'maximal_bands':[[list(p) for p in sorted(B)] for B in bands],
'crossing_graph_edges':[[i,j] for i in adj for j in sorted(adj[i]) if i<j],
'connected_components':components,'strict_cover_counts':strict,'inclusive_cover_counts':inclusive,
'strict_density':max(strict[0]),'inclusive_density':max(inclusive[0]),
'claims':{'matching_and_canonical':True,'both_planar_and_fresh':True,'minimum_pair_span':min(b-a for a,b in PAIRS),
'old_strict_Gamma_accepts_geometry':True,'corrected_inclusive_Gamma_rejects_geometry':True,
'physical_DP09_or_source_positive_attainment_verified':False,'biological_master_claim':False}}
Path(__file__).with_name('density-endpoint-fixture-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
