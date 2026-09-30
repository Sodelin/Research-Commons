"""Exact counterexample to the generic containing-reference-tree lemma.

No third-party packages. Imported graph generator is preserved inherited input.
This tests a binary tree FAMILY, not source-network admission.
"""
from pathlib import Path
from itertools import combinations, permutations
import sys,json,platform
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'2026-09-30-root-exact-query'))
from verify_candidate_order import trees,graph_splits,is_circular
sys.path.insert(0,str(HERE.parent/'2026-09-30-astra-sparse-query'))
from sparse_quartet import graph_from_shape,physical_quartet_oracle
N=7;Y=tuple(range(1,N));PAIR=list(combinations(Y,2));PIN={p:i for i,p in enumerate(PAIR)};TRIP=list(combinations(Y,3))
G1=frozenset([(-5,-4),(-5,5),(-5,6),(-4,-3),(-4,4),(-3,-2),(-3,0),(-2,-1),(-2,3),(-1,1),(-1,2)])
G2=frozenset([(-5,-3),(-5,-1),(-5,6),(-4,-3),(-4,4),(-4,5),(-3,-2),(-2,2),(-2,3),(-1,0),(-1,1)])
SPLITS=[graph_splits(g,N) for g in (G1,G2)]
assert all(is_circular(s,tuple(range(N))) for ss in SPLITS for s in ss)
def rooted_topology(ss,q):
    qq=(0,)+q
    out=0
    for j,p in enumerate(combinations(q,2)):
        if any(sum(bool(s&(1<<a)) for a in qq)==2 and
               (all(s&(1<<a) for a in p) or all(not s&(1<<a) for a in p)) for s in ss):out|=1<<j
    assert out in (1,2,4)
    return out
PROFILE=tuple(rooted_topology(SPLITS[0],q)|rooted_topology(SPLITS[1],q) for q in TRIP)
assert PROFILE==(5,5,5,5,5,5,5,4,4,4,1,1,1,4,5,5,4,5,5,5)
HISTORY=(9,12,2,7,0,10,19,16,15)
def cmp(u,a,b):return ((u>>PIN[tuple(sorted((a,b)))])&1)^(a>b)
def satisfies(u,q,mask):
    x,y,z=q
    for j,(a,b,c) in enumerate(((x,y,z),(x,z,y),(y,z,x))):
        if mask>>j&1 and cmp(u,c,a)!=cmp(u,c,b):return False
    return True
def ordervector(p):
    pos={a:i for i,a in enumerate(p)}
    return sum((pos[a]>pos[b])<<i for i,(a,b) in enumerate(PAIR))
ORDERS={ordervector(p):p for p in permutations(Y)}
SOLUTIONS={u for u in range(1<<len(PAIR)) if all(satisfies(u,TRIP[j],PROFILE[j]) for j in HISTORY)}
assert len(SOLUTIONS)==4 and SOLUTIONS<=ORDERS.keys()
EXPECTED={(1,2,3,4,5,6),(1,4,2,5,3,6),(6,3,5,2,4,1),(6,5,4,3,2,1)}
assert {ORDERS[u] for u in SOLUTIONS}==EXPECTED
allgraphs=trees(N)
for g in allgraphs:
    ss=graph_splits(g,N)
    assert not all(all(is_circular(s,(0,)+ORDERS[u]) for s in ss) for u in SOLUTIONS)
# Close the two correlated selections under independent copy choices.
# Rooted tip shape 1outer / (M / 6outer), M=((1inner,2),3)/(4/(5,6inner)).
shape=(1,((((2,3),4),(5,(6,7))),8));copies=[[0],[1,2],[3],[4],[5],[6],[7,8]]
physical=physical_quartet_oracle(graph_from_shape(shape,9),copies)
# On anchored156, physical mask1 means rooted56; mask4 means rooted15.
assert physical((0,1,5,6))==5
assert PROFILE[TRIP.index((1,5,6))]==4
report={'status':'PASS','created_utc':datetime.now(timezone.utc).isoformat(),'python':platform.python_version(),
 'scope':'Exact generic common-order binary tree-family counterexample; no source-network counterexample',
 'family_rooted_newick':['(((1,2),3),(4,(5,6)))','(1,(6,((2,3),(4,5))))'],
 'family_graphs':[sorted(G1),sorted(G2)],'full_anchored_profile':PROFILE,
 'rooted_bit_semantics':['xy|rz','xz|ry','yz|rx'],
 'queried_triples':[TRIP[j] for j in HISTORY],
 'queried_masks':[PROFILE[j] for j in HISTORY],
 'all_partial_affine_assignments_transitive':True,'partial_orders':sorted(EXPECTED),
 'containing_binary_trees_excluded':len(allgraphs),
 'independent_copy_completion_adds_anchored156_topology':True,
 'limits':'Correlated two-tree family not established admitted. Independent adjacent-copy completion destroys the bad parity space.'}
HERE.joinpath('adaptive-construction-countercheck.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
