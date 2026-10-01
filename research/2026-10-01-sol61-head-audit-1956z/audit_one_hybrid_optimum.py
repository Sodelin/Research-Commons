"""Source-matched sharp G7 exact-law 4-taxon/1-hybrid branch.

The census is adapted only by replacing general NetworkX planarity with an
exact class-specific theorem: a connected multigraph of cyclomatic rank <=1
is outerplanar, so all marked vertices are cofacial. This is NOT an unchanged
replay of verify_census.py. All other original census definitions are parsed
from the pinned source bytes. No source files are overwritten.
"""
import ast, hashlib, json, sys
from pathlib import Path
from itertools import permutations, product
from collections import defaultdict
import sympy as sp
from argparse import ArgumentParser
parser=ArgumentParser(description=__doc__)
parser.add_argument("--source-dir", default=str(Path(__file__).resolve().parent.parent / "2026-10-01-g7-continuous-design"))
args=parser.parse_args()
source_dir=Path(args.source_dir).resolve()
expected={"law_compiler.py":"0fed445a5b7f72ebe056f8b8778d8e67dcc898e2", "verify.py":"8b87285316c2a3dc844fcc87ca0a46a8308906cb", "source_census.py":"3873aeb667576bea857a3ebfcdf803824c7fcc79"}
for name,sha in expected.items():
    raw=(source_dir/name).read_bytes()
    assert hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest()==sha, name+" source bytes mismatch"
sys.path.insert(0,str(source_dir))
from law_compiler import Network, forest, split_signature, compile_law, unrooted_law, evaluate
from verify import TRIANGLE, DIAMOND, SPLITS, add_bigon

source=(source_dir/'source_census.py').read_text()
names={'reachable','admitted','canonical_key','census','displayed'}

def cofacial(edges,marked):
    vertices={v for edge in edges for v in edge}
    assert set(marked)<=vertices
    assert len(vertices)==len(reachable(edges,next(iter(vertices)),undirected=True))
    cycle_rank=len(edges)-len(vertices)+1
    assert 0<=cycle_rank<=1, 'The exact outerplanarity shortcut is only for rank <=1.'
    return True

tree=ast.parse(source)
selected=ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names],type_ignores=[])
exec(compile(selected,'pinned_census_rank_one_definitions','exec'),globals())

def decode_pooled_quartet(law):
    baseline=min(law.values())
    return frozenset(t for t,p in law.items() if p>baseline)

nets=list(census(4,1)); assert len(nets)==546
compiled=0; margins=[]; targets=set()
for net in nets:
    hybrid=net.structure()[3][0]
    answers=displayed(net)
    edgevals={i:sp.Rational(i+4,i+7) for i in range(len(net.edges))}
    laws=[unrooted_law(compile_law(net,'independent',{hybrid:b},edge_values=edgevals)) for b in (0,1)]
    pooled={t:sp.expand((laws[0][t]+laws[1][t])/2) for t in laws[0]}
    assert sum(pooled.values())==1
    Q=set(answers.values()); baseline=min(pooled.values())
    assert decode_pooled_quartet(pooled)==Q
    margins.append(min(pooled[t]-baseline for t in Q))
    targets.add(tuple(sorted(Q))); compiled+=2

# Lower bound for one forced row: match the forced diamond's displayed tree
# with a source of singleton target and one neutral pendant hybrid.
# Use 4/5 on all diamond edges. The selected displayed tree has a strictly
# positive total internal length, recovered as survival = 3*minor CF.
dx,dg=DIAMOND.parameters(); dv={i:sp.Rational(4,5) for i in range(len(dx))}
forced_collision=[]
for bit in (0,1):
    law=unrooted_law(compile_law(DIAMOND,'independent',{'H':bit},edge_values=dv))
    major=max(law,key=law.get); minor=next(p for t,p in law.items() if t!=major)
    survival=3*minor; assert 0<survival<1
    side0,side1=major[0]
    a,b=side0; c,d=side1
    tree_net=Network((('R',a),('R','U'),('U',b),('U','V'),('V',c),('V',d)),'R',(a,b,c,d))
    padded=add_bigon(tree_net,a,0)
    assert admitted(padded)
    vals={i:sp.Rational(4,5) for i in range(len(padded.edges))}
    internal=next(i for i,e in enumerate(padded.edges) if e==('U','V'))
    vals[internal]=survival
    match=unrooted_law(compile_law(padded,'independent',{'padH0':bit},edge_values=vals))
    assert match==law
    assert set(displayed(padded).values())=={major}
    assert set(displayed(DIAMOND).values())!={major}
    forced_collision.append({'forced_bit':bit,'law':[str(law[t]) for t in SPLITS],'singleton_target':repr(major),'survival':str(survival)})

# Natural one-row lower bound: explicit positive admitted triangle/diamond.
tx,tg=TRIANGLE.parameters(); tv={i:sp.Rational(9,10) for i in range(len(tx))}; tv[2]=sp.Rational(1,10)
tlaw=unrooted_law(compile_law(TRIANGLE,'independent',edge_values=tv,inheritance_values={'H':sp.Rational(1,2)}))
dv={i:sp.Rational(4,5) for i in range(len(dx))};dv[2]=dv[3]=sp.Rational(177,200)
dlaw=unrooted_law(compile_law(DIAMOND,'independent',edge_values=dv,inheritance_values={'H':sp.Rational(1,2)}))
assert admitted(TRIANGLE) and admitted(DIAMOND)
assert tlaw==dlaw and set(displayed(TRIANGLE).values())!=set(displayed(DIAMOND).values())

result={'status':'PASS','contract':'unknown admitted four-taxon graph; exactly one complete named hybrid with parent labels; independent inheritance; positive finite edge lengths/interior gamma; unrooted one-copy exact laws; pooled full forcing; worst-case distinct pathwise costs',
 'sharp_costs':{'actuated_sites':1,'distinct_configurations':2,'executed_programs':1},
 'census_graphs':len(nets),'full_forcing_law_compilations':compiled,'distinct_target_sets':len(targets),
 'positive_margin_all_numeric_cases':all(m>0 for m in margins),
 'natural_collision_law':[str(tlaw[t]) for t in SPLITS], 'forced_one_row_collisions':forced_collision,
 'planarity_gate':'exact connected rank<=1 outerplanarity theorem, replacing NetworkX only in this adapted one-hybrid census',
 'versions':{'python':sys.version.split()[0],'sympy':sp.__version__},
 'limits':'Uniform positive-parameter validity and lower bounds are hand proved in ONE-HYBRID-OPTIMUM.md. Rational exhaustive graph controls are finite replay, not full symbolic/formal verification or unrestricted G7 closure.'}
Path(__file__).with_name('one-hybrid-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
