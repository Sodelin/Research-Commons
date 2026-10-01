"""Exact all-r witness family for static FULL-forcing numerical-law lower bounds.
No assertion about partial forcing, adaptive row minima, richer readouts or loci.
"""
from itertools import product,combinations
from pathlib import Path
import json,sys,hashlib
from argparse import ArgumentParser
p=ArgumentParser(description=__doc__)
p.add_argument('--source-dir',default=str(Path(__file__).resolve().parent.parent/'2026-10-01-g7-continuous-design'))
a=p.parse_args(); sd=Path(a.source_dir).resolve()
for name,sha in {'law_compiler.py':'0fed445a5b7f72ebe056f8b8778d8e67dcc898e2','verify.py':'8b87285316c2a3dc844fcc87ca0a46a8308906cb'}.items():
 b=(sd/name).read_bytes(); assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha
sys.path.insert(0,str(sd))
import sympy as s
from law_compiler import Network,compile_law,unrooted_law
from verify import PAIR,SPLITS,add_bigon

def swap_bc(net):
 rename={'B':'C','C':'B'}
 return Network(tuple((rename.get(u,u),rename.get(v,v)) for u,v in net.edges),net.root,net.leaves)

# Whole symbolic laws, same edge symbols on both sources and all rows.
symbolic_equal=0
for bits in product((0,1),repeat=2):
 force=dict(zip(('HA','HC'),bits))
 left=unrooted_law(compile_law(PAIR,'independent',force))
 right=unrooted_law(compile_law(swap_bc(PAIR),'independent',force))
 equal=all(s.expand(left[t]-right[t])==0 for t in SPLITS)
 assert equal == (bits!=(1,0))
 symbolic_equal+=int(equal)

# Parent-labelled source family, arbitrary active-ID placements/cylinder bits.
def family(r,i,j,desired):
 names={'HA':f'H{i}','HC':f'H{j}'}
 net=Network(tuple((names.get(u,u),names.get(v,v)) for u,v in PAIR.edges),PAIR.root,PAIR.leaves)
 # A parent bit is incoming-edge index order. Reverse those two entries when
 # needed, retaining the same physical DAG and all nonrouting edge variables.
 edges=list(net.edges)
 for h,wanted,old in ((f'H{i}',desired[0],1),(f'H{j}',desired[1],0)):
  if wanted!=old:
   ix=[k for k,(_,v) in enumerate(edges) if v==h]
   edges[ix[0]],edges[ix[1]]=edges[ix[1]],edges[ix[0]]
 net=Network(tuple(edges),net.root,net.leaves)
 for k in range(r):
  if k not in (i,j):
   old=add_bigon(net,'B',k)
   net=Network(tuple((f'H{k}' if u==f'padH{k}' else u,f'H{k}' if v==f'padH{k}' else v) for u,v in old.edges),old.root,old.leaves)
 return net,swap_bc(net)

cases=rows=laws=0
for r in range(2,6):
 for i,j in combinations(range(r),2):
  for desired in product((0,1),repeat=2):
   left,right=family(r,i,j,desired)
   assert left.structure()[3]==right.structure()[3]
   # One fixed nonuniform assignment per graph, shared across every row.
   vals={k:s.Rational(k+4,k+7) for k in range(len(left.edges))}
   for bits in product((0,1),repeat=r):
    force={f'H{k}':bit for k,bit in enumerate(bits)}
    pl=unrooted_law(compile_law(left,'independent',force,edge_values=vals))
    pr=unrooted_law(compile_law(right,'independent',force,edge_values=vals))
    inside=(bits[i],bits[j])==desired
    assert (pl==pr) == (not inside)
    if inside:
     assert max(pl,key=pl.get)==SPLITS[0] and max(pr,key=pr.get)==SPLITS[1]
    else:
     assert max(pl,key=pl.get)==max(pr,key=pr.get)==SPLITS[2]
    assert sum(pl.values())==sum(pr.values())==1
    rows+=1; laws+=2
   cases+=1

result={'status':'PASS','contract':'static parameter-oblivious fully forced original-ID programmes; exact unrooted four-taxon one-copy law; fixed shared parameters across rows; selected-row labels may be retained or pooled',
 'all_parameter_symbolic_core_equal_rows':symbolic_equal,
 'symbolic_core_unequal_hidden_row':True,
 'padded_parent_labelled_witness_pairs':cases,'full_configurations_checked':rows,'exact_rational_law_compilations':laws,
 'r_values':[2,3,4,5],'active_placements':'all unordered active-ID pairs and all four named missing cylinders',
 'parameters':'one nonuniform rational edge assignment per graph, reused across every response row and across the taxon-swap pair',
 'sharp_static_full_forcing_configuration_minimum':'binary strength-two covering-array C(r)',
 'sharp_program_minimum_with_positive_support_cap_L':'ceil(C(r)/L)',
 'limits':'General source-admission/padding and source two-switch upper bound are hand proofs. No partial-row/adaptive/richer-readout or historical-novelty claim; no proof assistant.'}
Path(__file__).with_name('forced-menu-collision-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
