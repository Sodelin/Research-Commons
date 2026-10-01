"""Fresh admitted G1/G2 foundation controls; exact source parameters/rows.
No historical sealed-proof hash equivalence, calendar reduction or novelty claim.
"""
import sys,json,hashlib
from pathlib import Path
from itertools import combinations
from collections import defaultdict
from argparse import ArgumentParser
a=ArgumentParser(description=__doc__)
a.add_argument("--source-dir",default=str(Path(__file__).resolve().parent.parent/"2026-10-01-g7-continuous-design"))
args=a.parse_args();sd=Path(args.source_dir).resolve()
for name,sha in {"law_compiler.py":"0fed445a5b7f72ebe056f8b8778d8e67dcc898e2","verify.py":"8b87285316c2a3dc844fcc87ca0a46a8308906cb","source_census.py":"3873aeb667576bea857a3ebfcdf803824c7fcc79"}.items():
 b=(sd/name).read_bytes();assert hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==sha
sys.path.insert(0,str(sd))
import sympy as s
import networkx as nx
from law_compiler import Network,compile_law,unrooted_law,forest,split_signature
from source_census import admitted,displayed
from verify import PAIR,TRIANGLE,DIAMOND,SPLITS

# Saturated three-port outer-labeled ladder; root uses same module with no entry.
def sharp_core(n):
 edges=[]; counter=[0]
 def build(leaves,entry):
  k=counter[0];counter[0]+=1
  U,V,LH,RH=(f'U{k}',f'V{k}',f'HL{k}',f'HR{k}')
  edges.extend(((entry,LH),(entry,U),(U,RH),(U,V),(V,LH),(V,RH)))
  groups=(leaves[:len(leaves)//2],leaves[len(leaves)//2:])
  for h,g in zip((LH,RH),groups):
   if len(g)==1:edges.append((h,g[0]))
   else:
    e=f'E{counter[0]}';edges.append((h,e));build(g,e)
 build(tuple(f'L{i}' for i in range(n)),'R')
 return Network(tuple(edges),'R',tuple(f'L{i}' for i in range(n)))

sharp=[]
for n in range(4,11):
 net=sharp_core(n);inc,out,order,hs=net.structure()
 assert admitted(net)
 assert len(hs)==2*n-2 and len(order)==6*n-5 and len(net.edges)==8*n-8
 G=nx.Graph();G.add_edges_from(net.edges)
 blocks=[B for B in nx.biconnected_components(G) if len(B)>2]
 assert len(blocks)==n-1
 for B in blocks:
  ports=sum((u in B)!=(v in B) for u,v in net.edges)
  assert ports==(2 if net.root in B else 3)
 sharp.append({'n':n,'r':len(hs),'V':len(order),'E':len(net.edges),'cyclic_blocks':len(blocks)})

# Re-establish original G2D numbers with one positive graph/one gamma per state.
BASE=Network((('R','U'),('R','V'),('U','H'),('U','H'),('H','W'),('W','A'),('W','B'),('V','C'),('V','D')),'R',('A','B','C','D'))
assert admitted(BASE)
def state(c,a,x0,x1):
 vals={i:s.Rational(1,2) for i in range(len(BASE.edges))}
 vals[0]=a; vals[2]=x0;vals[3]=x1;vals[4]=c
 return vals
A=state(s.Rational(1,2),s.Rational(1,2),s.Rational(1,2),s.Rational(1,2))
B=state(s.Rational(3,4),s.Rational(2,3),s.Rational(1,4),s.Rational(1,4))
endpoint_equal=0
for bit in (0,1):
 la=compile_law(BASE,'independent',{'H':bit},edge_values=A,inheritance_values={'H':s.Rational(1,2)})
 lb=compile_law(BASE,'independent',{'H':bit},edge_values=B,inheritance_values={'H':s.Rational(1,2)})
 assert la==lb; endpoint_equal+=len(la)
 q=unrooted_law(la);assert [q[t] for t in SPLITS]==[s.Rational(23,24),s.Rational(1,48),s.Rational(1,48)]
na=unrooted_law(compile_law(BASE,'independent',edge_values=A,inheritance_values={'H':s.Rational(1,2)}))
nb=unrooted_law(compile_law(BASE,'independent',edge_values=B,inheritance_values={'H':s.Rational(1,2)}))
assert [na[t] for t in SPLITS]==[s.Rational(15,16),s.Rational(1,32),s.Rational(1,32)]
assert [nb[t] for t in SPLITS]==[s.Rational(43,48),s.Rational(5,96),s.Rational(5,96)]
assert set(displayed(BASE).values())=={SPLITS[0]}

# Safe categorical pullback: common coin (or a site with <=1 live lineage).
vals=state(s.Rational(1,2),s.Rational(1,2),s.Rational(1,2),s.Rational(1,4))
common_coordinates=0; ind_failure=0
for ga,gb in ((s.Rational(1,3),s.Rational(2,3)),(s.Rational(2,3),s.Rational(1,3))):
 for mode in ('common','independent'):
  target=compile_law(BASE,mode,edge_values=vals,inheritance_values={'H':ga})
  natural=compile_law(BASE,mode,edge_values=vals,inheritance_values={'H':gb})
  bit=0 if ga>=gb else 1
  endpoint=compile_law(BASE,mode,{'H':bit},edge_values=vals,inheritance_values={'H':gb})
  w=(1-ga)/(1-gb) if ga>=gb else ga/gb
  pulled={t:s.expand(w*natural[t]+(1-w)*endpoint[t]) for t in target}
  if mode=='common': assert pulled==target; common_coordinates+=len(target)
  else: assert pulled!=target; ind_failure+=1

# Same-source all-copy projection for natural and original-ID fixed rows.
def prune(t,keep):
 if isinstance(t,str):return t if t in keep else None
 roots=[prune(x,keep) for x in t]; roots=[x for x in roots if x is not None]
 if not roots:return None
 if len(roots)==1:return roots[0]
 return forest(roots)
def project(law,keep):
 out=defaultdict(lambda:s.S.Zero)
 for t,p in law.items():out[prune(t,keep)]+=p
 return {t:s.expand(p) for t,p in out.items()}
proj_coordinates=proj_cases=0
for net in (BASE,TRIANGLE,DIAMOND,PAIR,sharp_core(4)):
 hs=net.structure()[3];v={i:s.Rational(i+4,i+7) for i in range(len(net.edges))};g={h:s.Rational(2,5) for h in hs}
 leaf=net.leaves[0];samples={x:(x,) for x in net.leaves};samples[leaf]=(leaf,'EXTRA')
 for mode in ('independent','common'):
  for force in ({},{hs[0]:0},{hs[0]:1}):
   small=compile_law(net,mode,force,edge_values=v,inheritance_values=g)
   large=compile_law(net,mode,force,samples=samples,edge_values=v,inheritance_values=g)
   assert project(large,set(net.leaves))==small
   proj_coordinates+=len(small);proj_cases+=1

# Broader causal register interface needs conditioning, not fresh marginal draws.
original=s.Rational(1,2)*s.Rational(1,2)
resampled=s.Rational(1,2)*(s.Rational(1,2)*s.Rational(1,2)+s.Rational(1,2)*s.Rational(1,4))
assert original==s.Rational(1,4) and resampled==s.Rational(3,16)
report={'status':'PASS','sharp_core_sources':sharp,'G2D_endpoint_rooted_coordinates':endpoint_equal,'G2D_forced_CF':['23/24','1/48','1/48'],'G2D_natural_A_CF':[str(na[t]) for t in SPLITS],'G2D_natural_B_CF':[str(nb[t]) for t in SPLITS],
 'common_categorical_pullback_coordinates':common_coordinates,'independent_locus_mixture_countercontrols':ind_failure,'same_source_projection_cases':proj_cases,'same_source_projection_coordinates':proj_coordinates,
 'conditional_register_countercontrol':{'retained_shared_coin':'1/4','incorrect_independent_resampling':'3/16'},
 'versions':{'python':sys.version.split()[0],'sympy':s.__version__,'networkx':nx.__version__},
 'limits':'Fresh finite controls and new hand source proofs, not retrieved historical sealed B/D/projectivity bundles or all-size formal verification. Conditional-register test is an interface countercontrol beyond private natural-source coins, not a failure in the original private-source domain.'}
Path(__file__).with_name('foundation-source-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
