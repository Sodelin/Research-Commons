"""Exact natural-CF + one labelled full-forcing marker decoder.
No finite-data certification or b<r simultaneous-control optimum is asserted.
"""
import sys,json,hashlib
from pathlib import Path
from itertools import product
from collections import Counter
from argparse import ArgumentParser
p=ArgumentParser(description=__doc__)
p.add_argument('--source-dir',default=str(Path(__file__).resolve().parent.parent/'2026-10-01-g7-continuous-design'))
a=p.parse_args(); sd=Path(a.source_dir).resolve()
for name,sha in {'law_compiler.py':'0fed445a5b7f72ebe056f8b8778d8e67dcc898e2','verify.py':'8b87285316c2a3dc844fcc87ca0a46a8308906cb','source_census.py':'3873aeb667576bea857a3ebfcdf803824c7fcc79'}.items():
 b=(sd/name).read_bytes(); assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha
sys.path.insert(0,str(sd))
import sympy as s
import networkx as nx
from law_compiler import Network,compile_law,unrooted_law
from source_census import census,displayed,admitted
from verify import TRIANGLE,DIAMOND,PAIR,SPLITS,add_bigon

def decode(natural,marker):
 assert set(natural)==set(marker)
 top=max(marker,key=marker.get)
 assert all(marker[top]>v for t,v in marker.items() if t!=top)
 keys=tuple(natural)
 candidates=[]
 for t in keys:
  other=[natural[u] for u in keys if u!=t]
  if other[0]==other[1]: candidates.append(frozenset((t,)))
 for absent in keys:
  keep=frozenset(t for t in keys if t!=absent)
  if all(natural[t]>natural[absent] for t in keep): candidates.append(keep)
 selected=[q for q in candidates if top in q]
 assert len(selected)==1, (natural,marker,candidates)
 return selected[0]

def pattern(law):
 vals=sorted(law.values())
 if vals[0]==vals[2]: return 'uniform'
 if vals[0]==vals[1]: return 'unique-maximum_equal-minors'
 if vals[1]==vals[2]: return 'unique-minimum_equal-majors'
 return 'three-distinct'

n=checks=laws=0; pats=Counter()
for net in census(4,1):
 n+=1; expected=set(displayed(net).values()); hs=net.structure()[3]
 vals={i:s.Rational(i+4,i+7) for i in range(len(net.edges))}; gs={h:s.Rational(2,5) for h in hs}
 marker=unrooted_law(compile_law(net,'independent',{h:0 for h in hs},edge_values=vals)); laws+=1
 for mode in ('independent','common'):
  nat=unrooted_law(compile_law(net,mode,edge_values=vals,inheritance_values=gs)); laws+=1
  assert decode(nat,marker)==expected
  pats[pattern(nat)]+=1; checks+=1

# Exact source-critical anomalous, uniform and pair-collision controls.
fixtures=0
for r in range(1,7):
 for kind in ('triangle-anomalous','triangle-uniform','diamond-pair'):
  base=DIAMOND if kind=='diamond-pair' else TRIANGLE
  net=base
  leaf='B' if kind=='diamond-pair' else 'D'
  for k in range(r-1): net=add_bigon(net,leaf,k)
  assert admitted(net)
  vals={i:s.Rational(4,5) for i in range(len(net.edges))}
  if kind=='diamond-pair':
   for e in (('U','V'),('U','W')): vals[net.edges.index(e)]=s.Rational(177,200)
  else:
   for e in (('H','W'),('U','H'),('V','H')): vals[net.edges.index(e)]=s.Rational(9,10)
   vals[net.edges.index(('U','V'))]=s.Rational(16,45) if kind=='triangle-uniform' else s.Rational(1,10)
  hs=net.structure()[3]; gs={h:s.Rational(1,2) for h in hs}
  nat=unrooted_law(compile_law(net,'independent',edge_values=vals,inheritance_values=gs))
  marker=unrooted_law(compile_law(net,'independent',{h:0 for h in hs},edge_values=vals))
  assert decode(nat,marker)==set(displayed(net).values()); laws+=2; fixtures+=1
  pats[pattern(nat)]+=1
  if kind=='triangle-uniform': assert len(set(nat.values()))==1
  else: assert [nat[t] for t in SPLITS]==[s.Rational(59,200),s.Rational(141,400),s.Rational(141,400)]

res={'status':'PASS','contract':'promised-source exact unrooted one-copy quartet laws; natural independent/common row + one all-zero fully forced original-ID marker; labels retained; no finite-data claim',
 'complete_one_hybrid_graphs':n,'both_mechanism_census_decoder_checks':checks,'padded_exact_critical_fixtures':fixtures,'exact_law_compilations':laws,'natural_patterns':dict(pats),
 'sharp_independent_or_unknown_mode_unrestricted_labelled_costs':{'sites': 'r','configurations':2,'programs':1},
 'common_only_passive_branch':'one natural row, zero actuated sites already suffices; two-row decoder valid but not optimal',
 'versions':{'python':sys.version.split()[0],'sympy':s.__version__,'networkx':nx.__version__},
 'limits':'All-r/all-level proof depends on original-source singleton equality and strict two-support minimum, independently hand reviewed; numeric cases are not a general proof. No simultaneous cap b<r, erased-label programme minimum, full resource Pareto, DNA or Lean claim.'}
Path(__file__).with_name('natural-marker-results.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
