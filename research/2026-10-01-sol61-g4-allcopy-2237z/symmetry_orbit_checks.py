#!/usr/bin/env python3
"""Exact orbit counts, selected-leaf pruning and source projectivity controls."""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json,sys
import sympy as S
import obstruction_checks as F
import known_placement_six_checks as K

def leaves(t):
    return (t,) if isinstance(t,str) else leaves(t[0])+leaves(t[1])
def remove(t,label):
    if isinstance(t,str):return None if t==label else t
    a=remove(t[0],label);b=remove(t[1],label)
    if a is None:return b
    if b is None:return a
    return F.join(a,b)
def prune(f,label):return F.canonical(t for root in f if (t:=remove(root,label)) is not None)

def run():
    output=[]
    for n in range(1,7):
        forests=[f for d in F.merger_forests(tuple(f'A{i}' for i in range(1,n+1))).values() for f in d]
        sizes=Counter(K.orbit(f) for f in forests);reps={K.orbit(f):f for f in forests}
        labels=sorted(sizes,key=lambda o:(-len(o),repr(o)))
        row={'input_roots':n,'labelled_forests':len(forests),'shape_orbits':len(sizes),
             'orbits':[{'shape':repr(o),'size':sizes[o]} for o in labels]}
        if n>1:
            lower=[f for d in F.merger_forests(tuple(f'A{i}' for i in range(1,n))).values() for f in d]
            lower_sizes=Counter(K.orbit(f) for f in lower)
            transition={}
            for o in labels:
                f=reps[o];counts=Counter(K.orbit(prune(f,leaf)) for t in f for leaf in leaves(t))
                assert sum(counts.values())==n
                transition[o]={p:S.Rational(c,n) for p,c in counts.items()}
                assert sum(transition[o].values())==1
            for p in lower_sizes:
                for kernel in [K.bare,lambda o:K.edge_forest(o,K.x)]:
                    marginal=sum(sizes[o]*kernel(o)*transition[o].get(p,0) for o in labels)
                    target=lower_sizes[p]*kernel(p)
                    assert S.expand(marginal-target)==0
            # Independent combinatorial labelled restriction control at every orbit.
            direct={o:Counter() for o in labels}
            for f in forests:direct[K.orbit(f)][K.orbit(prune(f,'A1'))]+=1
            for o in labels:
                for p in lower_sizes:
                    assert Fraction(direct[o][p],sizes[o])==Fraction(transition[o].get(p,0))
            row['prune_one_transition']={repr(o):{repr(p):str(c) for p,c in transition[o].items()} for o in labels}
            row['exact_projectivity']='PASS: symbolic ordinary and independent bare kernels; labelled selected-A1 and uniform-leaf shape restriction agree'
        output.append(row)
    assert [r['labelled_forests'] for r in output]==[1,2,7,37,266,2431]
    assert [r['shape_orbits'] for r in output]==[1,2,3,6,10,20]
    return {'status':'PASS','python':sys.version,'sympy':S.__version__,
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependencies_sha256':{Path(p).name:sha256(Path(p).read_bytes()).hexdigest() for p in [F.__file__,K.__file__]},
        'caps':output,'six_root_scalar_coordinates_after_normalization':19,
        'limits':['Projectivity under arbitrary serial private source composition and opaque subtree grafting is a separate source argument.',
                  'No minimal physical tester count or admitted-source affine dimension is claimed.',
                  'Colored multiport and external shared-register kernels need separate joint orbit quotients.']}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
