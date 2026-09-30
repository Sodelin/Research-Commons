"""Independent source-graph replay of reported normalized mechanism; no theorem-priority claim."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations,permutations
from math import prod
import json
from inputs import exact_networks as ex
from sunlet_fixture import sunlet

ROOT=Path(__file__).parent

def all_orders(labels):
    first,*rest=sorted(labels)
    for tail in permutations(rest):
        if tail[0]<tail[-1]:
            yield (first,)+tail

def distance(qs,labels,c,s,a,o):
    d={(x,x):F(0) for x in labels}
    for x,y in combinations(labels,2):
        value=F(2*len(labels)-4)
        for z,w in combinations([v for v in labels if v not in (x,y)],2):
            splits=qs[tuple(sorted((x,y,z,w)))]
            separated=sum((x in side)!=(y in side) for side in splits)
            score=(s if separated else c) if len(splits)==1 else (a if separated==1 else o)
            value+=2*score
        d[x,y]=d[y,x]=value
    return d

def check_identity(qs,labels,c,s,a):
    beta=s-c
    actual=distance(qs,labels,c,s,a,s)
    base=2*len(labels)-4;K=(len(labels)-1)*(len(labels)-2)
    residual=c*K+(1-s)*base
    if beta:
        b=(a-c)/beta
        normalized=distance(qs,labels,0,1,b,1)
        for x,y in actual:
            assert actual[x,y]==(residual+beta*normalized[x,y] if x!=y else 0)
    else:
        assert a==s
        for x,y in actual:assert actual[x,y]==(residual if x!=y else 0)
    return {'c':str(c),'s=o':str(s),'a':str(a),'beta':str(beta),'star_residual':str(residual),'diagonal_checked':True}

def main():
    base,leaves=sunlet(7)
    net=ex.cherry_at(base,leaves[0],'hybrid-twins-')
    admission=net.validate();labels=sorted(net.leaves);qs,trees=ex.quartet_system(net)
    x,y='hybrid-twins-x','hybrid-twins-y'
    outsiders=[leaves[1],leaves[3],leaves[6]]
    d=distance(qs,labels,F(1,2),F(1),F(1,2),F(1))
    assert all(d[x,z]==d[y,z] for z in outsiders)
    contrasts=[{'outsiders':[u,v],'value':str(d[x,y]+d[u,v]-d[x,u]-d[y,v])}
               for u,v in combinations(outsiders,2)]
    values=[F(r['value']) for r in contrasts]
    assert values==[F(-11),F(4),F(-7)] and prod(values)>0
    # Nonzero odd-positive contrast pattern violates the two-arc assignment.
    compatible=[];checked=0
    for order in all_orders(labels):
        checked+=1
        if all(d[order[i],order[j]]+d[order[(i+1)%8],order[(j+1)%8]]
               -d[order[i],order[(j+1)%8]]-d[order[(i+1)%8],order[j]]>=0
               for i,j in combinations(range(8),2)):
            compatible.append(order)
    assert checked==2520 and not compatible
    identities=[check_identity(qs,labels,*point) for point in
                [(F(1,2),F(1),F(3,4)),(F(1,2),F(1),F(1,2)),(F(1),F(1),F(1)),
                 (F(0),F(3),F(3,2)),(F(1),F(3),F(2)),(F(3),F(3),F(3))]]
    receipt={'status':'PASS_INDEPENDENT_TWIN_COUNTEREXAMPLE_AND_STAR_IDENTITIES',
             'family':'7-sunlet with hybrid leaf replaced by ordinary binary cherry;8taxa;level1;multiple non-leaf blobs',
             'admission':admission,'displayed_trees':len(set(trees)),'quartets':len(qs),
             'labels':labels,'scores_c_s_a_o':['1/2','1','1/2','1'],
             'matrix':[[str(d[u,v]) for v in labels] for u in labels],
             'twins':[x,y],'outsider_triple':outsiders,'twin_contrasts':contrasts,
             'all_orders_checked':checked,'nonnegative_orders':compatible,
             'star_identity_controls':identities,
             'full_formula':'d(c,s,a,s)=star[c*K_n+(1-s)*(2n-4)]+(s-c)*d(0,1,(a-c)/(s-c),1), on offdiagonal; diagonal0; s=c requires a=c and is purestar',
             'scope':'Independent corroboration of reported mechanism, not full unbounded proof review or Lean certificate.'}
    (ROOT/'twin-normalization-review.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('status','family','twin_contrasts','all_orders_checked','star_identity_controls')},indent=2))

if __name__=='__main__':main()
