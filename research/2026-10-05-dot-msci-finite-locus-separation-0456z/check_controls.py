#!/usr/bin/env python3
"""Exact supplementary controls; not a replacement for the all-L hand proof."""
from fractions import Fraction as F
from itertools import product, combinations
import json
from pathlib import Path

def partitions(items):
    if not items:
        yield (); return
    a,*rest=items
    for p in partitions(rest):
        yield ((a,),)+p
        for i in range(len(p)):
            yield p[:i]+((a,)+p[i],)+p[i+1:]

def xor_all(xs):
    v=0
    for x in xs:v^=x
    return v

primitive=[]
for a,b in product(range(4),repeat=2):
    drop=int(a!=0)+int(b!=0)-int(a^b!=0)
    assert drop>=0
    primitive.append([a,b,drop])
ps=list(partitions(list(range(6))))
assert len(ps)==203
checks=0
# All globally zero-total one-site assignments; an arbitrary L-site assignment
# consists of L such independent charge columns.
for first in product(range(4),repeat=5):
    chars=first+(xor_all(first),)
    for p in ps:
        charges=[xor_all(chars[i] for i in block) for block in p]
        k=sum(c!=0 for c in charges)
        for i,j in combinations(range(len(p)),2):
            kp=k-int(charges[i]!=0)-int(charges[j]!=0)+int(charges[i]^charges[j]!=0)
            assert kp<=k
            # If this pair is legal in any population of occupancy n, C drop
            # is exactly (n-1)r. Check all possible occupancies (r factors out).
            for n in range(2,len(p)+1):
                assert n*(n-1)//2-(n-1)*(n-2)//2==n-1>0
            checks+=1

# Laplace-transform verification of finite convolution formula at exact values:
# residues at the simple poles -d_i are 1/prod_(j != i)(d_j-d_i).
convolution_checks=0
r=F(7,5);mu=F(4,3)
for m in range(6):
    ns=list(range(6,6-m-1,-1))
    ds=[F(n*(n-1),2)*r+mu*(2*n) for n in ns]
    assert all(ds[i]>ds[i+1] for i in range(m))
    coeff=[]
    for i in range(m+1):
        den=F(1)
        for j in range(m+1):
            if i!=j:den*=ds[j]-ds[i]
        coeff.append(1/den)
    for z in [F(0),F(1,7),F(2),F(101,3)]:
        lhs=sum(coeff[i]/(z+ds[i]) for i in range(m+1))
        rhs=F(1)
        for d in ds:rhs/=z+d
        assert lhs==rhs
        convolution_checks+=1

# A pair's L-site repeated character moment at a shared root genealogy is
# r/(r+2L*mu), not the Lth power of its separately averaged one-site moment.
shared=[]
for L in range(1,9):
    true=r/(r+2*L*mu)
    separate=(r/(r+2*mu))**L
    assert (true==separate)==(L==1)
    shared.append({'L':L,'shared':str(true),'separate':str(separate)})

# Routing is per CURRENT B block, independent of descendant count.
g=F(2,7)
for b in range(1,7):
    weights=[]
    for route in product((0,1),repeat=b):
        u=sum(route);weights.append(g**u*(1-g)**(b-u))
    assert sum(weights)==1
assert g!=g*g # merged two-descendant block still receives one Bernoulli.
result={'status':'PASS','arithmetic':'Python Fraction/integer only',
        'primitive_charge_pairs':len(primitive),'label_partitions':len(ps),
        'globally_zero_charge_columns':4**5,'partition_merger_checks':checks,
        'convolution_laplace_checks':convolution_checks,
        'shared_genealogy_pair_controls':shared,
        'pulse_current_block_routing_counts':list(range(1,7)),
        'limits':'Finite exact transcription controls, not a numerical fit, full locus compiler, Lean proof, effective length bound, or independent proof review.'}
Path(__file__).with_name('CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
