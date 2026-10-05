#!/usr/bin/env python3
"""Exact supplementary controls for the bounded pulse-network hand proof.
All computations use integer/Fraction arithmetic; no numerical simulation or fit.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import json

def stirling(n,k):
    a=[[0]*(n+1) for _ in range(n+1)];a[0][0]=1
    for i in range(1,n+1):
        for j in range(1,i+1):a[i][j]=a[i-1][j-1]+j*a[i-1][j]
    return a[n][k]
def bell(n):return sum(stirling(n,k) for k in range(n+1))
def bound(n,J,P):
    S=bell(n)*P**n;b=comb(n,2);E=sum(b**i for i in range(n))
    F=J*S*S+S;M=E*(n*E*S)**J;K=2*M*(2*F+1);L=4**(n-1)*(K-1)
    return {'n':n,'J':J,'P':P,'S':S,'E':E,'F':F,'M':M,'K':K,'L':L}
assert [bell(n) for n in range(9)]==[1,1,2,5,15,52,203,877,4140]
state_bounds=0
for n in range(2,9):
    for P in range(1,5):
        assert sum(stirling(n,k)*P**k for k in range(1,n+1))<=bell(n)*P**n
        state_bounds+=1
primitive=0
for a,b in product(range(4),repeat=2):
    assert int(a!=0)+int(b!=0)-int((a^b)!=0)>=0;primitive+=1

# The decrease in killed rate is positive for every possible pair occupancy
# and all charge losses. Coefficients, not floating-rate choices, certify this.
rate_drops=0
for n in range(2,9):
    for occupancy in range(2,n+1):
        dc=comb(occupancy,2)-comb(occupancy-1,2)
        assert dc==occupancy-1>0
        for charge_loss in range(0,17):
            assert dc*Q(2,7)+Q(4,3)*charge_loss>0;rate_drops+=1

# An equal-rate pair of UNRELATED two-population states is not a directed
# merger pair; the two comparable paths each have strictly falling rates.
r=Q(3,5)
assert comb(2,2)*r+comb(1,2)*r==comb(1,2)*r+comb(2,2)*r
for counts in [((2,2),(1,2),(1,1)),((2,2),(2,1),(1,1))]:
    cs=[sum(comb(j,2)*r for j in ss) for ss in counts]
    assert cs[0]>cs[1]>cs[2]

# Exact partial-fraction/Laplace convolution identity; also zero-duration
# cancellation, which is necessary for padded catalogue schedules.
conv_checks=0;zero_duration_checks=0
for m in range(8):
    ds=[Q(50+3*(m-i),7) for i in range(m+1)]
    coefficients=[]
    for i in range(m+1):
        den=Q(1)
        for j in range(m+1):
            if i!=j:den*=ds[j]-ds[i]
        coefficients.append(1/den)
    if m:
        assert sum(coefficients)==0;zero_duration_checks+=1
    else:assert sum(coefficients)==1
    for z in [Q(0),Q(2,9),Q(11)]:
        left=sum(coefficients[i]/(z+ds[i]) for i in range(m+1))
        right=Q(1)
        for d in ds:right/=z+d
        assert left==right;conv_checks+=1

# Same-rate genealogy under different calendar subdivisions, with identity
# boundary maps: different catalogue descriptions have the same pair moments.
# In dimensionless time x=(8/3)t, use rate a and lengths d*log2.
def pair_chain(a,ds,k):
    ans=Q(a,a+k)
    for d in reversed(ds):
        surv=Q(2)**(-(a+k)*d)
        ans=Q(a,a+k)*(1-surv)+surv*ans
    return ans
catalogue_checks=0
for a in [1,2,5]:
    for ds in [[],[0],[1],[1,2],[0,1,0,2,0],[3,2,1]]:
        for k in range(13):
            assert pair_chain(a,ds,k)==Q(a,a+k);catalogue_checks+=1

# Boundary independent routing is polynomial and remains normalized at the
# endpoints g=0 and g=1 as well as in the interior.
routing_checks=0
for blocks in range(1,7):
    for g in [Q(0),Q(2,7),Q(1)]:
        assert sum(g**sum(bits)*(1-g)**(blocks-sum(bits)) for bits in product((0,1),repeat=blocks))==1
        routing_checks+=1

def pmul(p,q):
    out=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out
# Two count coordinates, including cross terms in the polynomial and
# coincident bases: annihilator coefficients do not depend on other counts.
terms=[(Q(1),Q(1,2)),(Q(2,3),Q(3,5)),(Q(2,3),Q(1))]
def f(a,b):return sum((i+1)*(a+2*b+i+1)**3*x**a*y**b for i,(x,y) in enumerate(terms))
recurrence_checks=0
for coordinate in [0,1]:
    ann=[Q(1)]
    for bases in terms:
        for _ in range(4):ann=pmul(ann,[-bases[coordinate],Q(1)])
    assert ann[-1]==1
    for start in range(4):
        for other in range(4):
            got=sum(c*(f(start+i,other) if coordinate==0 else f(other,start+i)) for i,c in enumerate(ann))
            assert got==0;recurrence_checks+=1

result={'status':'PASS','arithmetic':'Integer and Fraction only','primitive_character_checks':primitive,
        'state_count_bounds':state_bounds,'positive_rate_drop_checks':rate_drops,
        'path_convolution_checks':conv_checks,'zero_duration_path_checks':zero_duration_checks,
        'cross_schedule_pair_moment_checks':catalogue_checks,'routing_normalization_checks':routing_checks,
        'multivariate_recurrence_checks':recurrence_checks,
        'sample_bound_constants':[bound(2,0,1),bound(3,2,3),bound(6,3,5)],
        'limits':'Supplementary finite controls; not an executable arbitrary-network likelihood compiler, a substitute for independent proof review, parameter identification, finite-sample accuracy, or Lean verification.'}
Path(__file__).with_name('CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
