#!/usr/bin/env python3
"""Exact controls for the stated bounds and an actual two-tip JC modulus."""
from fractions import Fraction as F
from itertools import product
from math import comb
import json
rare=0
for n in range(1,13):
    for q in (F(1,100),F(1,17),F(1,5),F(1,3)):
        tail=1-(1-q)**n-n*q*(1-q)**(n-1)
        assert 0<=tail<=comb(n,2)*q*q
        rare+=1
root=0
for n in range(2,20):
    for lo,hi in ((F(1),F(2)),(F(3,2),F(8,5)),(F(7,3),F(15,4))):
        exact_bad=1-(lo/hi)**(n-1)
        assert exact_bad<=(n-1)*(hi-lo)/lo
        root+=1
windows=0
for J in range(1,5):
    for x in product((F(1,2),F(1),F(3,2)),repeat=J):
        y=tuple(reversed(x)); tx=[];ty=[];a=b=F(0)
        for dx,dy in zip(x,y):a+=dx;b+=dy;tx.append(a);ty.append(b)
        d=max(abs(u-v) for u,v in zip(x,y))
        intervals=sorted((min(a,b),max(a,b)) for a,b in zip(tx,ty))
        union=F(0);left=right=None
        for a,b in intervals:
            if left is None:left,right=a,b
            elif a>right:union+=right-left;left,right=a,b
            else:right=max(right,b)
        union+=right-left
        assert union<=sum(abs(a-b) for a,b in zip(tx,ty))<=F(J*(J+1),2)*d
        # Outside moved-boundary windows, both sources have applied exactly the
        # same number of ordered routing operators, even when windows overlap.
        endpoints=sorted(set([F(0)]+tx+ty+[max(tx+ty)+1]))
        for a,b in zip(endpoints,endpoints[1:]):
            t=(a+b)/2
            if not any(u<=t<=v for u,v in intervals):
                assert sum(s<t for s in tx)==sum(s<t for s in ty)
        windows+=1

# Actual source: two sampled lineages in one root population, rate r in[1,2].
# One stationary clock-JC site has four diagonal probabilities (1+3q)/16 and
# twelve off-diagonal probabilities (1-q)/16, q=r/(r+8/3).
def p(r):
    q=r/(r+F(8,3))
    ans=[(1+3*q)/16]*4+[(1-q)/16]*12
    assert sum(ans)==1 and min(ans)>0
    return ans
# Pair-cell search at resolution epsilon=1/4. Symmetry permits r' >= r.
mesh=512; eps=F(1,4); minimum=None; cells=0
for i in range(mesh):
    lo=1+F(i,mesh)
    for j in range(i,mesh):
        blo=1+F(j,mesh);bhi=1+F(j+1,mesh)
        if bhi-lo<eps:continue
        other=max(blo,lo+eps)
        assert blo<=other<=bhi and other-lo>=eps
        f=max(abs(a-b) for a,b in zip(p(lo),p(other)))
        minimum=f if minimum is None else min(minimum,f);cells+=1
# The proof's generic full-timed-law constant is K=1 at n2/J0/r_min1.
lower=minimum-F(2,mesh)
assert lower>0
# Independent analytic minimum on this exact pair domain.
exact_min=F(9,1484)
assert lower<=exact_min<=minimum
# Forward full timed-TV bound implies this coordinate bound; test all grid pairs.
for i in range(21):
    a=1+F(i,20)
    for j in range(21):
        b=1+F(j,20)
        assert max(abs(x-y) for x,y in zip(p(a),p(b)))<=abs(a-b)
# Computable release comparisons: actual source witnesses plus rounded rational
# simplex proxies. Account for rounding separately, including exact thresholds.
def rational_simplex(v,den):
    nums=[(x.numerator*den)//x.denominator for x in v]
    left=den-sum(nums)
    assert 0<=left<len(nums)
    for k in range(left):nums[k]+=1
    q=[F(x,den) for x in nums]
    assert sum(q)==1 and max(abs(a-b) for a,b in zip(q,v))<=F(1,den)
    return q
Delta=lower
# Outward-safe denominator makes evaluation error at most Delta/16.
den=(16*Delta.denominator)//Delta.numerator+1
truth=F(5,3); witness=truth+Delta/32
pw,pt=p(witness),p(truth)
proxy=rational_simplex(pw,den)
assert max(abs(a-b) for a,b in zip(proxy,pw))<=Delta/16
empirical=pt[:];empirical[0]+=Delta/8;empirical[-1]-=Delta/8
assert sum(empirical)==1 and min(empirical)>=0
computed=max(abs(a-b) for a,b in zip(proxy,empirical))
assert computed<=Delta/4
assert max(abs(a-b) for a,b in zip(pw,pt))<=7*Delta/16
assert F(1,16)+F(1,4)+F(1,8)==F(7,16)
assert F(7,16)+F(1,16)==F(1,2)<1
print(json.dumps({'status':'PASS','rare_route_bounds':rare,'root_clock_bounds':root,'boundary_window_cases':windows,'actual_JC_feasible_pair_cells':cells,'mesh':mesh,'generic_K':1,'certified_inverse_lower':str(lower),'analytic_inverse_minimum':str(exact_min),'forward_JC_pair_checks':441,'rational_cloud_denominator':den,'rational_threshold_test':'PASS','witness_error_fraction':'7/16','cell_error_fraction':'1/2'},sort_keys=True,indent=2))
