"""Finite replay for the inherited anchor inputs and new endpoint deductions.

Exact interval-bitset enumeration of adjacent-copy plane trees on 3..6 labels.
This repeats a known baseline method, not an independent structural proof.
The unbounded source reduction and composition are inherited, not executed here.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json
import sys

ZERO=(0,0,0,0,0)
ROWS={(-1,0,0,0,1),(-1,0,1,0,0),(0,-1,0,1,0),(0,-1,1,0,0),
      (0,0,-1,0,1),(0,0,-1,2,0),(0,0,0,1,0),(0,0,1,-1,0),
      (0,0,1,0,-1),(0,0,1,0,0),(0,1,0,0,0),(1,-1,0,0,0),
      (1,0,-1,0,0),(1,0,0,-1,0),(1,0,0,0,-1),(1,0,0,0,0)}


def systems(n):
    qs=list(combinations(range(n),4)); result=set(); tree_count=0
    for mask in range(1<<n):
        labs=[i for i in range(n) for _ in range(1+((mask>>i)&1))]
        m=len(labs); tree_count+=comb(2*(m-2),m-2)//(m-1)
        edge={}
        for i in range(1,m):
            for j in range(i+1,m+1):
                A=set(labs[i:j]);B=set(labs[:i]+labs[j:]); pattern=0
                for k,(a,b,c,d) in enumerate(qs):
                    for t,(u,v,w,z) in enumerate(((a,b,c,d),(a,c,b,d),(a,d,b,c))):
                        if ({u,v}<=A and {w,z}<=B) or ({u,v}<=B and {w,z}<=A):
                            pattern|=1<<(3*k+t)
                edge[i,j]=pattern
        @lru_cache(None)
        def rec(i,j):
            if j-i==1:return frozenset((0,))
            out=set(); E=edge[i,j]
            for k in range(i+1,j):
                for L in rec(i,k):
                    for R in rec(k,j):out.add(L|R|E)
            return frozenset(out)
        result.update(rec(1,m))
    decoded=[]
    for pattern in sorted(result):
        codes={Q:(pattern>>(3*k))&7 for k,Q in enumerate(qs)}
        assert all(v in (1,4,5) for v in codes.values())
        decoded.append(codes)
    return decoded,tree_count


def cat(x,y,p,q,codes):
    Q=tuple(sorted((x,y,p,q)));code=codes[Q]
    pairs=[Q[:2],(Q[0],Q[2]),(Q[0],Q[3])]
    cherries=sum(((x in pair)==(y in pair)) for t,pair in enumerate(pairs) if code&(1<<t))
    if code in (1,4):return 0 if cherries else 1
    assert code==5 and cherries in (0,1)
    return 2 if cherries else 3


def entry(x,y,p,q,codes):
    if x==y:return ZERO
    count=(x in (p,q))+(y in (p,q))
    if count==2:return ZERO
    if count==1:return (1,0,0,0,0)
    v=[0]*5;v[1+cat(x,y,p,q,codes)]=2
    return tuple(v)


def alpha(n,i,j,p,q,codes):
    a,b,c,d=i,(i+1)%n,j,(j+1)%n
    terms=[entry(a,c,p,q,codes),entry(b,d,p,q,codes),
           entry(a,d,p,q,codes),entry(b,c,p,q,codes)]
    return tuple(t[0]+t[1]-t[2]-t[3] for t in zip(*terms))


def ev(v,b):
    return v[0]+v[2]+F(b)*v[3]+v[4]


def run():
    histogram=Counter(); size_rows=[]; absent_checks=0; present_checks=0
    pendant_checks=0; support_controls=0; all_ones_controls=0
    for n in range(3,7):
        ss,tree_count=systems(n); assert len(ss)=={3:1,4:3,5:16,6:102}[n]
        coefficient_count=0
        for codes in ss:
            anchors=list(combinations(range(n),2))
            for i,j in combinations(range(n),2):
                adjacent=(j==i+1 or (i==0 and j==n-1))
                vv=[alpha(n,i,j,p,q,codes) for p,q in anchors]
                for v in vv:
                    g=gcd(*v);histogram[tuple(x//g for x in v) if g else ZERO]+=1
                    assert ev(v,F(1,2))>=0 and ev(v,1)>=0
                    coefficient_count+=1
                if not adjacent:
                    a,b,c,d=i,(i+1)%n,j,(j+1)%n
                    present=cat(b,c,a,d,codes) in (0,2)
                    for v in vv:
                        assert sum(v)==0;all_ones_controls+=1
                    lam0=sum(ev(v,F(1,2)) for v in vv)/2
                    lam1=sum(ev(v,1) for v in vv)/2
                    assert lam0>=0 and lam1>=0
                    if not present:
                        assert all(ev(v,F(1,2))==ev(v,1)==0 for v in vv)
                        absent_checks+=len(vv)
                    else:
                        assert lam0>=1;present_checks+=1
                    assert (lam0>0)==present
                    assert not lam1>0 or present
                    support_controls+=1
            # Weighted pendant lemma for a finite collection of positive integer masses.
            masses=[[1]*n,[2]*n,list(range(1,n+1)),[1+(i%3)*2 for i in range(n)]]
            masses += [[1 if j==i else 3 for j in range(n)] for i in range(n)]
            for x in range(n):
                y,z=(x-1)%n,(x+1)%n
                kvals=[]
                for p,q in anchors:
                    terms=[entry(y,x,p,q,codes),entry(x,z,p,q,codes),entry(y,z,p,q,codes)]
                    kvals.append(tuple(t[0]+t[1]-t[2] for t in zip(*terms)))
                for bval in (F(1,2),1):
                    kk=[ev(v,bval)/2 for v in kvals]
                    assert kk[anchors.index(tuple(sorted((y,z))))]==1
                    for p in set(range(n))-{x,y,z}:
                        assert kk[anchors.index(tuple(sorted((y,p))))]+kk[anchors.index(tuple(sorted((z,p))))]>=1
                    for m in masses:
                        lam=sum(k*m[p]*m[q] for k,(p,q) in zip(kk,anchors))
                        assert lam>=sum(m)-m[x]-1
                        pendant_checks+=1
        size_rows.append({'labels':n,'duplication_masks':1<<n,'plane_trees_represented':tree_count,
                          'distinct_quartet_systems':len(ss),'anchor_coefficients':coefficient_count})
    assert set(histogram)-{ZERO}==ROWS
    assert sum(histogram.values())==24667
    # The 16 inherited row types imply the new endpoint-absence result algebraically.
    endpoint_zero_rows=[]
    for v in ROWS:
        if sum(v)==0 and ev(v,F(1,2))==0:
            assert ev(v,1)==0
            endpoint_zero_rows.append(v)
    # Exact score-space identity, with no implicit baseline rescaling.
    for c,s,a in ((0,1,F(1,2)),(F(1,3),2,F(5,3)),(2,5,5),(7,7,7),(-3,-1,9)):
        u=2*(s-a);v=2*a-s-c
        Q0=(0,1,F(1,2),1);Q1=(0,1,1,1)
        assert tuple(c+u*x+v*y for x,y in zip(Q0,Q1))==(c,s,a,s)
    return {'status':'PASS_ENDPOINT_AND_PENDANT_CONTROLS','rows_by_size':size_rows,
            'total_anchor_coefficients':sum(histogram.values()),'distinct_nonzero_rows':len(ROWS),
            'identically_zero_anchor_coefficients':histogram[ZERO],
            'nontrivial_all_ones_zero_checks':all_ones_controls,
            'absent_split_anchor_endpoint_zero_checks':absent_checks,
            'present_split_original_margin_checks':present_checks,'nontrivial_split_cases':support_controls,
            'weighted_pendant_checks':pendant_checks,
            'row_histogram': [{'row':list(k),'count':v} for k,v in sorted(histogram.items())],
            'endpoint_zero_row_implications':[list(v) for v in sorted(endpoint_zero_rows)],
            'method':'Exact interval-bitset DP, rational evaluation, positive integer mass tests, symbolic row and score identities.',
            'limits':'Replays known finite paired-tip enumeration method. Does not independently prove source representation, restriction reduction or multiple-blob composition. Finite mass samples corroborate the written arbitrary-positive-integer-mass lemma.'}


if __name__=='__main__':
    report=run();report['python']=sys.version
    report['checker_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_name('ENDPOINT-EVIDENCE.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('row_histogram','endpoint_zero_row_implications')},indent=2))
