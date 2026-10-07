"""Test-only direct labelled-history oracle, independently from token grafting.

Adapted from Sol's obstruction_checks.py and placement_checks.py. Enumerates
mergers directly on attached historical trees. Shares the classical Kingman
pure-death identity, but does not call the production forest compiler.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from math import comb,prod
from functools import lru_cache


def canonical(f):return tuple(sorted(f,key=repr))
def join(a,b):return tuple(sorted((a,b),key=repr))

@lru_cache(None)
def histories(start):
    levels={len(start):{start:Q(1)}}
    for r in range(len(start),1,-1):
        out=defaultdict(Q)
        for f,p in levels[r].items():
            for i,j in combinations(range(r),2):
                after=canonical([f[k] for k in range(r) if k not in (i,j)]+[join(f[i],f[j])])
                out[after]+=p/Q(comb(r,2))
        levels[r-1]=dict(out)
    return levels


def death(k,r,x):
    if k==0:return Q(r==0)
    lam=lambda n:comb(n,2)
    numerator=prod(lam(j) for j in range(r+1,k+1))
    return numerator*sum((x**lam(j)/prod(lam(h)-lam(j) for h in range(r,k+1) if h!=j) for j in range(r,k+1)),Q(0))

@lru_cache(None)
def edge(start,x):
    if not start:return {():Q(1)}
    return {f:p*death(len(start),r,x) for r,d in histories(start).items() for f,p in d.items()}

@lru_cache(None)
def hybrid(start,x,y,g):
    out=defaultdict(Q)
    for bits in product((0,1),repeat=len(start)):
        left=canonical(start[i] for i,b in enumerate(bits) if b==0)
        right=canonical(start[i] for i,b in enumerate(bits) if b==1)
        weight=g**len(left)*(1-g)**len(right)
        for a,p in edge(left,x).items():
            for b,q in edge(right,y).items():out[canonical(a+b)]+=weight*p*q
    return dict(out)


def push(dist,op):
    out=defaultdict(Q)
    for f,p in dist.items():
        for h,q in op(f).items():out[h]+=p*q
    return dict(out)


def complete(parameters,n):
    a,x,y,g,b=parameters
    d=edge(canonical(f'copy{i}' for i in range(n)),a)
    d=push(d,lambda f:hybrid(f,x,y,g))
    return push(d,lambda f:edge(f,b))
