"""Actual bare-cell EPPF residual in the inherited exact 9-to-4 formula.

This is a bounded mathematical source exploration, not an original G4 test.
All arithmetic is exact; no full coefficient grid or hidden profile is used.
"""
from fractions import Fraction as F
from functools import cache
from itertools import product
from math import comb,factorial
import json

def rate(n):return n*(n-1)//2

@cache
def count_transition(n,k,x):
    if n==k:return x**rate(n)
    if n==0 or k==0 or n<k:return F(0)
    numerator=1
    for r in range(k+1,n+1):numerator*=rate(r)
    total=F(0)
    for j in range(k,n+1):
        denom=1
        for r in range(k,n+1):
            if r!=j:denom*=rate(r)-rate(j)
        total+=F(numerator,denom)*x**rate(j)
    return total

@cache
def gibbs(n,k,x):
    if n==k==0:return F(1)
    if n==0 or k==0 or n<k:return F(0)
    return count_transition(n,k,x)*F(factorial(k),factorial(n)*comb(n-1,k-1))

def partition_probability(blocks,p,x,y):
    q=1-p;n=sum(blocks);total=F(0)
    prefactor=1
    for v in blocks:prefactor*=factorial(v)
    for allocation in product((0,1),repeat=len(blocks)):
        na=sum(v for v,c in zip(blocks,allocation) if c==0)
        ka=allocation.count(0);nb=n-na;kb=len(blocks)-ka
        total+=p**na*q**nb*gibbs(na,ka,x)*gibbs(nb,kb,y)
    return prefactor*total

def residual(p,x,y):
    return (2*partition_probability((3,2,1,1),p,x,y)
                -partition_probability((4,1,1,1),p,x,y))/6

if __name__=='__main__':
    for p in (F(0),F(1,4),F(1,3),F(1,2),F(3,4),F(1)):
        assert residual(p,F(0),F(1)) == -p**4*(1-p)**3/6
        for x in (F(0),F(1,4),F(1,2),F(1)):
            assert residual(F(0),x,F(1,2))==0
            assert residual(F(1),F(1,2),x)==0
        for x,y in ((F(1,2),F(1,2)),(F(1,4),F(3,4)),(F(1,2),F(3,4)),(F(1,8),F(7,8))):
            print(json.dumps({'p':str(p),'x':str(x),'y':str(y),'e_actual_bare_cell':str(residual(p,x,y))}),flush=True)
