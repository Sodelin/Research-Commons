#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import product
import json
states=list(product(range(2),repeat=2))
characters=[(1,0),(0,1),(1,1)]
def chi(x,a):return (-1)**sum(v*w for v,w in zip(x,a))
def trans(root,leaf,q):return (1+3*q)/4 if root==leaf else (1-q)/4
checks=0
for q in (F(0),F(1,4),F(1,2),F(3,4),F(1)):
    for a in characters:
        val=sum(F(1,4)*trans(root,x,q)*trans(root,y,q)*chi(x,a)*chi(y,a)
                for root,x,y in product(states,repeat=3))
        assert val==q*q
        for k in range(1,56):
            mean=(1+val**k)/2
            assert F(1,2)<=mean<=1
            checks+=1
# The same genealogy is shared across sites: mix after taking conditional powers.
weights=(F(1,3),F(2,3));qs=(F(1,4),F(3,4))
m1=sum(w*q*q for w,q in zip(weights,qs))
m2=sum(w*q**4 for w,q in zip(weights,qs))
assert m2!=m1*m1
cov=m1*(1-m2)/4
assert cov>0
# Concrete schema and simple parity implementation for all 330 observables.
labels=['A1','A2','B1','B2','C1','C2']
pairs=[('A1','A2'),('B1','B2'),('C1','C2'),('A1','B1'),('B1','C1'),('A1','C1')]
seq={lab:''.join('ACGT'[(i+j)%4] for j in range(55)) for i,lab in enumerate(labels)}
sign={'A':1,'C':1,'G':-1,'T':-1};features=[]
for x,y in pairs:
    running=1
    for k in range(55):
        running*=sign[seq[x][k]]*sign[seq[y][k]]
        parity=sum(sign[seq[x][j]]!=sign[seq[y][j]] for j in range(k+1))%2
        value=(1+running)//2
        assert value==int(parity==0)
        features.append(value)
assert len(features)==330 and set(features)<={0,1}
print(json.dumps({'status':'PASS','character_site_checks':checks,'feature_count':len(features),'mixture_first_moment':str(m1),'mixture_second_moment':str(m2),'independent_mean_square_rejected':str(m1*m1),'within_locus_covariance':str(cov)},sort_keys=True,indent=2))
