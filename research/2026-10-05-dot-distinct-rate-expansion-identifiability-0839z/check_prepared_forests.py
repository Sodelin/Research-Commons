#!/usr/bin/env python3
"""Exact lawful triplet-history density and response-separation controls."""
from fractions import Fraction as Q
from itertools import product
from math import comb, prod
from pathlib import Path
import json
import sympy as s
oldrates=[1,2,4]  # Commensurate but pairwise distinct: total-rate resonance allowed.
first=[Q(1,3),Q(2,3)]
midrates=[1,3]
mid=[[Q(1,2),Q(1,3),Q(1,6)],[Q(1,4),Q(1,4),Q(1,2)]]
G=[[Q(1,2),Q(1,4),Q(1,8),Q(1,8)],
   [Q(1,8),Q(1,8),Q(1,4),Q(1,2)]]
G.append([(a+b)/2 for a,b in zip(G[0],G[1])])
newrates=[1,2,3,5]
assert s.Matrix(G).rank()==2 and len(G[0])>len(G)
assert all(sum(row)==1 and min(row)>0 for row in G+mid)

def past_weight(b):
    # No mergers through initial epoch (rate2,length log2), 1->2 pulse,
    # length-log2 epoch at rates1,3, then 2->3 pulse. Survival COUPLES routes.
    target=tuple(a for a in b for _ in range(3));n=len(target)
    total=Q(0)
    for zs in product((0,1),repeat=n):
        weight=prod(first[z] for z in zs)
        weight*=Q(2)**(-sum(comb(zs.count(p),2)*midrates[p] for p in (0,1)))
        weight*=prod(mid[z][a] for z,a in zip(zs,target))
        total+=weight
    return Q(2)**(-2*comb(n,2))*total

def exits_and_drops(b):
    blocks=[[a]*3 for a in b]
    def C():
        allp=[p for group in blocks for p in group]
        return sum(comb(allp.count(p),2)*oldrates[p] for p in range(3))
    Cs=[C()]
    for i,a in enumerate(b):
        blocks[i]=[a]*2;Cs.append(C())
        blocks[i]=[a];Cs.append(C())
    drops=tuple(Cs[k]-Cs[k+1] for k in range(2*len(b)))
    assert tuple(drops[2*i]-drops[2*i+1] for i in range(len(b)))==tuple(oldrates[a] for a in b)
    return Cs,drops

def complete(m,r):
    if m==1:return Q(1)
    lambdas=[comb(k,2)*r for k in range(2,m+1)]
    return 1-sum(prod(Q(z,z-y) for z in lambdas if z!=y)*Q(2)**(-y) for y in lambdas)

def response(b):
    return sum(prod(G[i][a] for i in b)*complete(len(b),newrates[a]) for a in range(4))

rows=0;all_density_checks=0;reconstruction_checks=0;positive_weights=0
for m in range(1,4):
    states=list(product(range(3),repeat=m));vectors=[];coeff=[];truth=[]
    for b in states:
        W=past_weight(b);assert W>0;positive_weights+=1
        Cs,q=exits_and_drops(b);vectors.append(q)
        A=W*prod(oldrates[a]**2 for a in b)*Q(2)**(-8*Cs[-1])
        # Merger times log2,2log2,...,2m log2 in a length8log2 known epoch.
        prepared=A*Q(2)**(-sum((i+1)*z for i,z in enumerate(q)))
        direct=W*prod(oldrates[a]**2 for a in b)
        for k in range(2*m):direct*=Q(2)**(-Cs[k])
        direct*=Q(2)**(-(8-2*m)*Cs[-1])
        assert prepared==direct;all_density_checks+=1
        F=response(b);assert 0<=F<=1
        coeff.append(prepared*F);truth.append((prepared,F))
    assert len(set(vectors))==len(states)
    # A short line segment in the legal open time simplex yields a Vandermonde.
    t=2
    while True:
        direction=[t**k for k in range(2*m)]
        lam=[-sum(a*v for a,v in zip(q,direction)) for q in vectors]
        if len(set(lam))==len(lam):break
        t+=1
    B=len(states)
    V=s.Matrix(B,B,lambda k,j:lam[j]**k)
    observed=s.Matrix([sum(c*z**k for c,z in zip(coeff,lam)) for k in range(B)])
    extracted=V.inv()*observed
    for recovered,(amplitude,F) in zip(extracted,truth):
        assert recovered/amplitude==F;reconstruction_checks+=1
    rows+=B

# All pair hazards can match at a disjoint-support expansion while slopes differ.
Split=[[Q(1,2),Q(1,2),0,0],[0,0,Q(1,2),Q(1,2)]]
rnew=[1,3,2,6];rold=[1,2]
assert len(set(rnew))==4
for i in range(2):
    assert sum(Split[i][a]**2*rnew[a] for a in range(4))==rold[i]
    assert -sum(Split[i][a]**2*rnew[a]**2 for a in range(4)) < -rold[i]**2
assert sum(Split[0][a]*Split[1][a]*rnew[a] for a in range(4))==0

result={'status':'PASS','arithmetic':'Fraction plus exact SymPy Vandermonde inversion',
'known_prefix':'1->2->3; no-merger survival couples the hidden routes',
'future_routing_shape':[3,4],'future_routing_rank':2,
'prepared_tuple_positive_weights':positive_weights,
'full_exit_count_slope_gap_and_density_checks':all_density_checks,
'exact_observable_future_response_recoveries':reconstruction_checks,
'old_rates':[1,2,4],
'disjoint_support_expansion_has_matching_hazards_but_distinct_slopes':True,
'copy_bound_formula':'6P+6 per initial population; each preparation uses only 3m total leaves with m<=2P+2',
'limits':'Finite exact controls, not proof of all-model induction, optimal sample/site bound, noisy-data inversion, historical novelty or Lean verification.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('CONTROL-RESULTS.json').write_text(text);print(text,end='')
