#!/usr/bin/env python3
"""Exact finite checks of the event-anchoring corollary, not statistical fitting."""
from fractions import Fraction as Q
from itertools import permutations
from pathlib import Path
import json

def eye(p):return [[Q(i==j) for j in range(p)] for i in range(p)]
def pulse(p,recipient,donor,g):
    M=eye(p);M[recipient][recipient]=1-g;M[recipient][donor]=g;return M

def perm_columns(M,perm):
    out=[[Q(0)]*len(perm) for _ in M]
    for i,row in enumerate(M):
        for j,v in enumerate(row):out[i][perm[j]]=v
    return out

def decode(M,ids):
    p=len(M);q=len(M[0]);assert len(ids)==p
    assert all(sum(row)==1 and all(x>=0 for x in row) for row in M)
    supports=[[j for j,x in enumerate(row) if x] for row in M]
    assert all(any(M[i][j] for i in range(p)) for j in range(q)),'Unused output column'
    mixed=[i for i,s in enumerate(supports) if len(s)>1]
    if p==q and len(mixed)==1:
        i=mixed[0];assert len(supports[i])==2
        anchored={}
        for a in range(p):
            if a!=i:
                assert len(supports[a])==1 and M[a][supports[a][0]]==1
                c=supports[a][0];assert c not in anchored;anchored[c]=ids[a]
        unassigned=set(range(q))-set(anchored);assert len(unassigned)==1
        own=unassigned.pop();assert own in supports[i] and M[i][own]>0
        donor_col=next(c for c in supports[i] if c!=own)
        donor=anchored[donor_col];g=M[i][donor_col];assert 0<g<1
        anchored[own]=ids[i]
        return {'type':'pulse','recipient':ids[i],'donor':donor,'gamma':g,'column_ids':anchored}
    if not mixed and q<p:
        groups={j:tuple(ids[i] for i in range(p) if M[i][j]==1) for j in range(q)}
        assert all(groups.values())
        column_ids={j:(g[0] if len(g)==1 else ('join@current',g)) for j,g in groups.items()}
        return {'type':'join','groups':groups,'column_ids':column_ids}
    if not mixed and p==q:
        anchored={supports[i][0]:ids[i] for i in range(p)}
        assert len(anchored)==p
        return {'type':'permutation','column_ids':anchored}
    raise ValueError('Not in the declared single-event alphabet')

def partitions(n):
    def go(a,maximum):
        if len(a)==n:yield a;return
        for k in range(maximum+2):yield from go(a+[k],max(k,maximum))
    if n:yield from go([0],0)

pulse_checks=0;join_checks=0;permutation_checks=0
for p in range(2,6):
    # These labels deliberately include a prior join ID; they are formal
    # population histories, not assertions about disjoint genetic ancestry.
    ids=tuple(['join@old(A,B)']+[f'population_{i}' for i in range(1,p)])
    for recipient in range(p):
        for donor in range(p):
            if recipient==donor:continue
            for g in [Q(1,4),Q(1,2),Q(3,4)]:
                original=pulse(p,recipient,donor,g)
                for perm in permutations(range(p)):
                    dec=decode(perm_columns(original,perm),ids)
                    assert (dec['type'],dec['recipient'],dec['donor'],dec['gamma'])==('pulse',ids[recipient],ids[donor],g)
                    assert all(dec['column_ids'][perm[i]]==ids[i] for i in range(p))
                    pulse_checks+=1
    for assignment in partitions(p):
        q=max(assignment)+1
        if q==p:continue
        M=[[Q(assignment[i]==j) for j in range(q)] for i in range(p)]
        target={frozenset(ids[i] for i in range(p) if assignment[i]==j) for j in range(q)}
        for perm in permutations(range(q)):
            dec=decode(perm_columns(M,perm),ids)
            assert dec['type']=='join'
            assert {frozenset(g) for g in dec['groups'].values()}==target
            for col,group in dec['groups'].items():
                if len(group)==1:assert dec['column_ids'][col]==group[0]
                else:assert dec['column_ids'][col]==('join@current',group)
            join_checks+=1
    for perm in permutations(range(p)):
        dec=decode(perm_columns(eye(p),perm),ids)
        assert dec['type']=='permutation'
        assert all(dec['column_ids'][perm[i]]==ids[i] for i in range(p))
        permutation_checks+=1

ids=('A','B')
assert decode(pulse(2,0,1,Q(0)),ids)['type']=='permutation'
try:decode(pulse(2,0,1,Q(1)),ids)
except AssertionError:pass
else:raise AssertionError('Rank-collapsed endpoint incorrectly admitted')
try:decode([[Q(3,4),Q(1,4)],[Q(1,3),Q(2,3)]],ids)
except ValueError:pass
else:raise AssertionError('Bidirectional event incorrectly declared anchored')

def mm(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
# Distinct contemporaneous pulse factorizations: this is excluded by the
# separate-time assumption, not distinguished by the reconstruction.
A=mm(pulse(2,0,1,Q(1,2)),pulse(2,0,1,Q(1,2)))
B=mm(pulse(2,0,1,Q(1,4)),pulse(2,0,1,Q(2,3)))
assert A==B==pulse(2,0,1,Q(3,4))

result={'status':'PASS','arithmetic':'Integer/Fraction only','pulse_permutation_checks':pulse_checks,
        'join_group_permutation_checks':join_checks,'pure_continuation_permutation_checks':permutation_checks,
        'gamma_zero_not_called_pulse':True,'gamma_one_rank_collapse_rejected':True,
        'bidirectional_event_excluded_from_anchoring_alphabet':True,
        'simultaneous_factorization_ambiguity_preserved':True,
        'limits':'Finite exact checks of anchoring logic; provider supplies law identification. No noisy-data inversion, all-network uniqueness, finite-loci confidence or Lean verification.'}
Path(__file__).with_name('ANCHOR-CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
