#!/usr/bin/env python3
"""Full labelled-forest tomography from positive rooted-topology completions.

Independent finite implementation controls for the accompanying hand proof.
No hidden state is treated as a physical observation: observations are the
probabilities of specified complete rooted topologies after pruning C,D.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import comb, prod
from pathlib import Path
import json
import verify

# A leaf is a string and an unordered binary tree is a canonical tuple.
def join(a, b):
    return tuple(sorted((a,b), key=repr))


def canonical(roots):
    return tuple(sorted(roots, key=repr))


def initial(k):
    return tuple(f'A{i}' for i in range(1,k+1))


@lru_cache(maxsize=None)
def skeletons(forest):
    """All merger forests, with probabilities conditional on root count."""
    levels = {len(forest):{forest:Q(1)}}
    for r in range(len(forest),1,-1):
        new = defaultdict(Q)
        for state, probability in levels[r].items():
            for i,j in combinations(range(r),2):
                target = canonical([state[l] for l in range(r) if l not in (i,j)]
                                   + [join(state[i],state[j])])
                new[target] += probability/Q(comb(r,2))
        levels[r-1] = dict(new)
    return levels


@lru_cache(maxsize=None)
def edge(forest,z):
    if not forest:
        return {():Q(1)}
    k=len(forest)
    return {state:verify.p(k,r,z)*prob
            for r,states in skeletons(forest).items() for state,prob in states.items()}


@lru_cache(maxsize=None)
def bigon(forest,x,y,g):
    k=len(forest); result=defaultdict(Q)
    for bits in range(1<<k):
        left=canonical(forest[i] for i in range(k) if bits & (1<<i))
        right=canonical(forest[i] for i in range(k) if not bits & (1<<i))
        weight=g**len(left)*(1-g)**len(right)
        for f,pf in edge(left,x).items():
            for h,ph in edge(right,y).items():
                result[canonical(f+h)] += weight*pf*ph
    return dict(result)


def push(distribution, kernel):
    out=defaultdict(Q)
    for state,prob in distribution.items():
        for target,weight in kernel(state).items():
            out[target] += prob*weight
    return dict(out)


def spine(forest):
    t='B'
    for root in forest:
        t=join(t,root)
    return t


def nodes(tree):
    result={tree}
    if isinstance(tree,tuple):
        result |= nodes(tree[0]) | nodes(tree[1])
    return result


def history_count(tree):
    if isinstance(tree,str):
        return 0,1
    i,hi=history_count(tree[0]); j,hj=history_count(tree[1])
    return i+j+1,comb(i+j,i)*hi*hj


@lru_cache(maxsize=None)
def completion_probability(tree,forest):
    """Kingman probability of tree from the given A forest plus one B root."""
    if not all(root in nodes(tree) for root in forest):
        return Q(0)
    replace={root:f'R{i}' for i,root in enumerate(forest)}
    def contract(t):
        if t in replace:
            return replace[t]
        if t=='B':
            return t
        if isinstance(t,str):
            raise AssertionError('An input component did not cover an A leaf.')
        return join(contract(t[0]),contract(t[1]))
    reduced=contract(tree)
    internal,h=history_count(reduced)
    assert internal == len(forest)
    return Q(h,prod(comb(j,2) for j in range(2,len(forest)+2)))


def upper_solve(matrix,rhs):
    n=len(rhs)
    assert all(matrix[i][j] == 0 for i in range(n) for j in range(i))
    out=[Q(0)]*n
    for i in range(n-1,-1,-1):
        assert matrix[i][i] != 0
        out[i]=(rhs[i]-sum((matrix[i][j]*out[j] for j in range(i+1,n)),Q(0)))/matrix[i][i]
    return out


def graft(tree, replacements):
    if isinstance(tree,str):
        return replacements[tree]
    return join(graft(tree[0],replacements),graft(tree[1],replacements))


def substituted_kernel(forest, recovered):
    k=len(forest)
    repl={f'A{i+1}':root for i,root in enumerate(forest)}
    return {canonical(graft(root,repl) for root in target):weight
            for target,weight in recovered[k].items()}


def run():
    theta=(Q(1,2),Q(3,4),Q(1,3)); z=Q(1,3);u=Q(1,2)
    recovered={};counts=[]; raw_observations=[]
    for k in range(1,5):
        states=sorted([s for level in skeletons(initial(k)).values() for s in level],
                      key=lambda f:(len(f),repr(f)))
        observation=[[completion_probability(spine(f),g) for g in states] for f in states]
        for i,f in enumerate(states):
            assert observation[i][i] == Q(1,prod(comb(j,2) for j in range(2,len(f)+2)))
        direct_b=bigon(initial(k),*theta)
        before_trailing=push(edge(initial(k),z),lambda f:bigon(f,*theta))
        padded=push(before_trailing,lambda f:edge(f,u))
        readings=[sum((observation[i][j]*padded.get(g,Q(0))
                       for j,g in enumerate(states)),Q(0)) for i in range(len(states))]
        assert all(0<=v<=1 for v in readings)
        after_observation_inverse=upper_solve(observation,readings)
        assert after_observation_inverse == [padded.get(f,Q(0)) for f in states]
        trailing=[[edge(g,u).get(f,Q(0)) for g in states] for f in states]
        after_trailing_inverse=upper_solve(trailing,after_observation_inverse)
        assert after_trailing_inverse == [before_trailing.get(f,Q(0)) for f in states]
        earlier=defaultdict(Q)
        for intermediate,weight in edge(initial(k),z).items():
            if len(intermediate)==k:
                continue
            for target,k_weight in substituted_kernel(intermediate,recovered).items():
                earlier[target] += weight*k_weight
        recovered[k]={f:(value-earlier[f])/z**verify.lam(k)
                      for f,value in zip(states,after_trailing_inverse)}
        assert all(recovered[k][f] == direct_b.get(f,Q(0)) for f in states)
        assert sum(recovered[k].values()) == 1
        counts.append({'input_roots':k,'labelled_forests':len(states),
                       'physical_topology_probabilities':len(readings),
                       'total_four_taxon_copies':k+3})
        raw_observations.append({'input_roots':k,'readings':[str(v) for v in readings]})
    here=Path(__file__)
    return {'status':'PASS','arithmetic':'exact fractions.Fraction',
            'source_sha256':sha256(here.read_bytes()).hexdigest(),
            'verify_dependency_sha256':sha256((here.parent/'verify.py').read_bytes()).hexdigest(),
            'scope':'one bare bigon, positive fixed padding, full labelled forest recovery through four inputs',
            'counts':counts,'recovered_coordinates':sum(c['labelled_forests'] for c in counts),
            'observations':raw_observations,
            'limits':['Universal tomography is a hand proof, not inferred from these finite ranks.',
                      'No all-copy equality stopping rule for arbitrary chains is implemented.',
                      'Output probabilities are exact model calculations, not empirical observations.']}


if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
