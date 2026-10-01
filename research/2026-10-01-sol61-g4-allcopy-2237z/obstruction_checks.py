#!/usr/bin/env python3
"""Exact bounded controls for the G4 standard-q obstruction and mixed zero-test.

A finite screen does not prove non-q-holonomicity or supply a complete G4 stop.
All probabilities use Fraction; no numerical near-equality is accepted.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import json
import sys


def lam(n):
    return comb(n,2)


def no_merger_polynomial(n):
    out=defaultdict(Q)
    for j in range(n+1):
        out[lam(j)+lam(n-j)] += Q(comb(n,j),2**n)
    return dict(out)


def evaluate(p,q):
    return sum((a*q**e for e,a in p.items()),Q(0))


def canonical(forest):
    return tuple(sorted(forest,key=repr))


def join(a,b):
    return tuple(sorted((a,b),key=repr))


@lru_cache(None)
def merger_forests(start):
    k=len(start)
    levels={k:{start:Q(1)}}
    for r in range(k,1,-1):
        target=defaultdict(Q)
        for state,weight in levels[r].items():
            for i,j in combinations(range(r),2):
                f=canonical([state[h] for h in range(r) if h not in (i,j)]
                            +[join(state[i],state[j])])
                target[f]+=weight/Q(comb(r,2))
        levels[r-1]=dict(target)
    return levels


def death(k,r,q):
    if k==0:
        return Q(int(r==0))
    pref=prod(lam(j) for j in range(r+1,k+1))
    return pref*sum((q**lam(j)/prod(lam(h)-lam(j)
                                  for h in range(r,k+1) if h!=j)
                    for j in range(r,k+1)),Q(0))


@lru_cache(None)
def edge(start,q):
    if not start:
        return {():Q(1)}
    k=len(start)
    return {f:weight*death(k,r,q) for r,dist in merger_forests(start).items()
            for f,weight in dist.items()}


def bigon(start,q):
    k=len(start);out=defaultdict(Q)
    for bits in range(2**k):
        left=canonical(start[i] for i in range(k) if bits&(1<<i))
        right=canonical(start[i] for i in range(k) if not bits&(1<<i))
        for f,p in edge(left,q).items():
            for h,w in edge(right,q).items():
                out[canonical(f+h)]+=p*w/Q(2**k)
    return dict(out)


def push(dist,op):
    out=defaultdict(Q)
    for f,p in dist.items():
        for h,w in op(f).items():
            out[h]+=p*w
    return dict(out)


def history_count(t):
    if isinstance(t,str):
        return 0,1
    i,a=history_count(t[0]);j,b=history_count(t[1])
    return i+j+1,comb(i+j,i)*a*b


def all_nodes(t):
    if isinstance(t,str):
        return {t}
    return {t}|all_nodes(t[0])|all_nodes(t[1])


def cherries_comb(n):
    roots=[join(f"A{i}",f"B{i}") for i in range(n)]
    t=roots[0]
    for r in roots[1:]:
        t=join(t,r)
    return t


def topology_probability(t,forest):
    # General current-root contraction, not an assumed hidden readout.
    if not all(r in all_nodes(t) for r in forest):
        return Q(0)
    tokens={root:f"T{i}" for i,root in enumerate(forest)}
    def replace(v):
        if v in tokens:
            return tokens[v]
        assert isinstance(v,tuple)
        return join(replace(v[0]),replace(v[1]))
    contracted=replace(t)
    internal,h=history_count(contracted)
    assert internal==len(forest)-1
    return Q(h,prod(comb(r,2) for r in range(2,len(forest)+1)))


def trim(p):
    p=list(p)
    while p and p[-1]==0:
        p.pop()
    return tuple(p)


def positive_tail_certificate(terms):
    """Rational specialization of the positive-algebraic dominance proof.

    Input: [(positive beta, polynomial coefficients in ascending powers)].
    Output N and explicit dominance bounds; no sampled-zero plateau.
    """
    combined={}
    for beta,p in terms:
        assert beta>0
        old=combined.get(beta,())
        combined[beta]=trim([ (old[i] if i<len(old) else Q(0))
                             +(p[i] if i<len(p) else Q(0))
                             for i in range(max(len(old),len(p)))])
    combined={b:p for b,p in combined.items() if p}
    if not combined:
        return {"identically_zero":True}
    beta=max(combined)
    p=combined[beta];d=len(p)-1
    c=abs(p[-1])/2
    # For n>=1, sum of all lower terms <= sum|p_i| n^(d-1).
    N=max(1,1+int(sum(abs(a) for a in p[:-1])/c))
    smaller=[]
    for b,a in combined.items():
        if b==beta:
            continue
        K=max(len(a)-1-d,0)
        C=sum(abs(v) for v in a)
        rho=b/beta
        # This exact bound makes n^K rho^n decreasing thereafter.
        N=max(N,1+int(Q(K)/(1-rho)))
        smaller.append((C/c,K,rho))
    while sum((C*N**K*rho**N for C,K,rho in smaller),Q(0))>=1:
        N*=2
    assert abs(sum((p[i]*Q(N)**i for i in range(len(p))),Q(0)))>=c*N**d
    return {
        "identically_zero":False,"N":N,"dominant_base":str(beta),
        "dominant_degree":d,"dominant_lower_constant":str(c),
        "remainder_upper_ratio":str(sum((C*N**K*rho**N
                                        for C,K,rho in smaller),Q(0))),
        "smaller_terms":[{"coefficient_bound_ratio":str(C),
                         "polynomial_power":K,"base_ratio":str(rho)}
                        for C,K,rho in smaller]
    }


def run():
    valuation=[]
    for n in range(1,65):
        p=no_merger_polynomial(n)
        v=min(p);m=n//2
        expect_v=m*(m-1) if n%2==0 else m*m
        expect_c=Q(comb(2*m,m),4**m) if n%2==0 else Q(comb(2*m+1,m),4**m)
        assert v==expect_v and p[v]==expect_c
        assert sum(p.values(),Q(0))==1
        if n<=10:
            valuation.append({"n":n,"lowest_q_exponent":v,"coefficient":str(p[v])})
    observed=[]
    for q in (Q(1,3),Q(1,2),Q(2,3)):
        for n in range(1,5):
            A=tuple(f"A{i}" for i in range(n))
            B=tuple(f"B{i}" for i in range(n))
            bare=bigon(A,q)
            K=push(push(edge(A,q),lambda f:bigon(f,q)),lambda f:edge(f,q))
            assert bare[A]==evaluate(no_merger_polynomial(n),q)
            assert K[A]==q**(2*lam(n))*bare[A]
            assert sum(K.values(),Q(0))==1 and all(w>=0 for w in K.values())
            tree=cherries_comb(n)
            internal,h=history_count(tree)
            assert internal==2*n-1
            odd_double_factorial=prod(range(1,2*n,2))
            kappa=Q(2**(2*n-1),factorial(2*n)*odd_double_factorial)
            assert Q(h,prod(comb(j,2) for j in range(2,2*n+1)))==kappa
            response=sum((pa*pb*topology_probability(tree,canonical(fa+fb))
                          for fa,pa in K.items() for fb,pb in edge(B,q).items()),Q(0))
            assert response==kappa*q**(3*lam(n))*bare[A]
            recovered=response/(kappa*q**(3*lam(n)))
            assert recovered==bare[A]
            observed.append({"q":str(q),"n":n,"response":str(response),
                             "kappa":str(kappa),"recovered_b_n":str(recovered)})
    certs=[]
    for terms in [
        [(Q(1,2),(Q(-5),Q(1)))],
        [(Q(1,2),(Q(-7),Q(1))),(Q(1,3),(Q(1),Q(0),Q(1)))],
        [(Q(2,3),(Q(2),Q(-3),Q(1))),(Q(1,4),(Q(-9),Q(7)))],
        [(Q(1,2),(Q(1),Q(2))),(Q(1,2),(Q(-1),Q(-2)))]
    ]:
        cert=positive_tail_certificate(terms);certs.append(cert)
        if not cert["identically_zero"]:
            N=cert["N"]
            for n in range(N,N+80):
                value=sum((beta**n*sum((p[i]*Q(n)**i for i in range(len(p))),Q(0))
                           for beta,p in terms),Q(0))
                assert value!=0
    singular=[Q(0)]*9
    singular[6]=Q(1)
    for n in range(8):
        assert Q(n-5)*Q(1,2)**n*singular[n+1]==0
    assert all(x==0 for x in singular[:6]) and singular[6]!=0
    return {"status":"PASS","python":sys.version,"arithmetic":"fractions.Fraction",
            "source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "lowest_coefficient_checks":64,"valuation_first_ten":valuation,
            "exact_legal_observation_checks":observed,
            "positive_tail_certificates":certs,
            "singular_prefix_countercontrol":{"all_0_through_5":True,
                                             "f_6":"1","recurrence":"(n-5)2^-n f_(n+1)=0"},
            "limits":["64 values are implementation controls, not the non-holonomicity proof.",
                      "The dominance algorithm is implemented for rational bases and coefficients.",
                      "No complete source-generated mixed recurrence was derived.",
                      "No arbitrary-chain all-copy cutoff or zero-test is claimed."]}


if __name__=="__main__":
    print(json.dumps(run(),indent=2,sort_keys=True))
