"""Exact finite-field minor certificate for a strict full-forest source bank.

The field calculation certifies a nonzero rational Jacobian minor. It is not
a search for an ordinary common zero, a convex mixture, or a physical inverse.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import time
import types

HELPER_SHA="e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"
PRIME=1000000007

def load_helper():
    p=Path(__file__).with_name("exact_forest_layer.py")
    captured=p.read_bytes()
    if sha256(captured).hexdigest()!=HELPER_SHA:
        raise ValueError("Frozen helper identity mismatch")
    module=types.ModuleType("frozen_forest_layer_helper")
    module.__file__=str(p)
    exec(compile(captured,str(p),"exec"),module.__dict__)
    return module

def mod(q):
    q=F(q)
    if q.denominator%PRIME==0:
        raise ValueError("Rational denominator vanishes in chosen field")
    return q.numerator*pow(q.denominator,-1,PRIME)%PRIME
def mm(a,b):
    n=len(a)
    out=[[0]*n for _ in range(n)]
    for i,row in enumerate(a):
        for k,c in enumerate(row):
            if c:
                for j,d in enumerate(b[k]):
                    if d:
                        out[i][j]=(out[i][j]+c*d)%PRIME
    return out
def vm(v,a):
    out=[0]*len(v)
    for k,c in enumerate(v):
        if c:
            for j,d in enumerate(a[k]):
                if d:
                    out[j]=(out[j]+c*d)%PRIME
    return out
def ident(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]
def elim(rows):
    a=[r[:] for r in rows]
    labels=list(range(len(a)))
    pivcols=[]
    pivrows=[]
    k=0
    determinant=1
    for j in range(len(a[0])):
        ii=next((i for i in range(k,len(a)) if a[i][j]),None)
        if ii is None:
            continue
        if ii!=k:
            a[k],a[ii]=a[ii],a[k]
            labels[k],labels[ii]=labels[ii],labels[k]
            determinant=-determinant
        d=a[k][j]
        determinant=determinant*d%PRIME
        inv=pow(d,-1,PRIME)
        a[k]=[x*inv%PRIME for x in a[k]]
        for i in range(k+1,len(a)):
            if a[i][j]:
                d=a[i][j]
                a[i]=[(x-d*y)%PRIME for x,y in zip(a[i],a[k])]
        pivcols.append(j)
        pivrows.append(labels[k])
        k+=1
        if k==len(a):
            break
    return k,pivrows,pivcols,determinant%PRIME
def minor_det(rows):
    rank,_,_,det=elim(rows)
    return det if rank==len(rows) else 0

def ordinary(E,z):
    zz=mod(z)
    return [[sum(mod(c)*pow(zz,e,PRIME) for e,c in p.items())%PRIME for p in row] for row in E]

def branch_scalar(p,q,s,h2):
    """Symmetric monomial and derivative wrt h^2, exact in the field."""
    m=min(p,q)
    d=abs(p-q)
    xy=(s*s-h2)%PRIME
    if d==0:
        return pow(xy,m,PRIME),(-m*pow(xy,m-1,PRIME))%PRIME if m else 0
    a=sum(comb(d,2*j)*pow(s,d-2*j,PRIME)*pow(h2,j,PRIME) for j in range(d//2+1))%PRIME
    da=sum(j*comb(d,2*j)*pow(s,d-2*j,PRIME)*pow(h2,j-1,PRIME) for j in range(1,d//2+1))%PRIME
    v=2*pow(xy,m,PRIME)*a%PRIME
    dv=2*(pow(xy,m,PRIME)*da-(m*pow(xy,m-1,PRIME)*a if m else 0))%PRIME
    return v,dv
def branch(B,A,w,t):
    n=len(B)
    s=mod(1-A*t)
    h2=mod(w*t**3)
    scale=mod(t**3)
    out=[[0]*n for _ in range(n)]
    der=[[0]*n for _ in range(n)]
    values={}
    for i,row in enumerate(B):
        for j,p in enumerate(row):
            for (px,py),c in p.items():
                if px<py:
                    continue
                assert p.get((py,px),F(0))==c
                if (px,py) not in values:
                    values[px,py]=branch_scalar(px,py,s,h2)
                v,dv=values[px,py]
                out[i][j]=(out[i][j]+mod(c)*v)%PRIME
                der[i][j]=(der[i][j]+mod(c)*dv*scale)%PRIME
    assert all(sum(row)%PRIME==1 for row in out)
    assert all(sum(row)%PRIME==0 for row in der)
    return out,der

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    h=load_helper()
    fa,pin=h.load_source(args.root)
    states=[h.representative(s,fa) for s in h.SHAPES6]
    index={s:i for i,s in enumerate(h.SHAPES6)}
    E=h.ordinary_polynomials(states,index,fa)
    B=h.bigon_polynomials(states,index,fa)
    C=h.delete_one(states,fa)
    A=[F(i,5) for i in range(1,5)]
    w=[F(2,125),F(33,1000),F(49,750),F(19,1000)]
    gamma=[a**3/12-b/2 for a,b in zip(A,w)]
    for k in range(4):
        assert sum(a**k*b for a,b in zip(A,w))==sum(a**(k+3)/F(2*(k+3)) for a in A)
    assert sum(gamma)==0 and min(w)>0
    t=F(1,1024)
    target_pair=F(1,4)
    prefix_survival=F(7,8)
    intra=1-t
    inter=F(9,10)
    n=len(states)
    factors=[ordinary(E,prefix_survival)]
    variables=[]
    pair=prefix_survival
    physical=[]
    for group in range(9):
        for j in range(4):
            aa,ww=A[j],w[j]
            ss=1-aa*t
            hh=ww*t**3
            # These exact inequalities imply 0<s-sqrt(h2)<s+sqrt(h2)<1.
            assert hh>0 and hh<ss**2 and hh<(aa*t)**2
            mat,der=branch(B,aa,ww,t)
            variables.append((len(factors),der))
            factors.append(mat)
            q=1-aa*t/2
            pair*=q
            physical.append({"group":group,"cell":j,"A":str(aa),"w":str(ww),
                             "s":str(ss),"h_squared":str(hh),"q":str(q),
                             "strict_arm_inequalities":True})
            if group!=8 or j!=3:
                gap=inter if j==3 else intra
                factors.append(ordinary(E,gap))
                pair*=gap
    calibration=target_pair/pair
    assert 0<calibration<1
    factors.append(ordinary(E,calibration))
    fresh=[1]+[0]*(n-1)
    prefix=[fresh]
    for factor in factors:
        prefix.append(vm(prefix[-1],factor))
    suffix=[None]*(len(factors)+1)
    suffix[-1]=ident(n)
    for i in range(len(factors)-1,-1,-1):
        suffix[i]=mm(factors[i],suffix[i+1])
    columns=[vm(vm(prefix[i],der),suffix[i+1]) for i,der in variables]
    J=[list(row) for row in zip(*columns)]
    # Complete lower forest response, with the new diagonal. No completed
    # tree projection or diagonal-only substitute is used.
    lower=[[sum(c*x for c,x in zip(row,col))%PRIME for col in columns] for row in C]
    lower_plus_diag=lower+[J[0]]
    full_rank,rr,cc,_=elim(J)
    constrained_rank=elim(lower_plus_diag)[0]
    sub=[[J[i][j] for j in cc] for i in rr]
    det=minor_det(sub)
    assert det!=0
    # Lower constraints are literally source-row coordinates; the quotient
    # rank difference is the local IFT fibre-image rank at THIS source point.
    result={"status":"EXECUTED_EXACT_RATIONAL_JACOBIAN_NONZERO_MINOR_CERTIFICATE_MOD_PRIME",
            "original_source":h.SOURCE,"original_source_sha256":pin,
            "executed_helper_sha256":HELPER_SHA,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "prime":PRIME,"rational_reduction_denominator_checks":True,
            "source_cells":physical,"t":str(t),"inheritance":"independent current roots, fair coin",
            "prefix_survival":str(prefix_survival),"intragroup_survival":str(intra),
            "intergroup_survival":str(inter),"pair_before_calibration":str(pair),
            "calibration_survival":str(calibration),"target_pair_survival":str(target_pair),
            "physical_word_is_strict":True,"one_shared_parameter_tuple_all_arities":True,
            "four_leading_diagonal_equations_exact":True,
            "same_placement_group_cubic_sum_zero":True,"group_gamma":list(map(str,gamma)),
            "full_20_by_36_jacobian_mod_prime":J,
            "complete_lower_plus_new_diagonal_jacobian_mod_prime":lower_plus_diag,
            "full_rank_lower_bound":full_rank,
            "lower_plus_diagonal_rank_lower_bound":constrained_rank,
            "full_minor_rows":rr,"full_minor_columns":cc,"full_minor_determinant_mod_prime":det,
            "candidate_constrained_rank_difference":full_rank-constrained_rank,
            "base_response_mod_prime":prefix[-1],
            "ordinary_target_mod_prime":[r for r in ordinary(E,target_pair)[0]],
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["ordinary common zero at t>0","exact lower target equality at this bank point",
                           "fibre centred at the ordinary target","all-cap result","uniform positive hazard budget"]}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"full_rank":full_rank,"lower_plus_diag_rank":constrained_rank,
                      "rank_difference":full_rank-constrained_rank,"nonzero_minor":det,
                      "runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
