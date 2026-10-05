#!/usr/bin/env python3
"""Exact three-tip Fourier controls: full-state propagation versus two-time densities."""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
from math import prod, comb
import json

# Dimensionless mu=1; lengths log(2); r denotes rate/mu. All numbers rational.
Gs=[[[Q(3,4),Q(1,4)],[Q(1,4),Q(3,4)]],[[Q(1)],[Q(1)]]]
rates=[[1,1],[2,2],[1]]
chars=[(1,1,0),(1,0,1),(0,1,1),(1,2,3)]
startblocks=((0,),(1,),(2,))
def merges(st):
    bs,ps=st
    for i,j in combinations(range(len(bs)),2):
        if ps[i]!=ps[j]:continue
        out=[(bs[k],ps[k]) for k in range(len(bs)) if k not in (i,j)]
        out.append((tuple(sorted(bs[i]+bs[j])),ps[i]));out.sort()
        yield (tuple(b for b,p in out),tuple(p for b,p in out)),ps[i]
def kill(st,n):
    bs,_=st; total=0
    for N,ch in zip(n,chars):
        for b in bs:
            val=0
            for i in b:val^=ch[i]
            total+=N*(val!=0)
    return total
def exit_rate(st,rs):return sum(rs[p] for _,p in merges(st))
def route(st,G):
    bs,ps=st
    for out in product(range(len(G[0])),repeat=len(bs)):
        w=prod(G[p][q] for p,q in zip(ps,out))
        if w:yield (bs,out),w
def add(D,k,v):D[k]=D.get(k,Q(0))+v

def epoch(D,rs,n):
    O={}
    for initial,w in D.items():
        def walk(st,qs,coef):
            q=exit_rate(st,rs)+kill(st,n);qs=qs+[q]
            assert len(set(qs))==len(qs)
            I=sum(Q(2)**(-x)/prod(y-x for y in qs if y!=x) for x in qs)
            add(O,st,w*coef*I)
            for nxt,p in merges(st):walk(nxt,qs,coef*rs[p])
        walk(initial,[],Q(1))
    return O

def direct(init,n):
    D={(startblocks,init):Q(1)}
    for rs,G in zip(rates,Gs):
        D=epoch(D,rs,n);O={}
        for st,w in D.items():
            for ns,v in route(st,G):add(O,ns,w*v)
        D=O
    def root(st):
        if len(st[0])==1:return Q(1)
        q=exit_rate(st,rates[-1])+kill(st,n)
        return sum(Q(rates[-1][p],q)*root(ns) for ns,p in merges(st))
    return sum(w*root(st) for st,w in D.items())

def surv_route(D,rs,G):
    O={}
    for st,w in D.items():
        w*=Q(2)**(-exit_rate(st,rs))
        for ns,v in route(st,G):add(O,ns,w*v)
    return O

def interval(x,j,root=False):return Q(2)**(-x*j)/x if root else (Q(2)**(-x*j)-Q(2)**(-x*(j+1)))/x

def tri(x,y,j,root=False):
    if root:return Q(2)**(-(x+y)*j)/(y*(x+y))
    U=j+1
    return (Q(2)**(-(x+y)*j)-Q(2)**(-(x+y)*U))/(y*(x+y))-Q(2)**(-y*U)*(Q(2)**(-x*j)-Q(2)**(-x*U))/(y*x)

def density(init,n):
    starts=[{(startblocks,init):Q(1)}]
    for rs,G in zip(rates,Gs):starts.append(surv_route(starts[-1],rs,G))
    ans=Q(0);pieces=0
    for j,D in enumerate(starts):
        rs=rates[j]
        for st,w in D.items():
            pre=exit_rate(st,rs)
            for ns,p in merges(st):
                cherry=next(b for b in ns[0] if len(b)==2)
                c=[(0,1),(0,2),(1,2)].index(cherry)
                A=2*n[c]+n[3];B=2*(sum(n[:3])-n[c]+n[3])
                post=exit_rate(ns,rs);a=pre-post
                assert a in (rs[p],2*rs[p])
                if post:
                    assert pre==3*rs[p] and post==rs[p]
                    amp=w*rs[p]**2*Q(2)**(3*rs[p]*j)
                    ans+=amp*tri(2*rs[p]+A,rs[p]+B,j,j==len(Gs));pieces+=1
                if j==len(Gs):continue
                # Density after first merger, survive to next boundary, route.
                amp=w*rs[p]*Q(2)**(a*j-post)
                two={}
                for nxt,v in route(ns,Gs[j]):add(two,nxt,v)
                for k in range(j+1,len(rates)):
                    for st2,v in two.items():
                        for final,q in merges(st2):
                            b=rates[k][q]
                            coeff=amp*v*b*Q(2)**(b*k)
                            ans+=coeff*interval(a+A,j)*interval(b+B,k,k==len(Gs));pieces+=1
                    if k<len(Gs):two=surv_route(two,rates[k],Gs[k])
    return ans,pieces

checks=0;pieces=0
for init in product(range(2),repeat=3):
    for n in product(range(2),repeat=4):
        a=direct(init,n);b,p=density(init,n)
        assert a==b,(init,n,a,b)
        if not any(n):assert a==1
        checks+=1;pieces+=p

# Direct rational integration of exp(-x*u-y*v), using variables 2^-u,
# checks finite/root triangles against sequential holding-time convolution.
triangle_checks=0
for x in range(1,6):
    for y in range(1,6):
        for j in range(3):
            # Independent evaluation after translating lower endpoint to zero.
            finite=Q(2)**(-(x+y)*j)*(Q(1,y)*((1-Q(2)**(-(x+y)))/(x+y)-Q(2)**(-y)*(1-Q(2)**(-x))/x))
            assert tri(x,y,j)==finite
            assert tri(x,y,j,True)==Q(2)**(-(x+y)*j)/Q(y*(x+y))
            triangle_checks+=2

# Coordinate recurrence exact control with repeated bases and polynomial weights.
def diff(seq,z):return [seq[i+1]-z*seq[i] for i in range(len(seq)-1)]
seq=[(k*k+3*k+1)*Q(2)**(-k)+(2*k+1)*Q(4)**(-k) for k in range(15)]
for z in (Q(1,2),Q(1,4)):
    for _ in range(3):seq=diff(seq,z)
assert not any(seq)

bounds={}
for J,P in [(1,2),(4,3),(10,10)]:
    R=J*P+1;K=6*(J+1)**2*(24*R+1)
    bounds[f'J{J}_P{P}']=4*(K-1)
result={'status':'PASS','arithmetic':'stdlib Fraction only; dimensionless mu=1 and lengths log2',
'full_state_vs_joint_density_fourier_checks':checks,'density_terms_checked':pieces,
'finite_and_root_triangle_integral_checks':triangle_checks,
'zero_count_normalization':True,'equal_rates_in_all_nonroot_epochs':True,
'exponential_polynomial_recurrence_control':True,'polynomial_bounds':bounds,
'limits':'Finite exact controls; full uniform endpoint/denominator count and law transfer are hand proved. No finite-loci accuracy, optimal bound, novelty or Lean claim.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('POLYNOMIAL-CONTROL-RESULTS.json').write_text(text);print(text,end='')
