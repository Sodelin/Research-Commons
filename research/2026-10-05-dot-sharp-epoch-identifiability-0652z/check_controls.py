#!/usr/bin/env python3
"""Exact finite controls for the sharp epoch reconstruction proof.
Rates are dimensionless r/(8/3), durations are multiples of log2/(8/3),
so all survival factors and integer pair moments are rational. This does
not estimate a model from finite noisy data or replace the all-model proof.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json

def pairs(p):return [(i,j) for i in range(p) for j in range(i,p)]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def mm(A,B):return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def mv(A,v):return [sum(a*b for a,b in zip(row,v)) for row in A]
def rank(A):
    X=[list(map(Q,row)) for row in A];m=len(X);n=len(X[0]);r=0
    for c in range(n):
        piv=next((i for i in range(r,m) if X[i][c]),None)
        if piv is None:continue
        X[r],X[piv]=X[piv],X[r];z=X[r][c];X[r]=[v/z for v in X[r]]
        for i in range(m):
            if i!=r:
                z=X[i][c];X[i]=[a-z*b for a,b in zip(X[i],X[r])]
        r+=1
        if r==m:break
    return r

def solve(A,b):
    X=[list(map(Q,row))+[Q(v)] for row,v in zip(A,b)];m=len(X);n=len(A[0]);r=0;sol=[None]*n
    for c in range(n):
        piv=next((i for i in range(r,m) if X[i][c]),None)
        assert piv is not None,'Not full column rank'
        X[r],X[piv]=X[piv],X[r];z=X[r][c];X[r]=[v/z for v in X[r]]
        for i in range(m):
            if i!=r:
                z=X[i][c];X[i]=[a-z*b for a,b in zip(X[i],X[r])]
        r+=1
    for i in range(n,m):assert all(v==0 for v in X[i])
    return [X[i][-1] for i in range(n)]

def route(G):
    p=len(G);q=len(G[0]);R=[]
    for i,j in pairs(p):
        row=[]
        for a,b in pairs(q):
            if a==b:val=G[i][a]*G[j][a]
            elif i==j:val=2*G[i][a]*G[i][b]
            else:val=G[i][a]*G[j][b]+G[i][b]*G[j][a]
            row.append(val)
        assert sum(row)==1
        R.append(row)
    return R

def survival(rates,d):return [Q(2)**(-rates[i]*d) if i==j else Q(1) for i,j in pairs(len(rates))]
def scale_columns(U,d):return [[x*y for x,y in zip(row,d)] for row in U]
def hazard(rs):return [Q(rs[i]) if i==j else Q(0) for i,j in pairs(len(rs))]
def sqrtq(x):
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    assert a*a==x.numerator and b*b==x.denominator
    return Q(a,b)

def forward(model):
    rs,ds,Gs=model['rates'],model['durations'],model['routing']
    Us=[eye(len(pairs(len(rs[0]))))];Ts=[]
    for j,(d,G) in enumerate(zip(ds,Gs)):
        assert rank(G)==len(G[0]);R=route(G);assert rank(R)==len(R[0])
        T=scale_columns(Us[-1],survival(rs[j],d));Ts.append(T)
        Us.append(mm(T,R));assert rank(Us[-1])==len(Us[-1][0])
    return Us,Ts

def moments(model,k):
    rs,ds=model['rates'],model['durations'];Us,_=forward(model)
    out=[Q(0)]*len(Us[0]);time=0
    for j,d in enumerate(ds):
        states=pairs(len(rs[j]))
        for p,r in enumerate(rs[j]):
            col=states.index((p,p));fac=Q(r,r+k)*(Q(2)**(-k*time)-Q(2)**(-r*d-k*(time+d)))
            for i in range(len(out)):out[i]+=Us[j][i][col]*fac
        time+=d
    r=rs[-1][0];fac=Q(r,r+k)*Q(2)**(-k*time)
    for i in range(len(out)):out[i]+=Us[-1][i][0]*fac
    return out

def backward_moments(model,k):
    rs,ds,Gs=model['rates'],model['durations'],model['routing']
    f=[Q(rs[-1][0],rs[-1][0]+k)]
    for j in reversed(range(len(ds))):
        d=ds[j];future=mv(route(Gs[j]),f);states=pairs(len(rs[j]));new=[]
        for pos,(a,b) in enumerate(states):
            if a==b:
                r=rs[j][a];v=Q(2)**(-(r+k)*d)
                new.append(Q(r,r+k)*(1-v)+v*future[pos])
            else:new.append(Q(2)**(-k*d)*future[pos])
        f=new
    return f

model={'rates':[[1,2,3],[2,4,5],[3,6],[4,7],[2]],'durations':[1,2,1,1],
       'routing':[[[Q(1),Q(0),Q(0)],[Q(1,4),Q(3,4),Q(0)],[Q(0),Q(0),Q(1)]],
                  [[Q(1),Q(0)],[Q(1),Q(0)],[Q(0),Q(1)]],
                  [[Q(3,4),Q(1,4)],[Q(1,3),Q(2,3)]],[[Q(1)],[Q(1)]]]}
Us,Ts=forward(model);recovered=[];prony_checks=0
for j,rs in enumerate(model['rates']):
    ps=pairs(len(rs));C=[[Q(r)*Us[j][i][ps.index((a,a))] for a,r in enumerate(rs)] for i in range(len(Us[0]))]
    assert all(sum(row[a] for row in C)>0 for a in range(len(rs)))
    # Classical exact Prony polynomial from scalar aggregate derivative moments.
    z=[sum(sum(row[a] for row in C)*Q(r)**k for a,r in enumerate(rs)) for k in range(2*len(rs))]
    H=[[z[i+k] for k in range(len(rs))] for i in range(len(rs))]
    coeff=solve(H,[-z[i+len(rs)] for i in range(len(rs))])
    for r in rs:assert Q(r)**len(rs)+sum(c*Q(r)**i for i,c in enumerate(coeff))==0
    V=[[Q(r)**k for r in rs] for k in range(len(rs))]
    for row in C:
        deriv=[sum(row[a]*Q(r)**k for a,r in enumerate(rs)) for k in range(len(rs))]
        assert solve(V,deriv)==row;prony_checks+=1
    if j:
        T=Ts[j-1];oldp=len(model['rates'][j-1]);G=model['routing'][j-1];cols=[]
        for b,r in enumerate(rs):
            col=[C[i][b]/r for i in range(len(C))];w=solve(T,col)
            rec=[sqrtq(w[pairs(oldp).index((a,a))]) for a in range(oldp)]
            assert rec==[G[a][b] for a in range(oldp)];cols.append(rec)
        recovered.append([[str(v) for v in row] for row in zip(*cols)])
        oldh=hazard(model['rates'][j-1]);newh=mv(route(G),hazard(rs))
        assert oldh!=newh and mv(T,oldh)!=mv(T,newh)

moment_checks=0
for k in range(17):
    assert moments(model,k)==backward_moments(model,k);moment_checks+=len(Us[0])
assert moments(model,0)==[1]*len(Us[0])

# Hidden-state permutations preserve all checked pair laws, including the
# bidirectional population-switch interpretation; initial labels stay fixed.
perms=[[0,1,2],[2,0,1],[1,0],[1,0],[0]]
other={'rates':[],'durations':model['durations'][:],'routing':[]}
for j,rs in enumerate(model['rates']):
    out=[None]*len(rs)
    for a,r in enumerate(rs):out[perms[j][a]]=r
    other['rates'].append(out)
for j,G in enumerate(model['routing'],1):
    H=[[Q(0)]*len(G[0]) for _ in G]
    for i,row in enumerate(G):
        for a,g in enumerate(row):H[perms[j-1][i]][perms[j][a]]=g
    other['routing'].append(H)
permutation_checks=0
for k in range(25):
    assert moments(model,k)==moments(other,k);permutation_checks+=len(Us[0])

# Negative/admission controls: redundant boundary, rank collapse, and missing
# within-population pair types. They are not claimed complete nonidentifiability tests.
I=eye(2);join=[[Q(1)],[Q(1)]]
silent={'rates':[[1,2],[1,2],[3]],'durations':[1,2],'routing':[I,join]}
removed={'rates':[[1,2],[3]],'durations':[3],'routing':[join]}
for k in range(17):assert moments(silent,k)==moments(removed,k)
assert mv(route(I),hazard([1,2]))==hazard([1,2])
assert mv(route(I),hazard([1,3]))!=hazard([1,2])
bad=[[Q(1,2),Q(1,2)],[Q(1,2),Q(1,2)]]
assert rank(bad)==1 and rank(route(bad))==1
assert 3*(3-1)//2 < 3*(3+1)//2

# Full rational annihilator check on different, inequivalent models.
changed={'rates':[[1,2,3],[3,4,6],[3,6],[4,7],[2]],'durations':[2,1,1,2],
         'routing':[row for row in model['routing']]}
def pmul(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
boundaries=set()
for mod in [model,changed]:
    t=0;boundaries.add(0)
    for d in mod['durations']:t+=d;boundaries.add(t)
R1=sum(map(len,model['rates']));R2=sum(map(len,changed['rates']))
ann=[Q(1)]
for t in sorted(boundaries):
    for _ in range(R1+R2):ann=pmul(ann,[-Q(2)**(-t),Q(1)])
order=len(ann)-1;assert ann[-1]==1 and order<=2*(2*4+1)*(4*3+1)
seq=[]
for k in range(order+3):
    den=Q(1)
    for mod in [model,changed]:
        for rs in mod['rates']:
            for r in rs:den*=r+k
    diff=[a-b for a,b in zip(moments(model,k),moments(changed,k))]
    seq.append([den*d for d in diff])
recurrence_checks=0
for pair_index in [0,1]:
    assert any(v[pair_index] for v in seq)
    for start in range(3):
        assert sum(c*seq[start+i][pair_index] for i,c in enumerate(ann))==0;recurrence_checks+=1

result={'status':'PASS','arithmetic':'Integer/Fraction only',
        'population_counts':[len(rs) for rs in model['rates']],
        'pair_transition_column_ranks':[rank(U) for U in Us],
        'exact_prony_component_reconstructions':prony_checks,
        'recovered_routing_matrices':recovered,'visible_boundaries_verified':len(Ts),
        'density_vs_backward_moment_checks':moment_checks,
        'hidden_population_permutation_moment_checks':permutation_checks,
        'silent_boundary_moment_checks':17,'rank_collapse_control':'rejected as outside class',
        'observed_annihilator_order':order,'nonzero_sequence_recurrence_checks':recurrence_checks,
        'generic_J4_P3_site_bound':2*(2*4+1)*(4*3+1)-1,
        'limits':'Finite exact controls of the proof formulas, not noisy-data estimation, complete catalogue fitting, sample-size calibration or formal Lean verification.'}
Path(__file__).with_name('CONTROL-RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
