"""Lossless exchangeable full-forest row for one fixed cap-nine operator test."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb,factorial
from collections import Counter
import json

def tree(a,b):return '('+''.join(sorted((a,b)))+')'
@lru_cache(None)
def trees(n):
    if n==1:return ('x',)
    return tuple(sorted({tree(a,b) for i in range(1,n) for a in trees(i) for b in trees(n-i)}))
@lru_cache(None)
def forests(n):
    if n==0:return ((),)
    return tuple(sorted({tuple(sorted((t,)+r)) for i in range(1,n+1) for t in trees(i) for r in forests(n-i)}))
def children(t):
    if t=='x':raise ValueError('leaf has no children')
    body=t[1:-1]
    if body[0]=='x':return body[:1],body[1:]
    depth=0
    for i,ch in enumerate(body):
        depth+=(ch=='(')-(ch==')')
        if depth==0:return body[:i+1],body[i+1:]
    raise ValueError('invalid canonical tree')
@lru_cache(None)
def aut(t):
    if t=='x':return 1
    a,b=children(t);return aut(a)*aut(b)*(2 if a==b else 1)
def orbit_size(f):
    n=sum(t.count('x') for t in f);den=1
    for t,m in Counter(f).items():den*=aut(t)**m*factorial(m)
    assert factorial(n)%den==0
    return factorial(n)//den

def build(n):
    if not 1<=n<=9:raise ValueError('fixed cap bound')
    states=tuple(sorted(forests(n),key=lambda f:(len(f),f)));ids={f:i for i,f in enumerate(states)};q=[];r=[]
    for f in states:
        k=len(f);qi={ids[f]:F(-comb(k,2))};ri={ids[f]:F(2*comb(k,3))}
        def add(d,ff,c):
            j=ids[tuple(sorted(ff))];d[j]=d.get(j,F(0))+c
        for i,j in combinations(range(k),2):
            ff=[tree(f[i],f[j])]+[f[h] for h in range(k) if h not in (i,j)]
            add(qi,ff,F(1));add(ri,ff,F(-(k-2)))
        for i,j,l in combinations(range(k),3):
            rest=[f[h] for h in range(k) if h not in (i,j,l)]
            for x,y,z in ((i,j,l),(i,l,j),(j,l,i)):add(ri,[tree(tree(f[x],f[y]),f[z])]+rest,F(1,3))
        assert sum(qi.values())==sum(ri.values())==0
        q.append({j:v for j,v in qi.items() if v});r.append({j:v for j,v in ri.items() if v})
    return states,ids,q,r

def apply(v,m):
    out=[F(0)]*len(v)
    for i,x in enumerate(v):
        if x:
            for j,y in m[i].items():out[j]+=x*y
    return out

def project(v,j,q,n):
    out=list(v);lj=comb(j,2)
    for k in range(1,n+1):
        if k!=j:
            lk=comb(k,2);w=apply(out,q);out=[(x+lk*y)/(lk-lj) for x,y in zip(w,out)]
    return out

def rank(vectors):
    piv={}
    for v in vectors:
        v=list(v)
        for j,w in sorted(piv.items()):
            c=v[j]
            if c:v=[x-c*y for x,y in zip(v,w)]
        for j,c in enumerate(v):
            if c:piv[j]=[x/c for x in v];break
    return len(piv)

def relation(columns,target):
    a=[[*row,t] for row,t in zip(zip(*columns),target)];where={};p=0
    for j in range(len(columns)):
        i=next((i for i in range(p,len(a)) if a[i][j]),None)
        if i is None:continue
        a[p],a[i]=a[i],a[p];d=a[p][j];a[p]=[x/d for x in a[p]]
        for i in range(len(a)):
            if i!=p and a[i][j]:
                d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[p])]
        where[j]=p;p+=1
    if any(not any(row[:-1]) and row[-1] for row in a):return None
    result=[F(0)]*len(columns)
    for j,i in where.items():result[j]=a[i][-1]
    assert [sum(c*x for c,x in zip(result,row)) for row in zip(*columns)]==target
    return result

def run():
    n=9;states,ids,q,r=build(n)
    if len(states)>2000:raise ValueError('predeclared state ceiling')
    e=[F(0)]*len(states);e[ids[('x',)*n]]=F(1);v=project(e,9,q,n);first=apply(v,r);blocks={}
    for j in range(4,10):
        blocks[str(j)]=project(apply(project(first,j,q,n),r),4,q,n)
        assert apply(blocks[str(j)],q)==[-6*x for x in blocks[str(j)]]
    direct=project(first,4,q,n);other=[direct]+[blocks[str(j)] for j in (5,6,8)];coeff=relation(other,blocks['7'])
    encode=lambda row:[{'orbit_index':i,'orbit_mass_coefficient':str(v),'coefficient_per_labelled_forest':str(v/orbit_size(states[i]))} for i,v in enumerate(row) if v]
    return {'schema':'lossless-full-nine-forest-resonance-v1','entering_roots':9,'orbit_count':len(states),'complete_labelled_forest_count':sum(map(orbit_size,states)),'orbits':[{'shape':list(f),'current_roots':len(f),'labelled_multiplicity':orbit_size(f)} for f in states],'orientation':'row distributions, chronological P9 R3 Pj R3 P4','normalization':'R3=-2T of accepted physical cubic provider','resonant_product_nonzero':any(blocks['7']),'resonant_product':encode(blocks['7']),'all_intermediate_products':{j:encode(v) for j,v in blocks.items()},'direct_block':encode(direct),'generous_nonresonant_span_rank':rank(other),'rank_with_resonant_product':rank(other+[blocks['7']]),'resonant_relation_coefficients_D_V5_V6_V8':None if coeff is None else list(map(str,coeff)),'lossless_scope':'complete exchangeable fresh-nine row; P9 annihilates lower arities, so graft extension gives the capped abstract-root operator','master_G4_closed':False,'positive_cancellation_constructed':False}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
