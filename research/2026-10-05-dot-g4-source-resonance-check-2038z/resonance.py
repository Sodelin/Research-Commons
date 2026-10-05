"""Exact marked-forest quotient diagnostic, not a physical source generator."""
from fractions import Fraction as F
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib,importlib.util,json
PROVIDER=Path(__file__).resolve().parent.parent/'graph-g3-allcap-insertion-20261005-0601z/forest_algebra_pinned.py'
PIN='850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884'
if PROVIDER.is_symlink():raise ValueError('forest utility link')
PROVIDER_BYTES=PROVIDER.read_bytes()
if hashlib.sha256(PROVIDER_BYTES).hexdigest()!=PIN:raise ValueError('forest utility pin')
spec=importlib.util.spec_from_file_location('_g4_forest_provider',PROVIDER);a=importlib.util.module_from_spec(spec);exec(compile(PROVIDER_BYTES,str(PROVIDER),'exec'),a.__dict__)

def build(marked,maximum):
    if not 1<=marked<=4 or not marked<=maximum<=9:raise ValueError('declared quotient bound')
    states=tuple((f,n) for n in range(1,maximum+1) for f in a.forests(tuple(range(marked))) if len(f)<=n);index={s:i for i,s in enumerate(states)}
    q=[];r=[]
    for f,n in states:
        k=len(f);u=n-k;pair={}
        def add(d,state,value):
            if value:d[index[state]]=d.get(index[state],F(0))+value
        for i,j in combinations(range(k),2):
            ff=a.forest([a.tree(f[i],f[j])]+[f[l] for l in range(k) if l not in (i,j)])
            add(pair,(ff,n-1),F(1))
        if u:add(pair,(f,n-1),F(k*u+comb(u,2)))
        qi=dict(pair);add(qi,(f,n),F(-comb(n,2)))
        ri={j:-(n-2)*v for j,v in pair.items()};add(ri,(f,n),F(2*comb(n,3)))
        if u>=2:add(ri,(f,n-2),F(comb(u,3)+k*comb(u,2)))
        if u:
            for i,j in combinations(range(k),2):
                ff=a.forest([a.tree(f[i],f[j])]+[f[l] for l in range(k) if l not in (i,j)])
                add(ri,(ff,n-2),F(u))
        for i,j,l in combinations(range(k),3):
            rest=[f[h] for h in range(k) if h not in (i,j,l)]
            for x,y,z in ((i,j,l),(i,l,j),(j,l,i)):
                add(ri,(a.forest([a.tree(a.tree(f[x],f[y]),f[z])]+rest),n-2),F(1,3))
        q.append({j:v for j,v in qi.items() if v});r.append({j:v for j,v in ri.items() if v})
        assert sum(qi.values())==0 and sum(ri.values())==0
    return states,index,q,r

def apply(v,m):
    out=[F(0)]*len(v)
    for i,x in enumerate(v):
        if x:
            for j,y in m[i].items():out[j]+=x*y
    return out

def projector(v,j,q,maximum):
    out=list(v);lj=comb(j,2)
    for k in range(1,maximum+1):
        if k==j:continue
        lk=comb(k,2);w=apply(out,q);out=[(x+lk*y)/(lk-lj) for x,y in zip(w,out)]
    return out

def rank(vectors):
    piv={}
    for vector in vectors:
        v=list(vector)
        for j,w in sorted(piv.items()):
            c=v[j]
            if c:v=[x-c*y for x,y in zip(v,w)]
        for j,c in enumerate(v):
            if c:piv[j]=[x/c for x in v];break
    return len(piv)

def run():
    states,index,q,r=build(4,9);v=[F(0)]*len(states);v[index[(tuple(range(4)),9)]]=F(1)
    v=projector(v,9,q,9);first=apply(v,r);blocks={}
    for j in range(4,10):
        middle=projector(first,j,q,9);out=projector(apply(middle,r),4,q,9)
        assert apply(out,q)==[-6*x for x in out]
        blocks[str(j)]=out
    direct=projector(first,4,q,9)
    # Endpoint intermediates are scalar multiples of the direct block. Other
    # unequal-gap intermediate products give an intentionally generous span.
    rivals=[direct]+[blocks[str(j)] for j in (5,6,8)]
    before=rank(rivals);after=rank(rivals+[blocks['7']])
    encode=lambda row:[{'state_index':i,'coefficient':str(x)} for i,x in enumerate(row) if x]
    return {'schema':'fixed-actual-cubic-resonance-v1','marked_tokens':4,'maximum_current_roots':9,'state_count':len(states),'states':[{'marked_forest':repr(f),'total_roots':n} for f,n in states],'orientation':'row distributions act from left; chronological product P9 R3 Pj R3 P4','R3_normalization':'diagonal2*C(n,3), each pair coefficient-(n-2), each triple uniformly resolved with total coefficient1','spectral_eigenvalues':{'9':36,'7':21,'4':6},'resonant_product_nonzero':any(blocks['7']),'resonant_product':encode(blocks['7']),'all_intermediate_products':{j:encode(v) for j,v in blocks.items()},'direct_block':encode(direct),'generous_nonresonant_span_rank':before,'rank_with_resonant_product':after,'outside_generous_nonresonant_span':after>before,'provider_sha256':PIN,'inference':'nonzero quotient implies nonzero full operator; zero quotient is inconclusive; no positive-word or G4 closure claim'}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
