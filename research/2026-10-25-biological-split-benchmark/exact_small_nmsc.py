"""Small exact natural-I genealogy compiler. Experimental, not independently verified.
Kingman edge transition probabilities use finite triangular ODEs over Q[s].
No dependencies beyond the Python standard library.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from collections import defaultdict
import json

def join(a,b): return '('+','.join(sorted((a,b)))+')'
def merge(fs,i,j):return tuple(sorted([x for k,x in enumerate(fs) if k not in (i,j)]+[join(fs[i],fs[j])]))
def lam(k):return k*(k-1)//2

@lru_cache(None)
def edge(fs,s):
    if len(fs)<2:return ((fs,F(1)),)
    levels={len(fs):{fs}}
    poly={fs:{lam(len(fs)):F(1)}}
    for k in range(len(fs),1,-1):
        levels.setdefault(k-1,set())
        for state in sorted(levels.get(k,set())):
            for i,j in combinations(range(k),2):
                dest=merge(state,i,j);levels[k-1].add(dest)
                pd=poly.setdefault(dest,defaultdict(F));ld=lam(k-1)
                for exponent,c in poly[state].items():
                    assert exponent!=ld
                    v=c/F(ld-exponent)
                    pd[exponent]+=v;pd[ld]-=v
    result=[]
    for state,p in poly.items():
        prob=sum((c*s**ex for ex,c in p.items()),F(0))
        assert prob>=0
        if prob:result.append((state,prob))
    assert sum(p for _,p in result)==1
    return tuple(result)

@lru_cache(None)
def ancestral(fs):
    if len(fs)==1:return ((fs[0],F(1)),)
    out=defaultdict(F)
    for i,j in combinations(range(len(fs)),2):
        for t,p in ancestral(merge(fs,i,j)):out[t]+=p/F(lam(len(fs)))
    assert sum(out.values())==1
    return tuple(out.items())

def normalize(state):return tuple(sorted((v,tuple(sorted(fs))) for v,fs in state.items() if fs))
def add_to(state,v,fs):state[v]=tuple(sorted(state.get(v,())+fs))

def law(nodes,parents,survival,allocation,gamma):
    # nodes is children-before-parents topological order, root last.
    start={x:tuple(f'{x}{i}' for i in range(k)) for x,k in allocation.items()}
    dist={normalize(start):F(1)}
    for node in nodes[:-1]:
        out=defaultdict(F)
        for key,weight in dist.items():
            state=dict(key);fs=state.pop(node,())
            ps=parents[node]
            if len(ps)==1:
                p=ps[0]
                for ff,prob in edge(fs,survival[(p,node)]):
                    st=state.copy();add_to(st,p,ff);out[normalize(st)]+=weight*prob
            else:
                assert len(ps)==2
                p,q=ps;g=gamma[node]
                for mask in product((0,1),repeat=len(fs)):
                    a=tuple(fs[i] for i,b in enumerate(mask) if b==0)
                    b=tuple(fs[i] for i,b in enumerate(mask) if b==1)
                    routing=g**len(a)*(1-g)**len(b)
                    for aa,pa in edge(a,survival[(p,node)]):
                        for bb,pb in edge(b,survival[(q,node)]):
                            st=state.copy();add_to(st,p,aa);add_to(st,q,bb)
                            out[normalize(st)]+=weight*routing*pa*pb
        dist=dict(out)
        assert sum(dist.values())==1
    result=defaultdict(F)
    for key,w in dist.items():
        state=dict(key);assert set(state)=={nodes[-1]}
        for t,p in ancestral(state[nodes[-1]]):result[t]+=w*p
    assert sum(result.values())==1
    return dict(result)

def parse_tree(s):
    if not s.startswith('('):return s
    depth=0
    for k,c in enumerate(s[1:-1],1):
        if c=='(':depth+=1
        elif c==')':depth-=1
        elif c==',' and depth==0:return (parse_tree(s[1:k]),parse_tree(s[k+1:-1]))
    raise ValueError(s)
def leaves(t):return {t} if isinstance(t,str) else leaves(t[0])|leaves(t[1])
def unrooted_key(s):
    t=parse_tree(s);alll=leaves(t);splits=set()
    def visit(v):
        if isinstance(v,str):return
        a=leaves(v);b=alll-a
        if len(a)>1 and len(b)>1:splits.add(tuple(sorted((tuple(sorted(a)),tuple(sorted(b))))))
        visit(v[0]);visit(v[1])
    visit(t)
    return str(tuple(sorted(splits)))
def unroot(dist):
    out=defaultdict(F)
    for t,p in dist.items():out[unrooted_key(t)]+=p
    return dict(out)
def tv(a,b):return sum(abs(a.get(k,F(0))-b.get(k,F(0))) for k in set(a)|set(b))/2

def triangle(z):
    es=[('R','U'),('R','D'),('U','V'),('U','H'),('V','C'),('V','H'),('H','W'),('W','A'),('W','B')]
    pars={}
    for p,c in es:pars.setdefault(c,[]).append(p)
    ss={e:F(1,2) for e in es}
    ss.update({('U','H'):F(9,10),('V','H'):F(9,10),('U','V'):F(1,10),('H','W'):z})
    return list('ABCD')+['W','H','V','U','R'],pars,ss,{'H':F(1,2)}
def fourcycle():
    es=[('Q','R'),('Q','D'),('R','U'),('R','V'),('U','A'),('U','H'),('V','B'),('V','H'),('H','C')]
    pars={}
    for p,c in es:pars.setdefault(c,[]).append(p)
    ss={e:F(1,2) for e in es};ss[('R','U')]=ss[('R','V')]=F(177,200)
    return list('ABCD')+['H','U','V','R','Q'],pars,ss,{'H':F(1,2)}
def run(source,allocation):
    nodes,pars,ss,gg=source
    return law(nodes,pars,ss,allocation,gg)

if __name__=='__main__':
    a=triangle(F(9,10));b=fourcycle();base={x:1 for x in 'ABCD'}
    results={'status':'Experimental exact small-source compiler; not independently validated or empirical','channels':[]}
    for label in ['one_each']+list('ABCD'):
        alloc=base.copy()
        if label!='one_each':alloc[label]+=1
        pa=run(a,alloc);pb=run(b,alloc);ua=unroot(pa);ub=unroot(pb)
        r={'allocation':alloc,'rooted_TV':str(tv(pa,pb)),'unrooted_TV':str(tv(ua,ub)),'rooted_outcomes':len(pa),'unrooted_outcomes':len(ua)}
        if label=='one_each':
            assert ua==ub
            assert sorted(ua.values())==[F(59,200),F(141,400),F(141,400)]
            r['shared_quartet_law']={k:str(v) for k,v in ua.items()}
        results['channels'].append(r)
    print(json.dumps(results,indent=2))
