"""Independent standard-library-only review. No contributor imports or data reads."""
from itertools import product, combinations
from collections import Counter, defaultdict, deque
from fractions import Fraction
import json, hashlib, pathlib, platform
X=tuple('abcfz')

def source(star):
    # Independently transcribed from the prose source specification.
    children={'O':['R','z'],'R':['A','D'],'A':['Ha','Hb']}
    age=dict(O=16,R=14,D=8,Ha=2,Hb=2,Hc=2,Hf=2,**{x:0 for x in X})
    if star:
        children.update(D=['S','DC'],S=['F','SC'],F=['Ha','Hb'],DC=['Hc','Hf'],SC=['Hc','Hf'])
        age.update(A=8,S=6,DC=5,F=4,SC=5)
    else:
        children.update(D=['B','C'],B=['Ha','BC'],C=['Hb','CC'],BC=['Hc','Hf'],CC=['Hc','Hf'])
        age.update(A=4,B=6,C=6,BC=5,CC=5)
    children.update({ 'H'+x:[x] for x in 'abcf'})
    edges=[(u,v) for u,vs in children.items() for v in vs]
    parents=defaultdict(list)
    for u,v in edges: parents[v].append(u)
    return children,age,edges,parents

def path(x,parent):
    out=[x]
    while x!='O': x=parent[x];out.append(x)
    return out

def connected(edges,start):
    adj=defaultdict(set)
    for u,v in edges:adj[u].add(v);adj[v].add(u)
    seen={start}; todo=[start]
    while todo:
        for y in adj[todo.pop()]-seen:seen.add(y);todo.append(y)
    return seen

def run(star):
    children,age,edges,parents=source(star)
    assert len(age)==17 and len(edges)==20 and len(set(edges))==20
    assert set(age)==set(children)|set(X)
    assert all(age[u]>age[v] for u,v in edges) # DAG too
    reach={'O'}
    for u in sorted(age,key=age.get,reverse=True):
        if u in reach: reach.update(children.get(u,[]))
    assert reach==set(age)
    for v in age:
        assert (len(parents[v]),len(children.get(v,[])))==((0,2) if v=='O' else (1,0) if v in X else (2,1) if v.startswith('H') else (1,2))
    for x in 'abcf':
        assert x not in connected([e for e in edges if e!=('H'+x,x)],'O')
    # Since O has a direct z child and others descend R, O is LSA.
    assert parents['z']==['O'] and children['O']==['R','z']
    laws={''.join(p):Counter() for p in combinations(X,2)}
    clusters=set();splits=set();quartets=set();trees=[]
    for bits in product((0,1),repeat=4):
        parent={v:ps[0] for v,ps in parents.items() if ps}
        for x,b in zip('abcf',bits): parent['H'+x]=parents['H'+x][b]
        paths={x:path(x,parent) for x in X}
        retained=list((p,v) for v,p in parent.items())
        cs=set()
        for u,v in retained:
            c=''.join(x for x in X if v in paths[x])
            if c:cs.add(c)
            # Compute actual edge cut, separately from ancestry clusters.
            comp=connected([e for e in retained if e!=(u,v)],v)
            a=''.join(x for x in X if x in comp);b=''.join(x for x in X if x not in comp)
            if min(len(a),len(b))>=2:splits.add('|'.join(sorted((a,b))))
        cs.add(''.join(X));clusters.update(cs)
        d={}
        for x,y in combinations(X,2):
            anc=next(v for v in paths[x] if v in paths[y])
            laws[x+y][age[anc]]+=Fraction(1,16)
            # All common ancestors form a shared suffix, hence meeting permanent.
            assert paths[x][paths[x].index(anc):]==paths[y][paths[y].index(anc):]
            d[frozenset((x,y))]=paths[x].index(anc)+paths[y].index(anc)
        # Unit-edge distances on actual switched trees identify displayed quartets.
        for a,b,c,d0 in combinations(X,4):
            pairs=[((a,b),(c,d0)),((a,c),(b,d0)),((a,d0),(b,c))]
            vals=[sum(d[frozenset(p)] for p in ps) for ps in pairs]
            lo=min(vals);assert vals.count(lo)==1
            assert sorted(vals)[1]==sorted(vals)[2]
            quartets.add('|'.join(sorted(''.join(p) for p in pairs[vals.index(lo)])))
        trees.append(cs)
    return laws,clusters,splits,quartets

a,b=run(False),run(True)
assert a[0]==b[0]
assert b[1]-a[1]=={'abc','abf'} and not a[1]-b[1]
assert b[2]-a[2]=={'abc|fz','abf|cz'} and not a[2]-b[2]
assert a[3]==b[3]
expected={'ab':{4:Fraction(1,4),8:Fraction(1,4),14:Fraction(1,2)},'cf':{5:Fraction(1,2),8:Fraction(1,2)}}
for p in ['ac','af','bc','bf']:expected[p]={6:Fraction(1,4),8:Fraction(1,4),14:Fraction(1,2)}
for p in ['az','bz','cz','fz']:expected[p]={16:Fraction(1)}
assert a[0]==expected
report={'verdict':'PASS','reviewer':'dot independent G5 minimality reviewer 0244Z','python':platform.python_version(),'original_sources':2,'switchings_per_source':16,'pair_switching_cases':320,'all_ten_exact_meeting_measures':{p:{str(t):str(w) for t,w in sorted(m.items())} for p,m in a[0].items()},'star_only_clusters':sorted(b[1]-a[1]),'star_only_splits':sorted(b[2]-a[2]),'equal_quartet_union':sorted(a[3]),'quartet_count':len(a[3]),'code_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'limits':'Finite checks corroborate independent shifted-Exp(1) analytic proof; no full Lean proof or Q lower bound.'}
print(json.dumps(report,indent=2))
