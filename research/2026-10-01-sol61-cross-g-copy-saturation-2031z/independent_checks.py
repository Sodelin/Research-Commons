"""Independent finite controls for the all-copy calendar boundary proof.

Standard library only. No author code or expected output is imported.
Arbitrary n,m are proved in PROOF.md; these controls are not extrapolation.
"""
from functools import lru_cache
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import hashlib, json, sys, time

START = time.perf_counter()

@lru_cache(None)
def rooted_trees(labels):
    if len(labels) == 1:
        return (labels[0],)
    ans = []
    rest = labels[1:]
    for mask in range(1 << len(rest)):
        left = (labels[0],) + tuple(x for i,x in enumerate(rest) if mask >> i & 1)
        right = tuple(x for i,x in enumerate(rest) if not mask >> i & 1)
        if not right:
            continue
        for a in rooted_trees(left):
            for b in rooted_trees(right):
                ans.append((a,b))
    return tuple(ans)

def tree_graph(tree):
    edges, ages = [], {}
    def walk(t):
        if isinstance(t,str):
            ages[t] = F(0)
            return t
        a,b = (walk(s) for s in t)
        v = 'v'+str(len(ages))
        ages[v] = max(ages[a],ages[b])+1
        edges.extend([(v,a),(v,b)])
        return v
    root=walk(tree)
    rates={e:F(i+2,i+3) for i,e in enumerate(edges)}
    return tuple(edges), ages, rates, root

def reach(edges,start,blocked=None,undirected=False):
    todo=[start]; seen=set()
    while todo:
        x=todo.pop()
        if x in seen or x == blocked:
            continue
        seen.add(x)
        for u,v in edges:
            if u==x and v!=blocked:
                todo.append(v)
            if undirected and v==x and u!=blocked:
                todo.append(u)
    return seen

def splits(edges,labels):
    X=frozenset(labels); ans=set()
    for j,(u,v) in enumerate(edges):
        side=frozenset(reach(edges[:j]+edges[j+1:],u,undirected=True)) & X
        other=X-side
        if len(side)>=2 and len(other)>=2:
            ans.add(frozenset((side,other)))
    return ans

def insert(edges,ages,rates,a,b):
    pa=next(u for u,v in edges if v==a)
    pb=next(u for u,v in edges if v==b)
    u=min(ages[pa],ages[pb]); h=u/3; d=2*u/3
    new=tuple(e for e in edges if e not in ((pa,a),(pb,b)))+((pa,'@D'),('@D',a),(pb,'@H'),('@H',b),('@D','@H'))
    na={**ages,'@D':d,'@H':h}
    nr={e:r for e,r in rates.items() if e not in ((pa,a),(pb,b))}
    nr.update({(pa,'@D'):rates[pa,a],('@D',a):rates[pa,a],(pb,'@H'):rates[pb,b],('@H',b):rates[pb,b],('@D','@H'):F(7,5)})
    return new,na,nr,(pa,pb,h,d)

def audit_source(edges,ages,rates,root,labels):
    V=set(ages); assert set(reach(edges,root))==V
    assert all(ages[u]>ages[v] and rates[u,v]>0 for u,v in edges)
    indeg={v:sum(y==v for x,y in edges) for v in V}
    outdeg={v:sum(x==v for x,y in edges) for v in V}
    for v in V:
        want=(0,2) if v==root else (1,0) if v in labels else (2,1) if v=='@H' else (1,2)
        assert (indeg[v],outdeg[v])==want
    assert len(edges)-len(V)+1==1 # exact unicyclic outerplanarity gate
    # The recipient is supplied separately by the sole hybrid child.
    b=next(v for u,v in edges if u=='@H')
    without=tuple(e for e in edges if e!=('@H',b))
    assert b not in reach(without,'@H',undirected=True)
    X=set(labels)
    for v in V-{root}:
        assert not X.isdisjoint(reach(edges,root,blocked=v))

source_count=0; tree_counts={}; early_rates=0; unchanged_target_controls=0
for n in (4,5):
    labels=tuple(chr(65+i) for i in range(n))
    ts=rooted_trees(labels); tree_counts[str(n)]=len(ts)
    for t in ts:
        e,ages,rates,r=tree_graph(t); original=splits(e,labels)
        for a,b in permutations(labels,2):
            sigma=frozenset((frozenset((a,b)),frozenset(set(labels)-{a,b})))
            ne,na,nr,(pa,pb,h,d)=insert(e,ages,rates,a,b)
            audit_source(ne,na,nr,r,labels)
            dominant=tuple(x for x in ne if x!=('@D','@H'))
            rare=tuple(x for x in ne if x!=(pb,'@H'))
            assert splits(dominant,labels)==original
            assert nr[pa,'@D']==nr['@D',a]==rates[pa,a]
            assert nr[pb,'@H']==nr['@H',b]==rates[pb,b]
            # Exact equal-rate semigroup coordinate: old hazard equals two pieces.
            assert nr[pa,'@D']*(na[pa]-d)+nr['@D',a]*d==rates[pa,a]*ages[pa]
            assert nr[pb,'@H']*(na[pb]-h)+nr['@H',b]*h==rates[pb,b]*ages[pb]
            target=original | splits(rare,labels)
            if sigma not in original:
                assert sigma in target and target>original
                tstar=(d+min(ages[pa],ages[pb]))/2
                assert h<d<tstar<min(ages[pa],ages[pb])
                early_rates+=1
            else:
                unchanged_target_controls+=1
            source_count+=1

# Rooted nonsibling is not the correct absent-unrooted-cherry condition.
e,age,rate,r=tree_graph(('A',('B',('C','D'))))
ab=frozenset((frozenset(('A','B')),frozenset(('C','D'))))
assert ab in splits(e,tuple('ABCD'))
assert next(u for u,v in e if v=='A')!=next(u for u,v in e if v=='B')

@lru_cache(None)
def count_polynomials(m):
    """P(K_m(t)=k) as exact polynomials in x=exp(-rho*t)."""
    lam=lambda k:k*(k-1)//2
    ans={m:{lam(m):F(1)}}
    for k in range(m-1,0,-1):
        q={j:F(lam(k+1))*a/F(lam(k)-j) for j,a in ans[k+1].items()}
        q[lam(k)]=-sum(q.values())
        ans[k]=q
    return ans

def evaluate(poly,x):
    return sum(a*x**j for j,a in poly.items())

kingman_cases=0; route_cases=0; max_sample=36; saturation=[]
for m in range(1,max_sample+1):
    polys=count_polynomials(m)
    for z in (F(1,4),F(1,2),F(3,4),F(9,10)):
        # x=z^2 makes exp(-rho*h/2)=z rational.
        law={k:evaluate(q,z*z) for k,q in polys.items()}
        assert all(p>=0 for p in law.values()) and sum(law.values())==1
        mean=sum(k*p for k,p in law.items())
        sharp_comparison=1/(1-(1-F(1,m))*z)
        C=1/(1-z)
        assert mean<=sharp_comparison<=C
        if z==F(1,2) and m in (1,2,4,8,16,36):
            saturation.append({'copies':m,'mean_live_ancestors':float(mean),'uniform_bound':str(C)})
        for eps in (F(1,100),F(1,10),F(1,2)):
            rare_mass=sum(p*(1-(1-eps)**k) for k,p in law.items())
            assert rare_mass<=eps*mean<=eps*C
            route_cases+=1
        kingman_cases+=1

# Exact stopped-path submeasure/Jensen controls on finite random exposures.
# Algebraic weighted event mass is the precise dominant-path probability.
submeasure_cases=0
for p in (F(3,4),F(9,10),F(99,100)):
    for eps in (F(1,100),F(1,10),F(1,2)):
        for a,b in ((1,2),(2,7),(4,19)):
            weighted=(p/3)*(1-eps)**a+(2*p/3)*(1-eps)**b
            exposure=p*(F(a,3)+F(2*b,3))
            # Numeric convexity control only; the proof uses exact Jensen.
            import math
            rhs=float(p)*math.exp(math.log(float(1-eps))*float(exposure/p))
            assert float(weighted)+1e-14>=rhs
            submeasure_cases+=1

result={'status':'PASS','python':sys.version.split()[0],
 'exhaustive_labelled_rooted_tree_counts':tree_counts,
 'all_ordered_leaf_insertions_source_checked':source_count,
 'absent_unrooted_cherry_strict_target_enlargements':early_rates,
 'already_present_cherry_controls':unchanged_target_controls,
 'rooted_nonsibling_unrooted_cherry_negative_control':True,
 'exact_Kingman_distribution_cases':kingman_cases,'largest_starting_copy_count':max_sample,
 'exact_independent_rare_routing_bound_cases':route_cases,
 'finite_weighted_dominant_path_Jensen_controls':submeasure_cases,
 'saturation_examples':saturation,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'seconds':time.perf_counter()-START,
 'limits':'Finite exact controls plus numeric Jensen sanity cases. PROOF.md establishes all-size results. No full calendar density compiler, global catalogue, empirical experiment, Lean verification, historical novelty certification or general G7 optimum.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
