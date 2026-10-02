"""Exact controls for the candidate two-position M4 full-block assembly.
The decoder sees only partition supports on <=3 original labels.
"""
import json,random,platform
from itertools import combinations,product
from collections import defaultdict
from pathlib import Path
import nonplanar_calendar_q_checks as source

def subsets(xs,minsize=1,maxsize=None):
    return [frozenset(c) for k in range(minsize,min(len(xs),maxsize or len(xs))+1) for c in combinations(xs,k)]

def partitions(domains,labels):
    out=set()
    for choices in product(*(domains[b] for b in labels)):
        blocks=defaultdict(list)
        for b,q in zip(labels,choices):blocks[q].append(b)
        out.add(frozenset(frozenset(x) for x in blocks.values()))
    return out

class Observation:
    def __init__(self,B,loader):self.B=tuple(B);self.loader=loader;self.cache={};self.jcache={}
    def H(self,U):
        U=frozenset(U);assert 1<=len(U)<=3
        if U not in self.cache:self.cache[U]=self.loader(tuple(sorted(U)))
        return self.cache[U]
    def joint(self,U):return frozenset((frozenset(U),)) in self.H(U)
    def exact(self,D,O):
        D,O=frozenset(D),frozenset(O);key=(D,O)
        if key not in self.jcache:self.jcache[key]=any(D in p for p in self.H(D|O))
        return self.jcache[key]
    def possible(self,C):
        C=frozenset(C);outside=tuple(b for b in self.B if b not in C)
        if not all(self.joint(U) for U in subsets(tuple(sorted(C)),maxsize=3)):return False
        return all(self.exact(D,O) for D in subsets(tuple(sorted(C)),maxsize=2)
                   for O in [frozenset()]+subsets(outside,maxsize=2) if len(D)+len(O)<=3)
    def sure(self,C):
        C=frozenset(C);outside=set(self.B)-C
        return all(all(frozenset((a,b)) in p for p in self.H((a,b))) for a,b in combinations(C,2)) and all(
            all(frozenset((a,b)) not in p for p in self.H((a,b))) for a in C for b in outside)

def abstract_cases():
    count=0;blocks=0;rng=random.Random(271828)
    options=[frozenset((i,)) for i in range(3)]+[frozenset(x) for x in combinations(range(3),2)]
    cases=[]
    for n in range(1,6):cases.extend((n,ds) for ds in product(options,repeat=n))
    opts5=[frozenset((i,)) for i in range(5)]+[frozenset(x) for x in combinations(range(5),2)]
    for n in range(6,10):cases.extend((n,tuple(rng.choice(opts5) for _ in range(n))) for _ in range(50))
    for n,ds in cases:
        B=tuple(str(i) for i in range(n));domains=dict(zip(B,ds))
        obs=Observation(B,lambda U:partitions(domains,U));truth=partitions(domains,B)
        possible=set.union(*(set(p) for p in truth));sure=set.intersection(*(set(p) for p in truth))
        for C in subsets(B):
            assert obs.possible(C)==(C in possible)
            assert obs.sure(C)==(C in sure)
            blocks+=1
        count+=1
    return count,blocks

def observed_chronology(G,hs,A,ages,mode):
    B=tuple(A);groups={b:frozenset((b,)) for b in B};s=0
    grid=sorted(set(ages.values()));recorded={frozenset((b,)) for b in A}|{frozenset(A)}
    stages=0;cartesian=0
    while len(B)>1:
        for tau in (t for t in grid if t>=s):
            obs=Observation(B,lambda U:source.support(G,hs,U,tau,ages,mode))
            sure={C for C in subsets(B,minsize=2) if obs.sure(C)}
            if sure:break
        else:raise AssertionError('no attained sure block from pair observations')
        for t in (t for t in grid if s<=t<=tau):
            obs=Observation(B,lambda U:source.support(G,hs,U,t,ages,mode))
            actual=source.support(G,hs,B,t,ages,mode)
            domains={b:{source.populations(p,t,ages) for p in source.paths(G,b)} for b in B}
            assert all(1<=len(S)<=2 for S in domains.values())
            assert partitions(domains,B)==actual;cartesian+=1
            blocks={C for C in subsets(B) if obs.possible(C)}
            assert blocks==set.union(*(set(p) for p in actual))
            for C in blocks:recorded.add(frozenset().union(*(groups[b] for b in C)))
        new=dict(groups)
        for block in sure:
            b=min(block);new[b]=frozenset().union(*(groups[x] for x in block))
            for x in block-{b}:del new[x]
        groups=new;B=tuple(sorted(new));s=tau;stages+=1
        assert stages<=len(A)-1
    return recorded,stages,cartesian

def main():
    count,blocks=abstract_cases();actual=0;cartesian=0;position_tests=0
    for cherry in (False,True):
        edges,leaves,ages=source.source(cherry);G,hs=source.audit(edges,leaves,ages)
        for b in leaves:
            for t in sorted(set(ages.values())):
                positions={source.populations(p,t,ages) for p in source.paths(G,b)}
                assert 1<=len(positions)<=2;position_tests+=1
        truth={frozenset((b,)) for b in leaves}|{frozenset(leaves)}
        for t in sorted(set(ages.values())):
            for p in source.support(G,hs,leaves,t,ages,'common'):truth.update(p)
        for mode in ('common','independent'):
            recovered,_,checks=observed_chronology(G,hs,leaves,ages,mode)
            assert recovered==truth
            actual+=1;cartesian+=checks
    report={'status':'PASS','abstract_position_families':count,'exact_block_and_sure_block_tests':blocks,
            'nonplanar_original_tip_age_two_position_tests':position_tests,
            'nonplanar_full_X_M3_assembly_cases':actual,'safe_stage_Cartesian_support_tests':cartesian,
            'versions':{'python':platform.python_version(),'networkx':source.nx.__version__},
            'limits':'Finite corroboration only; source blob route and local-to-global theorems require independent hand review. No universal law estimator or supplied hidden-population interface.'}
    Path(__file__).with_name('m4-split-assembly-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
