#!/usr/bin/env python3
"""Bounded exact current-root controls for the hierarchy cohort-peeling proof.

No finite run observes or proves reconstruction of the infinite hierarchy.
"""
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
from hashlib import sha256
import json,sys
from math import comb
import tomography_check as T
import obstruction_checks as F
import symmetry_orbit_checks as R
prune=R.prune

def tail(dist):
    dist=T.push(dist,lambda f:T.edge(f,Q(1,2)))
    dist=T.push(dist,lambda f:T.bigon(f,Q(2,3),Q(1,3),Q(3,5)))
    return T.push(dist,lambda f:T.edge(f,Q(2,5)))

def joint(n,m,x,y):
    A=tuple(f'A{i}' for i in range(1,n+1));B=tuple(f'B{i}' for i in range(1,m+1))
    pooled=defaultdict(Q)
    for a,p in T.edge(A,x).items():
        for b,q in T.edge(B,y).items():pooled[T.canonical(a+b)]+=p*q
    return tail(dict(pooled))

def marginal(dist,remove_labels):
    out=defaultdict(Q)
    for f,p in dist.items():
        for label in remove_labels:f=prune(f,label)
        out[f]+=p
    return dict(out)

def diagonal(dist,n,m):
    return dist.get(T.canonical([f'A{i}' for i in range(1,n+1)]+[f'B{i}' for i in range(1,m+1)]),Q(0))

def run():
    rows=[];recover=[]
    for x,y in [(Q(3,4),Q(1,4)),(Q(2,3),Q(2,3))]:
        d={};sym={}
        for n in range(5):
            for m in range(5-n):
                if not n+m:continue
                J=joint(n,m,x,y);Js=joint(n,m,y,x)
                assert sum(J.values(),Q(0))==1 and all(p>=0 for p in J.values())
                initial=T.canonical([f'A{i}' for i in range(1,n+1)]+[f'B{i}' for i in range(1,m+1)])
                s=tail({initial:Q(1)}).get(initial,Q(0))
                d[n,m]=diagonal(J,n,m);sym[n,m]=(diagonal(J,n,m)+diagonal(Js,n,m))/2
                assert d[n,m]==x**comb(n,2)*y**comb(m,2)*s
                assert sym[n,m]==(x**comb(n,2)*y**comb(m,2)+y**comb(n,2)*x**comb(m,2))/2*s
                A=tuple(f'A{i}' for i in range(1,n+1));B=tuple(f'B{i}' for i in range(1,m+1))
                assert marginal(J,B)==tail(T.edge(A,x))
                assert marginal(J,A)==tail(T.edge(B,y))
                rows.append({'arm_survivals':[str(x),str(y)],'cohort_sizes':[n,m],
                             'joint_no_merger':str(d[n,m]),'full_selected_cohort_marginals':'PASS'})
        assert d[2,0]/d[1,1]==x and d[0,2]/d[1,1]==y
        S=2*sym[2,0]/sym[1,1]
        P=(S*S-sym[3,0]/sym[2,1])/3
        assert S==x+y and P==x*y
        recover.append({'source_arms':[str(x),str(y)],'recovered_sum':str(S),'recovered_product':str(P)})
        for n in range(1,5):
            states=[f for dist in F.merger_forests(tuple(f'A{i}' for i in range(1,n+1))).values() for f in dist]
            states=sorted(states,key=lambda f:(-len(f),repr(f)));index={f:i for i,f in enumerate(states)}
            determinant=Q(1)
            for i,f in enumerate(states):
                row=defaultdict(Q)
                for z in (x,y):
                    for h,p in T.edge(f,z).items():row[h]+=p/2
                diag=(x**comb(len(f),2)+y**comb(len(f),2))/2
                assert row[f]==diag>0
                assert all(index[h]>=i for h,p in row.items() if p)
                determinant*=diag
            assert determinant>0
    return {'status':'PASS','python':sys.version,'arithmetic':'fractions.Fraction',
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'dependencies_sha256':{Path(p).name:sha256(Path(p).read_bytes()).hexdigest() for p in [T.__file__,F.__file__,R.__file__,T.verify.__file__]},
            'joint_current_root_controls':rows,'symmetric_arm_recovery':recover,
            'mixture_full_operator_checks':'positive triangular diagonal on every labelled forest through4, two source fixtures',
            'limits':['The countable positive-clade cohort identification is a hand proof, not this finite replay.',
                      'Conditional original-cohort source calculations are controls, not added physical actuator rows.',
                      'Full passive chain normal form, finite-prefix effectivity and unknown-size distinction are separate stated arguments.']}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
