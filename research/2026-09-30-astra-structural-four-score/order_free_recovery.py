"""Order-free split recovery using the classical Bandelt-Dress isolation index.

Exact rational reference implementation, not an efficient split-decomposition
algorithm. The all-split enumeration costs O(2**n * n**4) scalar operations.
No circular order enters the recovery function. The noise guarantee requires
an externally justified entrywise error bound and the theorem's target margin.
"""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, product
from hashlib import sha256
from pathlib import Path
import json
import sys


def canonical(A, X):
    A=tuple(sorted(A)); B=tuple(sorted(set(X)-set(A)))
    return min(A,B,key=lambda z:(len(z),z))


def all_splits(X):
    X=tuple(sorted(X)); n=len(X)
    if n<2 or len(set(X))!=n:
        raise ValueError('At least two distinct taxa are required.')
    # Every unoriented split has exactly one side containing X[0].
    for mask in range((1<<(n-1))-1):
        A=(X[0],)+tuple(X[i+1] for i in range(n-1) if mask&(1<<i))
        yield canonical(A,X)


def validate_matrix(D,X):
    for x in X:
        if D[x,x]!=0:raise ValueError('The diagonal must be zero.')
        for y in X:
            F(D[x,y])  # Reject values that do not have a finite rational form.
            if D[x,y]!=D[y,x]:raise ValueError('The matrix must be symmetric.')


def isolation_index(D,X,A):
    """Return I_(A|X-A)(D); repetitions within each side are intentional."""
    X=set(X);A=set(A);B=X-A
    if not A or not B or not A<=X:
        raise ValueError('A must be a nonempty proper subset of X.')
    best=None
    for a,aa in combinations_with_replacement(sorted(A),2):
        for b,bb in combinations_with_replacement(sorted(B),2):
            within=F(D[a,aa])+F(D[b,bb])
            cross1=F(D[a,b])+F(D[aa,bb])
            cross2=F(D[a,bb])+F(D[aa,b])
            value=(max(within,cross1,cross2)-within)/2
            best=value if best is None else min(best,value)
    return best


def split_indices(D,X):
    X=tuple(sorted(X));validate_matrix(D,X)
    return {A:isolation_index(D,X,A) for A in all_splits(X)}


def recover_nontrivial(D,X,margin,epsilon):
    """Threshold using a supplied true positive-weight margin and error bound.

The code checks the numerical condition, not the scientific validity of the
user-supplied margin or error bound. Under the theorem's premises, the returned
set equals the displayed nontrivial split union, without an order input.
"""
    margin,epsilon=F(margin),F(epsilon)
    if margin<=0 or epsilon<0 or 4*epsilon>=margin:
        raise ValueError('Require margin>0 and 0<=4*epsilon<margin.')
    return {A for A,w in split_indices(D,X).items()
            if len(A)>1 and w>margin/2}


def controls():
    from global_support_controls import (FIXTURES,paired_network,codes_from_graph,
        vectors,score_matrix,split_weights)
    from four_score_controls import gall
    exact=[];total=0
    params=[(0,1,F(1,2),1),(0,1,F(3,4),1),(2,5,5,5),(7,7,7,7)]
    for name,labs,tree in FIXTURES:
        net,C=paired_network(labs,tree)
        codes,support,_,_=codes_from_graph(net);VV=vectors(net,codes)
        for scores in params:
            D=score_matrix(VV,C,scores);ww=split_weights(D,C)
            # Deliberately reverse the input taxon list. Recovery sorts names,
            # but neither that ordering nor a source circle enters its formula.
            ii=split_indices(D,list(reversed(C)))
            assert len(ii)==2**(len(C)-1)-1
            for A,w in ii.items():assert w==ww.get(A,0),(name,scores,A,w,ww.get(A,0))
            assert {A for A,w in ii.items() if w>0}=={A for A,w in ww.items() if w>0}
            c,s,a,o=scores
            if a<s:
                assert recover_nontrivial(D,C,2*(s-a),0)=={A for A in support if len(A)>1}
            total+=len(ii)
            exact.append({'fixture':name,'scores':list(map(str,scores)),
                          'all_unordered_splits_checked':len(ii)})
    # Every +/-epsilon/zero perturbation of the six off-diagonal entries of a
    # four-cycle, for two positive-margin parameter vectors.
    X=['a','b','c','d'];net=gall(X,'a',{},('b','c'))
    codes,support,_,_=codes_from_graph(net);VV=vectors(net,codes)
    intended={A for A in support if len(A)>1};noise_cases=0;lip_checks=0
    for scores in ((0,1,F(1,2),1),(F(1,3),2,F(4,3),2)):
        c,s,a,o=scores;m=2*(s-a);eps=m/8
        D=score_matrix(VV,X,scores);truth=split_indices(D,X)
        for offsets in product((-1,0,1),repeat=6):
            noisy=dict(D)
            for (x,y),offset in zip(combinations(X,2),offsets):
                noisy[x,y]=noisy[y,x]=D[x,y]+eps*offset
            indices=split_indices(noisy,X)
            for A,w in indices.items():
                assert abs(w-truth[A])<=2*eps;lip_checks+=1
            assert recover_nontrivial(noisy,X,m,eps)==intended
            noise_cases+=1
    # A non-source dense circular split sum tests the purely metric lemma.
    from global_support_controls import canon
    dense=[]
    for n in (4,5,6,7):
        C=[f'T{i}' for i in range(n)];weights={}
        for i,j in combinations(range(n),2):
            weights[canon(C[i+1:j+1],C)]=F(1+((i+3*j)%5),3)
        D={(x,y):sum(w for A,w in weights.items() if (x in A)!=(y in A))
           for x in C for y in C}
        ii=split_indices(D,C)
        assert all(w==weights.get(A,0) for A,w in ii.items())
        dense.append({'taxa':n,'all_splits_checked':len(ii)})
    return {'status':'PASS_ORDER_FREE_ISOLATION_AND_NOISE_CONTROLS',
            'source_fixture_score_cases':len(exact),'source_split_indices_checked':total,
            'exact_cases':exact,'dense_circular_controls':dense,
            'exhaustive_ternary_noise_cases':noise_cases,'isolation_lipschitz_checks':lip_checks,
            'noise_radius':'one eighth of the theorem positive nontrivial weight margin',
            'novelty':'The isolation index is classical Bandelt-Dress split decomposition, not a new invention.',
            'limits':'Finite controls corroborate a separate all-size proof. Exponential reference code is not claimed computationally optimal. True observation error bounds and biological identifiability are not inferred by the program.'}


if __name__=='__main__':
    report=controls();report['python']=sys.version
    report['checker_sha256']=sha256(Path(__file__).read_bytes()).hexdigest()
    report['dependency_sha256']={f:sha256(Path(__file__).with_name(f).read_bytes()).hexdigest()
       for f in ('four_score_controls.py','global_support_controls.py')}
    Path(__file__).with_name('ORDER-FREE-EVIDENCE.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='exact_cases'},indent=2))
