#!/usr/bin/env python3
"""Exact source-derived forest identities recovering an unknown trailing pad.

The all-copy leading-pad atom argument is a separate hand proof.
"""
from pathlib import Path
from itertools import combinations
from math import comb
from hashlib import sha256
import sys,json
import sympy as S
import obstruction_checks as F
import known_placement_six_checks as K
x,y,g=K.x,K.y,K.g

def count_data(n):
    V=S.zeros(n)
    for j in range(1,n+1):
        V[j-1,j-1]=1
        for k in range(j+1,n+1):
            V[k-1,j-1]=V[k-2,j-1]*S.Rational(comb(k,2),comb(k,2)-comb(j,2))
    B=S.Matrix([[K.row_count(k,j) if j<=k else 0 for j in range(1,n+1)] for k in range(1,n+1)])
    H=(V.inv()*B*V).applyfunc(S.expand)
    return V,H

def forest_data(n):
    states=[f for d in F.merger_forests(tuple(f'A{i}' for i in range(1,n+1))).values() for f in d]
    reps={K.orbit(f):f for f in states}
    labels=sorted(reps,key=lambda o:(-len(o),repr(o))); index={o:i for i,o in enumerate(labels)}
    Q=S.zeros(len(labels));B=S.zeros(len(labels))
    for o in labels:
        i=index[o];f=reps[o];k=len(f);Q[i,i]=-comb(k,2)
        for a,b in combinations(range(k),2):
            target=F.canonical([f[t] for t in range(k) if t not in(a,b)]+[F.join(f[a],f[b])])
            Q[i,index[K.orbit(target)]]+=1
        roots=tuple(f'R{i}' for i in range(k));mapping=dict(zip(roots,f))
        def graft(t):
            return mapping[t] if isinstance(t,str) else F.join(graft(t[0]),graft(t[1]))
        for d in F.merger_forests(roots).values():
            for h in d:
                target=F.canonical(graft(t) for t in h)
                B[i,index[K.orbit(target)]]+=K.bare(K.orbit(h))
    B=B.applyfunc(S.expand)
    I=S.eye(len(labels));projectors={}
    for j in range(1,n+1):
        P=I
        for k in range(1,n+1):
            if k!=j:P=P*(Q+comb(k,2)*I)/(comb(k,2)-comb(j,2))
        projectors[j]=P
        assert P*Q==-comb(j,2)*P and P*P==P
    assert sum(projectors.values(),S.zeros(len(labels)))==I
    for i in projectors:
        for j in projectors:
            if i!=j:assert projectors[i]*projectors[j]==S.zeros(len(labels))
    for i,o in enumerate(labels):
        for j in range(1,len(o)+1):
            assert S.expand(sum(B[i,k] for k,p in enumerate(labels) if len(p)==j)-K.row_count(len(o),j))==0
    phi=(projectors[n][0,:]*B).applyfunc(S.expand)
    vectors={j:(phi*projectors[j]).applyfunc(S.expand) for j in range(1,n)}
    return labels,Q,projectors,vectors,len(states)

def run():
    V,H=count_data(6)
    labels5,Q5,P5,v5,N5=forest_data(5)
    comb5=(('*',('*',('*',('*','*')))),)
    triple5=('*','*',('*',('*','*')))
    beta53=H[4,2]
    assert S.expand(v5[1][labels5.index(comb5)]-S.Rational(7,6)*beta53)==0
    assert S.expand(v5[3][labels5.index(triple5)]-4*beta53)==0
    labels,Q,P,v,N=forest_data(6)
    A=H[5,1];B=H[5,3]
    sigma_shape=('*','*',('*',('*',('*','*'))))
    C=v[3][labels.index(sigma_shape)]
    basis=[A,B,C]
    d=[S.Poly(p,x,y,g).as_dict() for p in basis]
    monos=sorted(set().union(*(p.keys() for p in d))); selected=[];rows=[]
    for m in monos:
        row=[p.get(m,0) for p in d]
        if S.Matrix(rows+[row]).rank()>len(rows):rows.append(row);selected.append(m)
        if len(rows)==3:break
    M=S.Matrix(rows);assert M.rank()==3;inv=M.inv();coeffs={}
    for j in v:
        coeffs[j]=[]
        for k in range(len(labels)):
            p=S.Poly(v[j][k],x,y,g).as_dict()
            c=list(inv*S.Matrix([p.get(m,0) for m in selected]))
            assert S.expand(v[j][k]-sum(a*b for a,b in zip(c,basis)))==0
            coeffs[j].append(c)
    completed=[i for i,o in enumerate(labels) if len(o)==1]
    first3=completed[:3];M1=S.Matrix([coeffs[1][i] for i in first3])
    expected=S.Matrix([[S.Rational(28,15),-S.Rational(24,25),S.Rational(2,3)],
                       [S.Rational(14,15),-S.Rational(37,25),S.Rational(1,3)],
                       [S.Rational(14,5),S.Rational(64,25),-1]])
    assert M1==expected and M1.det()==S.Rational(56,15)
    inverse=S.Matrix([[S.Rational(47,280),S.Rational(1,5),S.Rational(5,28)],
                      [S.Rational(1,2),-1,0],[S.Rational(7,4),-2,-S.Rational(1,2)]])
    assert inverse*M1==S.eye(3)
    return {'status':'PASS','python':sys.version,'sympy':S.__version__,
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependencies_sha256':{Path(p).name:sha256(Path(p).read_bytes()).hexdigest() for p in [F.__file__,K.__file__]},
        'source_variables':'0<x,y,g<1; pads 0<a,b<1; current-root independent routing and subtree grafting',
        'five':{'forest_orbits':len(labels5),'labelled_forests':N5,'comb_shape':repr(comb5),
                'three_root_shape':repr(triple5),'block51_comb':'(7/6) beta53','block53_triple':'4 beta53',
                'b_cube_formula':'(7/24) observed_block53_triple / observed_block51_comb'},
        'six':{'forest_orbits':len(labels),'labelled_forests':N,'basis':['beta62','beta64','sigma'],
               'sigma_shape':repr(sigma_shape),'sigma_polynomial':str(S.factor(C)),
               'beta62_polynomial':str(S.factor(A)),'beta64_polynomial':str(S.factor(B)),
               'count_eigenbasis':[[str(c) for c in row] for row in V.tolist()],
               'completed_first_three_shapes':[repr(labels[i]) for i in first3],
               'completed_matrix':[[str(c) for c in row] for row in M1.tolist()],
               'completed_matrix_determinant':'56/15',
               'completed_inverse':[[str(c) for c in row] for row in inverse.tolist()],
               'all_spectral_blocks':{str(j):[{'shape':repr(labels[k]),'coefficients':[str(c) for c in coeffs[j][k]]}
                     for k in range(len(labels)) if any(c!=0 for c in coeffs[j][k])] for j in v}},
        'exact_controls':['Every source complete-forest row aggregates to the independent current-root count transition.',
                          'All root-count projectors are exact rational orthogonal idempotents with the correct eigenvalue.',
                          'Every five/six displayed source identity holds as a polynomial in x,y,g.',
                          'Six-root completed three-coordinate matrix and explicit inverse multiply to identity.'],
        'limits':['The positive four-mode nonvanishing theorem is inherited from uniform_placement_six_checks.py and its full source proof.',
                  'The pad spectral-scaling and graft/tomography argument is a hand proof, not this algebraic replay.',
                  'This certifies a trailing-pad component without supplied bare parameters; it does not by itself recover leading pad or bare source.',
                  'No general same-length multicell stopping theorem is claimed.']}

if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
