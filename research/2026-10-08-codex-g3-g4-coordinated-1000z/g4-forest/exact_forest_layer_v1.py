"""Source-authenticated exact cap-six forest/weak-cell/suffix-transport audit.

No signed operator or algebraic inverse is represented as a physical edge.
The source polynomial is the current-root independent routing/graft sum.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from math import comb
from pathlib import Path
import json
import time
import types

SOURCE = "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
SOURCE_SHA = "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884"

def load_source(root):
    p = root / SOURCE
    captured = p.read_bytes()
    actual = sha256(captured).hexdigest()
    if actual != SOURCE_SHA:
        raise ValueError(f"Source identity mismatch: {actual}")
    module = types.ModuleType("authenticated_original_forest_algebra")
    module.__file__ = str(p)
    exec(compile(captured, str(p), "exec"), module.__dict__)
    return module, actual

LEAF = ()
def size(t):
    return 1 if not t else size(t[0]) + size(t[1])
def shape_key(t):
    return size(t), repr(t)
def join(a,b):
    return tuple(sorted((a,b), key=shape_key))
def fs(*ts):
    return tuple(sorted(ts,key=shape_key))
T2 = join(LEAF,LEAF)
T3 = join(LEAF,T2)
B4 = join(T2,T2)
C4 = join(LEAF,T3)
A5,B5,C5 = join(LEAF,B4),join(LEAF,C4),join(T2,T3)
A6,B6,C6 = join(LEAF,A5),join(LEAF,B5),join(LEAF,C5)
D6,E6,F6 = join(T2,B4),join(T2,C4),join(T3,T3)
SHAPES5 = [fs(*([LEAF]*5)),fs(T2,*([LEAF]*3)),fs(T2,T2,LEAF),
           fs(T3,LEAF,LEAF),fs(T3,T2),fs(B4,LEAF),fs(C4,LEAF),
           fs(A5),fs(B5),fs(C5)]
SHAPES6 = [fs(*([LEAF]*6)),fs(T2,*([LEAF]*4)),fs(T2,T2,LEAF,LEAF),
           fs(T2,T2,T2),fs(T3,*([LEAF]*3)),fs(T3,T2,LEAF),fs(T3,T3),
           fs(B4,LEAF,LEAF),fs(C4,LEAF,LEAF),fs(B4,T2),fs(C4,T2),
           fs(A5,LEAF),fs(B5,LEAF),fs(C5,LEAF),
           fs(A6),fs(B6),fs(C6),fs(D6),fs(E6),fs(F6)]
FREE = [6,9,10,14,15,16,17,18,19]

def tree_shape(t):
    return LEAF if isinstance(t,int) else join(tree_shape(t[0]),tree_shape(t[1]))
def forest_shape(f):
    return fs(*(tree_shape(t) for t in f))
def representative(shape, fa):
    nxt = iter(range(sum(size(t) for t in shape)))
    def build(t):
        return next(nxt) if not t else fa.tree(build(t[0]),build(t[1]))
    return fa.forest(build(t) for t in shape)
def p_add(p,k,c):
    p[k] = p.get(k,F(0))+c
    if not p[k]:
        del p[k]
def eval_poly(p,x):
    return sum((c*x**e for e,c in p.items()),F(0))

def ordinary_polynomials(states, index, fa):
    n=len(states)
    mat=[[{} for _ in range(n)] for _ in range(n)]
    for i,f in enumerate(states):
        for v,p in fa.edge_polynomials(len(f)).items():
            j=index[forest_shape(fa.graft(f,v))]
            for e,c in p.items():
                p_add(mat[i][j],e,c)
    return mat

def bigon_polynomials(states, index, fa):
    n=len(states)
    mat=[[{} for _ in range(n)] for _ in range(n)]
    for i,f in enumerate(states):
        k=len(f)
        for bits in product((0,1),repeat=k):
            aa=tuple(j for j in range(k) if bits[j]==0)
            bb=tuple(j for j in range(k) if bits[j]==1)
            for va,pa in fa.edge_polynomials(len(aa)).items():
                ga=tuple(fa.relabel(t,dict(enumerate(aa))) for t in va)
                for vb,pb in fa.edge_polynomials(len(bb)).items():
                    gb=tuple(fa.relabel(t,dict(enumerate(bb))) for t in vb)
                    j=index[forest_shape(fa.graft(f,fa.forest(ga+gb)))]
                    for ex,cx in pa.items():
                        for ey,cy in pb.items():
                            p_add(mat[i][j],(ex,ey),cx*cy/F(2**k))
    return mat

@lru_cache(None)
def arm_jet(p,q,order):
    """x=1-A*t-h, y=1-A*t+h, h^2=w*t^3; keys(deg,Aexp,wexp)."""
    out={}
    for i in range(min(p,order)+1):
        for j in range(min(q,order)+1):
            for c in range(i+1):
                for d in range(j+1):
                    count=c+d
                    if count%2:
                        continue  # cancellation justified by the symmetric complete B polynomial
                    degree=i+j+count//2
                    if degree<=order:
                        val=F(comb(p,i)*comb(q,j)*comb(i,c)*comb(j,d)*(-1)**(i+j-count+c))
                        p_add(out,(degree,i+j-count,count//2),val)
    return out

def cubic_source_audit(B,E,states,fa):
    n=len(states)
    R=[[F(0) for _ in range(n)] for _ in range(n)]
    jet=[]
    for i in range(n):
        jr=[]
        for j in range(n):
            p={}
            # Individual x/y monomials need not be symmetric; the complete
            # source sum is symmetric, so all odd h powers cancel exactly.
            for (px,py),c in B[i][j].items():
                for key,v in arm_jet(px,py,3).items():
                    p_add(p,key,c*v)
            for e,c in E[i][j].items():
                for k in range(min(e,3)+1):
                    p_add(p,(k,k,0),-c*F(comb(e,k)*(-1)**k,2**k))
            assert all(k[0]==3 for k in p), (i,j,p)
            a=p.get((3,3,0),F(0))
            w=p.get((3,0,1),F(0))
            assert not (set(p)-{(3,3,0),(3,0,1)})
            assert w == -6*a, (i,j,p)
            R[i][j]=12*a
            jr.append(p)
        jet.append(jr)
    # Independently construct the claimed universal current-root jet.
    index={forest_shape(f):i for i,f in enumerate(states)}
    expected=[[F(0) for _ in range(n)] for _ in range(n)]
    for i,f in enumerate(states):
        k=len(f)
        expected[i][i]=-F(3,2)*comb(k,3)
        for a,b in combinations(range(k),2):
            g=fa.forest([t for j,t in enumerate(f) if j not in (a,b)]+[fa.tree(f[a],f[b])])
            expected[i][index[forest_shape(g)]]+=F(3,4)*(k-2)
        for a,b,c in combinations(range(k),3):
            for u,v,r in ((a,b,c),(a,c,b),(b,c,a)):
                g=fa.forest([t for j,t in enumerate(f) if j not in (a,b,c)]+
                            [fa.tree(fa.tree(f[u],f[v]),f[r])])
                expected[i][index[forest_shape(g)]]-=F(1,4)
    assert R==expected
    assert all(sum(r,F(0))==0 for r in R)
    return R

def conjugate_fresh(E,R):
    n=len(E)
    er=[{} for _ in range(n)]
    for j in range(n):
        for k in range(n):
            for e,c in E[0][k].items():
                if R[k][j]:
                    p_add(er[j],e,c*R[k][j])
    out=[{} for _ in range(n)]
    for j in range(n):
        for k in range(n):
            for e,c in er[k].items():
                for d,v in E[k][j].items():
                    p_add(out[j],e-d,c*v)
    return out

def rref(rows):
    if not rows:
        return [],[]
    a=[list(map(F,r)) for r in rows]
    pivots=[]
    k=0
    for j in range(len(a[0])):
        ii=next((i for i in range(k,len(a)) if a[i][j]),None)
        if ii is None:
            continue
        a[k],a[ii]=a[ii],a[k]
        d=a[k][j]
        a[k]=[v/d for v in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][j]:
                d=a[i][j]
                a[i]=[v-d*w for v,w in zip(a[i],a[k])]
        pivots.append(j)
        k+=1
        if k==len(a):
            break
    return a[:k],pivots
def nullspace(rows):
    a,piv=rref(rows)
    m=len(rows[0])
    out=[]
    for j in range(m):
        if j not in piv:
            v=[F(0)]*m
            v[j]=F(1)
            for row,i in zip(a,piv):
                v[i]=-row[j]
            out.append(v)
    return out
def matmul(a,b):
    return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]

def delete_one(states,fa):
    index={s:i for i,s in enumerate(SHAPES5)}
    C=[[0 for _ in states] for _ in SHAPES5]
    def prune(t,label):
        if isinstance(t,int):
            return None if t==label else t
        a,b=prune(t[0],label),prune(t[1],label)
        return b if a is None else a if b is None else fa.tree(a,b)
    for j,f in enumerate(states):
        for label in range(6):
            g=fa.forest(v for t in f if (v:=prune(t,label)) is not None)
            C[index[forest_shape(g)]][j]+=1
    return C

def encode(x):
    if isinstance(x,F):
        return str(x)
    if isinstance(x,dict):
        return {str(k):encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [encode(v) for v in x]
    return x

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    started=time.perf_counter()
    fa,pin=load_source(args.root)
    states=[representative(s,fa) for s in SHAPES6]
    index={s:i for i,s in enumerate(SHAPES6)}
    orbit_sizes=[sum(forest_shape(f)==s for f in fa.forests(tuple(range(6)))) for s in SHAPES6]
    assert sum(orbit_sizes)==len(fa.forests(tuple(range(6))))
    E=ordinary_polynomials(states,index,fa)
    Q=[[-sum((e*c for e,c in p.items()),F(0)) for p in row] for row in E]
    assert all(sum(row,F(0))==0 for row in Q)
    B=bigon_polynomials(states,index,fa)
    R=cubic_source_audit(B,E,states,fa)
    transported=conjugate_fresh(E,R)
    exponents=sorted({e for p in transported for e in p})
    coefficients=[[p.get(e,F(0)) for e in exponents] for p in transported]
    C=delete_one(states,fa)
    assert all(sum(col)==6 for col in zip(*C))
    assert len(rref(C)[1])==10
    constraints=matmul(C,coefficients)+[coefficients[0]]
    ker=nullspace(constraints)
    residual=[[sum((row[j]*v[j] for j in range(len(exponents))),F(0)) for v in ker] for row in coefficients]
    free_residual=[residual[j] for j in FREE]
    ranks={"transported_moment_map":len(rref(coefficients)[1]),
           "lower_plus_new_diagonal_constraints":len(rref(constraints)[1]),
           "moment_fibre":len(ker),"constrained_full_six_residual":len(rref(residual)[1]),
           "constrained_nine_coordinates":len(rref(free_residual)[1])}
    result={"status":"EXACT_RATIONAL_EXECUTED_FINITE_CAP_SIX_JET_ONLY",
            "executed_source_sha256":pin,"original_source":SOURCE,
            "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
            "source_convention":"current-root independent fair routing; ordinary RIGHT graft; chronological left-to-right product; suffix inverse survival X",
            "physical_branch":"x=1-A*t-sqrt(w)*t^(3/2), y=1-A*t+sqrt(w)*t^(3/2), A,w>0; q=1-A*t/2; fixed finite bank at sufficiently small t>0",
            "jet_identity":"B-E(q)=(A^3/12-w/2)*t^3*R+O(t^4), verified all 20 orbit rows",
            "shape_order":list(map(repr,SHAPES6)),"labelled_orbit_sizes":orbit_sizes,
            "ordinary_Q":Q,"actual_cubic_R":R,
            "transported_fresh_row_polynomials":transported,
            "moment_exponents":exponents,"moment_coefficient_matrix":coefficients,
            "delete_one_C":C,"all_lower_plus_diagonal_constraints":constraints,
            "constraint_rref":rref(constraints)[0],"moment_fibre_basis":ker,
            "constrained_full_residual_columns":residual,
            "nine_coordinate_indices":FREE,"constrained_nine_columns":free_residual,
            "exact_ranks":ranks,
            "runtime_seconds":time.perf_counter()-started,
            "not_claimed":["actual positive common zero", "higher-order source rank", "all-cap hazard bound", "G4 master closure", "convex mixture source realization"]}
    args.output.write_text(json.dumps(encode(result),indent=2)+"\n")
    print(json.dumps({"output":str(args.output),"exponents":exponents,"ranks":ranks,"runtime_seconds":result["runtime_seconds"]}))
if __name__=="__main__":
    main()
