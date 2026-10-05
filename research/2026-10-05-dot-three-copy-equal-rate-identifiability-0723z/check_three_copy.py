#!/usr/bin/env python3
"""Exact symbolic/rational finite controls; no empirical estimator validation."""
import itertools as it
import json
from pathlib import Path
import sympy as s
Q=s.Rational

def types(p,m): return list(it.combinations_with_replacement(range(p),m))
def route(G,m):
    p,q=G.shape; out=types(q,m); rows=[]
    for alpha in types(p,m):
        row=[]
        for beta in out:
            row.append(sum(s.prod(G[alpha[i],b[i]] for i in range(m)) for b in set(it.permutations(beta))))
        assert sum(row)==1
        rows.append(row)
    R=s.Matrix(rows); assert R.rank()==len(out)
    return R

def survival(rates,m):
    return s.diag(*[Q(2)**(-sum(a.count(i)*(a.count(i)-1)//2*r for i,r in enumerate(rates))) for a in types(len(rates),m)])
def tensor(G,r,m):
    return s.Matrix([sum(s.prod(G[i,a] for i in alpha)*r[a]**(m-1) for a in range(G.cols)) for alpha in types(G.rows,m)])
def leftsolve(T,v):
    answer=(T.T*T).inv()*T.T*v
    assert T*answer==v
    return answer

def reconstruct(M2, M3):
    # Exact generalized spectral control, equivalent to the proof's whitening.
    # Only M2 and M3 enter; no supplied routing columns, rates or hidden labels.
    p=M2.rows;q=M2.rank()
    rows=next(I for I in it.combinations(range(p),q) if M2.extract(I,I).det()!=0)
    A=M2.extract(rows,rows)
    for z in it.product(range(1,q+2),repeat=q):
        B=s.Matrix(q,q,lambda i,j:sum(z[k]*M3[tuple(sorted((rows[i],rows[j],rows[k])))] for k in range(q)))
        H=B*A.inv(); eig=H.eigenvects()
        if len(eig)==q and all(mult==1 for _,mult,_ in eig):break
    else:raise AssertionError('No separating contraction on test grid')
    V=s.Matrix.hstack(*[vv[0] for _,_,vv in eig])
    # Extend eigen-directions to all old rows using the known M2 column space.
    X=M2[:,list(rows)]*A.inv()*V
    scales=leftsolve(X,s.ones(p,1))
    G=X*s.diag(*scales)
    Linv=(G.T*G).inv()*G.T
    D=s.simplify(Linv*M2*Linv.T)
    assert D==s.diag(*D.diagonal()) and all(v>0 for v in D.diagonal())
    assert all(x>=0 for x in G) and G*s.ones(q,1)==s.ones(p,1)
    rates=list(D.diagonal())
    assert tensor(G,rates,3)==s.Matrix([M3[a] for a in types(p,3)])
    return G,rates

def canonical(G,r):
    return sorted([tuple(G[:,j])+ (r[j],) for j in range(G.cols)],key=str)

Gs=[s.Matrix([[Q(3,4),Q(1,4),0],[0,1,0],[0,0,1]]),
    s.Matrix([[1,0],[Q(1,3),Q(2,3)],[0,1]]),
    s.Matrix([[Q(3,4),Q(1,4)],[Q(1,4),Q(3,4)]]),
    s.Matrix([[1],[1]])]
rates=[[1,1,1],[4,4,4],[9,9],[4,4],[1]]
Us={m:s.eye(len(types(3,m))) for m in (2,3)}
checks=0; visibility=[]
for j,G in enumerate(Gs):
    recovered={}
    for m in (2,3):
        D=survival(rates[j],m);T=Us[m]*D
        assert T.rank()==T.cols
        R=route(G,m);b=tensor(G,rates[j+1],m)
        # Forward probabilities' leading coefficients, then recovery with known T.
        observed=T*R*s.Matrix([rates[j+1][a[0]]**(m-1) if len(set(a))==1 else 0 for a in types(G.cols,m)])
        assert observed==T*b
        recovered[m]=leftsolve(T,observed)
        assert recovered[m]==b
        Us[m]=T*R; assert Us[m].rank()==Us[m].cols
        checks+=1
    M2=s.Matrix(G.rows,G.rows,lambda a,b:recovered[2][types(G.rows,2).index(tuple(sorted((a,b))))])
    M3=dict(zip(types(G.rows,3),recovered[3]))
    Gh,rh=reconstruct(M2,M3)
    assert canonical(Gh,rh)==canonical(G,rates[j+1]);checks+=1
    old=s.Matrix([rates[j][a] if a==b else 0 for a,b in types(G.rows,2)])
    visibility.append(recovered[2]!=old);assert visibility[-1]

# Multinomial normalizations and complete-three merger coefficient.
g=Q(1,3); R=route(s.Matrix([[g,1-g],[0,1]]),3)
assert R[0,types(2,3).index((0,0,1))]==3*g*g*(1-g)
x,r=s.symbols('x r',positive=True)
F=1-Q(3,2)*s.exp(-r*x)+Q(1,2)*s.exp(-3*r*x)
assert s.limit(F/x**2,x,0)==Q(3,2)*r*r

# Equal-rate pair tensor alone admits different positive row-stochastic factors.
# A rational orthogonal matrix fixing ones rotates a sufficiently interior G.
v=s.Matrix([1,-1,0]); O=s.eye(3)-2*v*v.T/(v.T*v)[0] # permutation control first
assert O*s.ones(3,1)==s.ones(3,1)
u=s.Matrix([1,1,-2]); O=s.eye(3)-2*u*u.T/(u.T*u)[0]
G=s.Matrix([[Q(1,2),Q(1,4),Q(1,4)],[Q(1,4),Q(1,2),Q(1,4)],[Q(1,4),Q(1,4),Q(1,2)]])
H=G*O
assert O*O.T==s.eye(3) and O*s.ones(3,1)==s.ones(3,1)
assert min(H)>=0 and H*s.ones(3,1)==s.ones(3,1) and H.det()!=0
assert G*G.T==H*H.T
assert tensor(G,[1]*3,3)!=tensor(H,[1]*3,3)
assert canonical(G,[1]*3)!=canonical(H,[1]*3)

bounds={}
for J,P in [(1,2),(4,3)]:
    S=5*P**3; F=J*S*S+S; M=13*(39*S)**J
    bounds[f'J{J}_P{P}']=16*(2*M*(2*F+1)-1)
result={'status':'PASS','arithmetic':'SymPy exact rational/symbolic, no numerical tolerances',
'boundary_count':4,'pair_triple_transfer_and_tensor_reconstruction_checks':checks,
'all_nonroot_test_epochs_have_coincident_rates':True,'boundary_visibility':visibility,
'factor_three_over_two_verified':True,'multinomial_triple_normalization_verified':True,
'equal_rate_pair_tensor_ambiguity_separated_by_triple_tensor':True,
'finite_bridge_bounds':bounds,
'limits':'Finite controls support the proof; they do not prove all-model identifiability, noisy-data recovery, minimal sampling, novelty or Lean verification.'}
text=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('CONTROL-RESULTS.json').write_text(text)
print(text,end='')
