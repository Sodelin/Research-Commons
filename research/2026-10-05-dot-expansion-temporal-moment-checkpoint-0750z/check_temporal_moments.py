#!/usr/bin/env python3
"""Exact source-event coefficients and finite positive-moment recovery controls."""
import itertools as it
import math
from functools import lru_cache
from pathlib import Path
import json
import sympy as s
Q=s.Rational

def multi(d,n):
    if d==1:yield (n,);return
    for k in range(n+1):
        for z in multi(d-1,n-k):yield (k,)+z

def hcomplete(xs,n):
    h=[1]+[0]*n
    for x in xs:
        for j in range(1,n+1):h[j]+=x*h[j-1]
    return h[n]
def C(m,j):
    cs=[math.comb(k,2) for k in range(2,m+1)]
    return (-1)**j*Q(math.prod(cs)*hcomplete(cs,j),math.factorial(m-1+j))
@lru_cache(None)
def phase_coefficient(m,j,r):
    # Independent pure-death matrix coefficient, state indices lineages-1.
    A=s.zeros(m)
    for k in range(2,m+1):
        lam=math.comb(k,2)*r; A[k-1,k-1]=-lam;A[k-1,k-2]=lam
    n=m-1+j
    return (A**n)[m-1,0]/math.factorial(n)

def poly_mul(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items():
            key=tuple(u+v for u,v in zip(i,j));out[key]=out.get(key,0)+x*y
    return out

def recover(mu,d,P):
    # Only observable moments and bound P enter this generic projection Prony.
    best=None
    for t in range((d-1)*P*(P-1)//2+1):
        v=[t**j for j in range(d)];lin={tuple(int(i==j) for i in range(d)):v[j] for j in range(d)}
        polys=[{(0,)*d:1}]
        for k in range(2*P):polys.append(poly_mul(polys[-1],lin))
        moms=[sum(c*mu[a] for a,c in po.items()) for po in polys]
        H=s.Matrix(P+1,P+1,lambda i,j:moms[i+j]);q=H.rank()
        if best is None or q>best[0]:best=(q,polys,moms)
    q,polys,moms=best
    H=s.Matrix(q,q,lambda i,j:moms[i+j])
    co=H.inv()*s.Matrix([-moms[q+i] for i in range(q)])
    z=s.symbols('z');roots=s.roots(z**q+sum(co[i]*z**i for i in range(q)))
    assert len(roots)==q and all(m==1 for m in roots.values())
    zs=list(roots);V=s.Matrix(q,q,lambda i,j:zs[j]**i)
    ws=V.inv()*s.Matrix(moms[:q]);assert all(w>0 for w in ws)
    coords=[]
    for j in range(d):
        obs=[]
        for po in polys[:q]:
            obs.append(sum(c*mu[tuple(v+int(k==j) for k,v in enumerate(a))] for a,c in po.items()))
        vals=V.inv()*s.Matrix(obs);coords.append([vals[i]/ws[i] for i in range(q)])
    return [(tuple(coords[j][i] for j in range(d)),ws[i]) for i in range(q)]

models=[(s.Matrix([[Q(1,4),Q(1,4),Q(1,2)]]),[2,2,1]),
(s.Matrix([[Q(1,6),Q(1,6),Q(1,3),Q(1,3)],[Q(1,4)]*4]),[3,3,2,5]),
(s.Matrix([[Q(1,4),Q(1,4),Q(1,2)],[Q(1,4),Q(1,4),Q(1,2)]]),[1,2,2])]
coefficient_checks=0;moment_checks=0;recovered_counts=[]
for G,rs in models:
    p,P=G.shape; T={}
    for m in range(2,2*P+3):
        for j in range(2*P-m+3):
            c=C(m,j);assert c!=0
            for r in set(rs):
                assert phase_coefficient(m,j,r)==c*r**(m-1+j);coefficient_checks+=1
            for alpha in multi(p,m):
                # Coefficient of the actual completion event divided by C(m,j).
                obs=sum(s.prod(G[i,a]**alpha[i] for i in range(p))*phase_coefficient(m,j,rs[a]) for a in range(P))
                T[alpha,j]=obs/c
    mu={}
    for degree in range(2*P+1):
        for ind in multi(p+1,degree):
            alpha,temporal=ind[:-1],ind[-1]
            val=0
            for i,j in it.product(range(p),repeat=2):
                aa=tuple(v+int(k==i)+int(k==j) for k,v in enumerate(alpha))
                val+=T[aa,temporal]
            mu[ind]=val
            expected=0
            for a in range(P):
                atom=[rs[a]*G[i,a] for i in range(p)]+[rs[a]]
                mass=sum(atom[:-1])**2/rs[a]
                expected+=mass*s.prod(x**n for x,n in zip(atom,ind))
            assert val==expected;moment_checks+=1
    atoms=recover(mu,p+1,P);cols=[]
    for atom,w in atoms:
        aa,r=atom[:-1],atom[-1]; multiplicity=s.simplify(w*r/sum(aa)**2)
        assert multiplicity.is_Integer and multiplicity>0
        col=tuple(x/r for x in aa)+(r,)
        cols += [col]*int(multiplicity)
    truth=[tuple(G[:,a])+(rs[a],) for a in range(P)]
    assert sorted(cols,key=str)==sorted(truth,key=str)
    recovered_counts.append({'input_populations':p,'output_populations':P,'routing_rank':G.rank(),'distinct_joint_atoms':len(atoms),'recovered_multiplicity_total':len(cols)})

# Leading tensors fail for all m by exact formula; temporal index resolves.
for m in range(2,13):
    assert 2*Q(1,2)**m*2**(m-1)==1
    assert 2*Q(1,2)**m*2**m==2
# Smooth density value but non-smooth slope at a true expansion boundary.
b=Q(1);gamma=[Q(1,2)]*2;rs=[Q(2)]*2
assert sum(g*g*r for g,r in zip(gamma,rs))==b
assert -sum(g*g*r*r for g,r in zip(gamma,rs))==-2 < -b*b
result={'status':'PASS','arithmetic':'SymPy exact rational/polynomial arithmetic',
'pure_death_matrix_vs_homogeneous_polynomial_coefficients':coefficient_checks,
'observable_tilted_joint_moments_checked':moment_checks,
'overcomplete_and_duplicate_atom_recoveries':recovered_counts,
'leading_tensor_alias_and_temporal_separation':True,'density_slope_detects_hazard_matched_expansion':True,
'limits':'First-boundary candidate controls only. No subsequent-expansion observability, minimal sampling, noisy-data accuracy, novelty or Lean claim.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('CONTROL-RESULTS.json').write_text(text);print(text,end='')
