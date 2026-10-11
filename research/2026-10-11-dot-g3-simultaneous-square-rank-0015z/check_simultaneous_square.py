#!/usr/bin/env python3
"""Finite diagnostics only: generic series identity and one two-chain rank control."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sympy as s

e, u, v, x, y, tau = s.symbols('e u v x y tau', real=True)
r = s.symbols('r', positive=True)
n = s.symbols('n', positive=True, integer=True)
def trunc(z):
    return s.series(z, e, 0, 4).removeO().expand()
def H(z, q):
    return s.log(1+z)-s.log(1+z*q**n)
pair = trunc(H(e,r)+H(e**2*(s.Rational(1,2)+e*u), r**2+e*v)-e*(1-r**n))
expected = e**3*((1-r**(3*n))/3 + u*(1-r**(2*n))-v*n*r**(2*n-2)/2)
assert s.simplify(pair-expected) == 0
old = (tau-e+e**3*x)*(1-(r+e**3*y)**n)
reference = (tau-e)*(1-r**n)
assert s.simplify(trunc(old-reference)-e**3*(x*(1-r**n)-tau*y*n*r**(n-1))) == 0
print('PASS symbolic positive-integer exponent pair expansion and removed-weight cross order')

def rank(matrix):
    a=[row[:] for row in matrix]
    k=0
    for col in range(len(a[0])):
        pivot=next((i for i in range(k,len(a)) if a[i][col]),None)
        if pivot is None:
            continue
        a[k],a[pivot]=a[pivot],a[k]
        z=a[k][col]
        a[k]=[v/z for v in a[k]]
        for i in range(k+1,len(a)):
            z=a[i][col]
            if z:
                a[i]=[v-z*w for v,w in zip(a[i],a[k])]
        k+=1
        if k==len(a):
            break
    return k

Q={F(1,2),F(1,3)}
E={q for q in Q if q*q not in Q}
T=Q|{q*q for q in Q}
assert len(Q)==len(E)==2 and len(T)==4
assert all(q**3 not in T for q in Q)
records=[]
for alpha in (0,1):
    for beta in (0,1):
        d=2*len(T)+alpha+beta
        lam=[i*(i+1)//2 for i in range(1,d+1)]
        def matrix(nodes):
            rows=[]
            for l in lam:
                rows.append(([F(l)] if alpha else [])+([F(1)] if beta else [])+
                            [z for q in sorted(nodes) for z in (1-q**l,-l*q**(l-1))])
            return rows
        new=matrix(T)
        old=matrix(Q|{min(Q)**2})
        rn,ro=rank(new),rank(old)
        assert rn==d and ro==d-2
        records.append(dict(alpha=alpha,beta=beta,cap=d+1,new_rank=rn,old_rank=ro,
                            matrix=[[str(z) for z in row] for row in new]))
        print(f'PASS alpha={alpha} beta={beta}: old rank {ro}, simultaneous rank {rn}/{d}')
out={'nodes':[str(q) for q in sorted(Q)],'terminals':[str(q) for q in sorted(E)],
     'square_union':[str(q) for q in sorted(T)],'cube_separated':True,'records':records}
body=json.dumps(out,sort_keys=True,indent=2)+'\n'
Path(__file__).with_name('square-rank-certificate.json').write_text(body)
print('certificate SHA256',hashlib.sha256(body.encode()).hexdigest())
print('No IFT/source theorem, cutoff, RCF witness or input acquisition executed.')
