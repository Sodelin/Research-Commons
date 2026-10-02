#!/usr/bin/env python3
"""Bounded exact source controls for the arbitrary-tail first-comb invariant."""
from pathlib import Path
from hashlib import sha256
from math import comb,factorial,prod
import json,sys
import sympy as S
import obstruction_checks as F
import known_placement_six_checks as K
x,y,g=K.x,K.y,K.g

def H(n):return S.Integer(prod(comb(j,2) for j in range(2,n+1)))
def tree(n):
    t='A1'
    for j in range(2,n+1):t=F.join(t,f'A{j}')
    return t

def prefix(n,k):
    r=n-k+1
    return F.canonical([tree(r)]+[f'A{j}' for j in range(r+1,n+1)])

def transfer(n,k):
    r=n-k+1
    out=0
    for u,v,z,w in [(g,1-g,x,y),(1-g,g,y,x)]:
        for j in range(k):
            ell=k-1-j
            out+=u**(n-ell)*v**ell*S.binomial(k-1,j)*H(n)/H(k)*K.death(n-ell,j+1,z)*H(j+1)/H(n-ell)*w**comb(ell,2)
    return S.expand(out)

def C(n,q,t):
    return S.expand(sum(t**ell*q**comb(ell,2)*S.Rational(factorial(n)*factorial(n-1),factorial(n-ell)*factorial(n-ell-1)*factorial(ell)*factorial(ell+1)) for ell in range(n)))

def exact_sum(n):
    total=0
    for u,v,z,w in [(g,1-g,x,y),(1-g,g,y,x)]:
        for ell in range(n):
            expectation=sum(K.death(n-ell,r,z)*S.Rational(factorial(r),factorial(r+ell)) for r in range(1,n-ell+1))
            weight=S.Rational(factorial(n)*factorial(n-1),factorial(n-ell)*factorial(n-ell-1)*factorial(ell))
            total+=u**(n-ell)*v**ell*w**comb(ell,2)*weight*expectation
    return S.expand(total)

def run():
    checks=[]
    for n in range(1,7):
        rows=[]
        for k in range(1,n+1):
            a=transfer(n,k)
            direct=S.expand(H(n)/H(k)*K.bare(K.orbit(prefix(n,k))))
            assert S.expand(a-direct)==0
            ordinary=S.expand(H(n)/H(k)*K.edge_forest(prefix(n,k),x))
            assert S.expand(ordinary-K.death(n,k,x))==0
            rows.append(a)
        assert S.expand(sum(rows)-exact_sum(n))==0
        checks.append({'n':n,'all_comb_cut_coordinates_checked':n,'source_transfer_and_expectation_formula':'PASS'})
    controls=[]
    for xx,yy,gg in [(S.Rational(1,2),S.Rational(3,4),S.Rational(2,3)),(S.Rational(2,3),S.Rational(1,3),S.Rational(1,2))]:
        for n in range(2,13):
            value=exact_sum(n).subs({x:xx,y:yy,g:gg}) if n<=6 else sum(transfer_numeric(n,k,xx,yy,gg) for k in range(1,n+1))
            upper=gg**n*C(n,yy,(1-gg)/gg)+(1-gg)**n*C(n,xx,gg/(1-gg))
            lower=min(K.death(n,1,xx),K.death(n,1,yy))*upper
            assert 0<lower<=value<=upper
            controls.append({'n':n,'source':[str(xx),str(yy),str(gg)],'positive_bounds':'PASS'})
    return {'status':'PASS','python':sys.version,'sympy':S.__version__,
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'dependencies_sha256':{Path(p).name:sha256(Path(p).read_bytes()).hexdigest() for p in [F.__file__,K.__file__]},
        'symbolic_source_controls':checks,'rational_positive_bound_controls':controls,
        'limits':['These controls verify the finite comb-cut algebra, not the asymptotic saddle or arbitrary-tail theorem.',
                  'No asymptotic numerical fit or all-copy equality stopping claim is made.']}

def transfer_numeric(n,k,xx,yy,gg):
    out=0
    for u,v,z,w in [(gg,1-gg,xx,yy),(1-gg,gg,yy,xx)]:
        for j in range(k):
            ell=k-1-j
            out+=u**(n-ell)*v**ell*S.binomial(k-1,j)*H(n)/H(k)*K.death(n-ell,j+1,z)*H(j+1)/H(n-ell)*w**comb(ell,2)
    return out

if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
