#!/usr/bin/env python3
"""Exact q=4 original-source recurrence/degree fixture; no native/Lean/QE."""
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json


def lam(k):
    return k*(k-1)//2


def monophyly_polynomial(k):
    out={0:Q(0)}
    for r in range(1,k+1):
        num=Q(1)
        for j in range(r+1,k+1):
            num*=lam(j)
        weight=Q(2,r*(r+1))
        for j in range(r,k+1):
            den=Q(1)
            for l in range(r,k+1):
                if l!=j:
                    den*=lam(l)-lam(j)
            out[lam(j)]=out.get(lam(j),Q(0))+weight*num/den
    return out


def evaluate(poly,x):
    return sum(coef*x**power for power,coef in poly.items())


def solve_channel(h,polys):
    ds={}
    for k in sorted(polys,reverse=True):
        power=lam(k)
        rem=h.get(power,Q(0))-sum(d*polys[j].get(power,Q(0)) for j,d in ds.items())
        ds[k]=rem/polys[k][power]
    return ds


def wire(x):
    return f"{x.numerator}/{x.denominator}"


def main():
    checks=0
    def require(ok):
        nonlocal checks
        if not ok:
            raise AssertionError(f"exact check {checks+1} failed")
        checks+=1

    q=4
    kappa=Q(1,8);rho=Q(1,128*q);y=Q(1,2);c=y*kappa
    v=a=1-Q(1,4*q);s=(v*a)**(q-1)
    lo=kappa-rho;hi=kappa+rho
    require(s>Q(1,2))
    require(0<lo/s<hi/s<1)
    require(0<v*lo/hi<v*hi/lo<1)
    for ks in product((lo,hi),repeat=q):
        leading=ks[0]/s
        arms=[v*x/ks[0] for x in ks[1:]]
        require(0<leading<1 and all(0<x<1 for x in arms))
        require(leading*s==ks[0])
        for j in range(q-1):
            require(leading*s*arms[j]/v==ks[j+1])

    polys={k:monophyly_polynomial(k) for k in range(2,q+4)}
    expected={
        2:{0:Q(1),1:-Q(2,3)},
        3:{0:Q(1),1:-Q(1),3:Q(1,6)},
        4:{0:Q(1),1:-Q(6,5),3:Q(1,3),6:-Q(1,30)},
        5:{0:Q(1),1:-Q(4,3),3:Q(10,21),6:-Q(1,12),10:Q(1,140)},
        6:{0:Q(1),1:-Q(10,7),3:Q(25,42),6:-Q(5,36),10:Q(3,140),15:-Q(1,630)},
        7:{0:Q(1),1:-Q(3,2),3:Q(25,36),6:-Q(7,36),10:Q(9,220),15:-Q(1,180),21:Q(1,2772)},
    }
    for k,poly in polys.items():
        require(poly==expected[k])
        require(poly[0]==1)
        require(evaluate(poly,Q(1))==Q(2,k*(k+1)))
        diag=-Q(2,3) if k==2 else (-1)**(k-1)*Q(2*factorial(k-1)*factorial(k-2),factorial(2*k-2))
        require(poly[lam(k)]==diag)

    fixture=[];coeff_bound=Q(0);gaps=[];rank_minor=Q(1)
    for i in range(1,q+1):
        r=lam(i+3)
        alpha=Q(r*(r-1),6)*c**(r-3)
        beta=Q(r*(r-3),2)*c**(r-1)
        h={r:Q(1),3:-alpha,1:beta}
        ds=solve_channel(h,polys)
        eps=1/(4*(1+sum(map(abs,ds.values()))))
        actual={power:sum(ds[k]*poly.get(power,Q(0)) for k,poly in polys.items()) for power in (1,3,6,10,15,21)}
        require(actual=={power:h.get(power,Q(0)) for power in actual})
        for bits in product((0,1),repeat=len(polys)):
            channel=Q(1,2)+eps*sum(ds[k]*(bit-1) for k,bit in zip(polys,bits))
            require(Q(1,4)<channel<Q(3,4))
        def response(k):
            return Q(1,2)+eps*evaluate(h,y*k)
        center=response(kappa)
        lower=response(lo);upper=response(hi)
        require(lower<center<upper)
        gap=min(center-lower,upper-center);gaps.append(gap)
        require(r*c**(r-1)-3*alpha*c*c+beta==0)
        require(r*(r-1)*c**(r-2)-6*alpha*c==0)
        third=r*(r-1)*(r-2)*c**(r-3)-6*alpha
        require(third==r*(r-1)*(r-3)*c**(r-3)>0)
        rank_minor*=eps*kappa**r
        bound=eps*(hi**r+alpha*hi**3+beta*hi)
        coeff_bound=max(coeff_bound,bound)
        # Direct same-word moment substitution at the actual ordinary reference.
        for k in (lo,kappa,hi):
            moment_response=Q(1,2)+eps*(k**r*y**r-alpha*k**3*y**3+beta*k*y)
            require(moment_response==response(k))
        fixture.append({'r':r,'target':wire(center),'lower':wire(lower),'upper':wire(upper),
                        'epsilon':wire(eps),'monophyly_channel_coefficients':{str(k):wire(d) for k,d in ds.items()}})
    require(rank_minor>0)
    delta=min(gaps)
    threshold=delta/(2*coeff_bound)
    require(delta>0 and threshold>0)
    # A finite rational positive source W_N=E(y_N), same in all rows;
    # select a coherent moment tolerance without float approximations.
    denominator=2
    while True:
        yN=y+Q(1,denominator)
        if yN<1 and max(abs(yN**j-y**j) for j in (1,3,6,10,15,21))<threshold:
            break
        denominator*=2
    moments={j:yN**j for j in (1,3,6,10,15,21)}
    for row in fixture:
        r=row['r'];alpha=Q(r*(r-1),6)*c**(r-3);beta=Q(r*(r-3),2)*c**(r-1);eps=Q(row['epsilon'])
        def perturbed(k):
            return Q(1,2)+eps*(k**r*moments[r]-alpha*k**3*moments[3]+beta*k*moments[1])
        target=Q(row['target'])
        require(perturbed(lo)<target<perturbed(hi))
        for k in (lo,kappa,hi):
            require(abs(perturbed(k)-(Q(1,2)+eps*( (y*k)**r-alpha*(y*k)**3+beta*y*k )))<delta/2)

    receipt={'status':'PASS','exact_checks':checks,'q_fixture':q,'protected_hybrids':q-1,
             'contextual_private_word_response_rank':q,'same_original_sample_allocation':{'A':q+3,'B':1,'C':1,'D':1},
             'strict_bank_box':[wire(lo),wire(hi)],'reference_word_survival':wire(y),
             'center_leading_population':wire(kappa/s),'fixed_parent0_and_connector':wire(v),
             'degree':1,'full_bank_jacobian_and_hessian':'zero at center; exact source response derivative calculation',
             'conditional_rank_minor':wire(rank_minor),'full_face_gap':wire(delta),
             'moment_error_bound_coefficient':wire(coeff_bound),'sufficient_moment_error':wire(threshold),
             'coherent_ordinary_approximant_survival':wire(yN),'channels':fixture,
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'evidence':'exact original Kingman monophyly recurrence and rational source/chart/channel checks; not native binary/full8label enumeration/Lean/QE'}
    Path(__file__).with_name('high-rank-source-test-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('channels','conditional_rank_minor')},indent=2))


if __name__=='__main__':
    main()
