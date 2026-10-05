#!/usr/bin/env python3
"""Exact supporting controls, not a numerical proof of global injectivity.
Dimensionless rates r correspond to physical rates c*r, c=8/3.
A rational beta_a denotes exp(-c*a), so all tested ages are legal real ages.
"""
from fractions import Fraction as F
from math import isqrt
import json

def sqrt_fraction(x):
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    assert a*a==x.numerator and b*b==x.denominator
    return F(a,b)

def root(beta,R,k):return beta**k*R/(R+k)
def stage(beta_a,beta_T,r,R,k):
    # Used only at integer r, so every endpoint expression is rational.
    survival=(beta_T/beta_a)**r
    return beta_a**k*r/(r+k)*(1-(beta_T/beta_a)**(r+k))+survival*root(beta_T,R,k)

root_checks=0
for R in (F(1,2),F(2,3),F(1),F(2),F(3),F(5),F(10)):
    for beta in (F(1,2),F(1,4),F(3,4),F(5,7)):
        a1,a2=root(beta,R,1),root(beta,R,2)
        Q=a2/a1**2
        assert Q>1
        recovered=sqrt_fraction(Q/(Q-1))-1
        assert recovered==R and a1*(R+1)/R==beta
        assert a2-a1*a1>0
        root_checks+=1

cc_checks=0;bc_checks=0;g_checks=0
for T in range(3,8):
    beta_T=F(2)**(-T)
    for R in range(1,6):
        vals=[stage(F(1),beta_T,r,R,1) for r in range(1,7)]
        assert all(x<y for x,y in zip(vals,vals[1:]));cc_checks+=5
        B1,B2=root(beta_T,R,1),root(beta_T,R,2)
        assert B2>B1*B1
        for rC in range(1,6):
            ratios=[]
            for h in range(1,T):
                D1=stage(F(2)**(-h),beta_T,rC,R,1)-B1
                D2=stage(F(2)**(-h),beta_T,rC,R,2)-B2
                assert D1>0 and D2>0
                ratios.append(D2/D1)
                for g in (F(1,4),F(1,2),F(3,4)):
                    m1,m2=B1+g*D1,B2+g*D2
                    assert (m2-B2)/(m1-B1)==D2/D1
                    assert (m1-B1)/D1==g
                    g_checks+=1
            assert all(x>y for x,y in zip(ratios,ratios[1:]));bc_checks+=len(ratios)-1

# Actual two-stage laws with EXACTLY EQUAL FIRST moments and distinct onsets.
# First law's pre-root rate equals its root rate, so its law is shifted Exp(R).
# Choose the second law, then solve the first onset beta exactly.
ab_checks=0;minimum_gap=None
for R in range(1,6):
    for r2 in range(R+1,R+6):
        for beta_T in (F(1,32),F(1,16)):
            for beta_a2 in (F(1,8),F(1,4),F(1,2)):
                mu=stage(beta_a2,beta_T,r2,R,1)
                beta_a1=mu*(R+1)/R
                assert beta_T<beta_a2<beta_a1<1 # a1<a2<T
                first1=stage(beta_a1,beta_T,R,R,1)
                first2=stage(beta_a2,beta_T,r2,R,1)
                assert first1==first2
                second1=stage(beta_a1,beta_T,R,R,2)
                second2=stage(beta_a2,beta_T,r2,R,2)
                gap=second1-second2
                assert gap>0
                minimum_gap=gap if minimum_gap is None else min(minimum_gap,gap)
                # At T the earlier/slower law has strictly higher survival,
                # whereas at the later onset it has lower survival.
                assert (beta_T/beta_a1)**R>(beta_T/beta_a2)**r2
                assert (beta_a2/beta_a1)**R<1
                ab_checks+=1

# Accepted AA and BB source formulas on a rational-exponential grid.
def pair_aa_bb(h,u,v,rA,rB,rC,rAB,R,g):
    t1=h+u;T=t1+v;e=lambda x:F(2)**(-x)
    H=lambda r,l:F(r,r+1)*(1-e((r+1)*l))
    tail=e(T)*F(R,R+1)
    AA=H(rA,t1)+e(rA*t1)*e(t1)*H(rAB,v)+e(rA*t1+rAB*v)*tail
    s=e(rB*h);b=e(rB*u);a=e(rAB*v);cc=e(rC*(u+v))
    BB=H(rB,h)+s*((1-g)**2*e(h)*H(rB,u)+g*g*e(h)*H(rC,u+v)+(1-g)**2*b*e(t1)*H(rAB,v)+((1-g)**2*b*a+g*g*cc+2*g*(1-g))*tail)
    return AA,BB
rate_checks=0
for h,u,v in ((1,1,1),(1,2,1),(2,1,2)):
    for rC,rAB,R in ((1,1,1),(2,3,4),(4,2,1),(3,3,3)):
        for g in (F(1,4),F(1,2),F(3,4)):
            aa=[pair_aa_bb(h,u,v,r,2,rC,rAB,R,g)[0] for r in range(1,7)]
            bb=[pair_aa_bb(h,u,v,2,r,rC,rAB,R,g)[1] for r in range(1,7)]
            assert all(x<y for x,y in zip(aa,aa[1:]))
            assert all(x<y for x,y in zip(bb,bb[1:]))
            rate_checks+=10

# Exact symbolic identities expressed by polynomial numerator arithmetic.
# q'(x)-1 has numerator B2-B1^2 after multiplying (x-B1)^2.
for x,B1,B2 in ((F(3,4),F(1,4),F(1,8)),(F(1,2),F(1,8),F(1,16))):
    derivative=((2*x)*(x-B1)-(x*x-B2))/(x-B1)**2
    assert derivative==1+(B2-B1*B1)/(x-B1)**2 and derivative>0

out={'status':'PASS','root_closed_form_checks':root_checks,'cc_strict_rate_comparisons':cc_checks,'bc_strict_ratio_comparisons':bc_checks,'gamma_exact_recoveries':g_checks,'ab_equal_first_distinct_second_cases':ab_checks,'ab_minimum_exact_second_gap':str(minimum_gap),'aa_bb_strict_rate_comparisons':rate_checks,'two_site_upper_bound_only':True,'global_proof_by_controls':False}
print(json.dumps(out,sort_keys=True,indent=2))
