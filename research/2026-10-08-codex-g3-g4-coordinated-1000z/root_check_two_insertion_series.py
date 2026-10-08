"""Independent bounded exact series audit of actual bare-cell source jets.

Rational EPPF enumeration; no original provider/module execution, search,
compiler, or selected-zero numerical witness. The generic minority probability
is u, its survival is rho=1/2, and the majority survival is exp(-u*z).
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json
import sys
import sympy as s

z=s.Symbol('z')

def lam(n):
    return n*(n-1)//2

@lru_cache(None)
def arm(sizes, exponential):
    if not sizes:
        return (s.Integer(1),)+(s.Integer(0),)*4
    n,r=sum(sizes),len(sizes)
    factor=F(factorial(r)*prod(factorial(a) for a in sizes),
             factorial(n)*comb(n-1,r-1))*prod(lam(j) for j in range(r+1,n+1))
    coefficients=[factor/F(prod(lam(k)-lam(j) for k in range(r,n+1) if k!=j))
                  for j in range(r,n+1)]
    if not exponential:
        value=sum((c*F(1,2)**lam(j) for j,c in zip(range(r,n+1),coefficients)),F(0))
        return (s.Rational(value.numerator,value.denominator),)+(s.Integer(0),)*4
    return tuple(sum((s.Rational(c.numerator,c.denominator)*(-lam(j)*z)**q/s.factorial(q)
                      for j,c in zip(range(r,n+1),coefficients)),s.Integer(0)) for q in range(5))

def source(sizes):
    result=[s.Integer(0) for _ in range(5)]
    n=sum(sizes)
    for mask in product((0,1),repeat=len(sizes)):
        minority=tuple(a for a,m in zip(sizes,mask) if m)
        majority=tuple(a for a,m in zip(sizes,mask) if not m)
        j=sum(minority)
        if j>4:
            continue
        fixed=arm(minority,False)[0]
        exponential=arm(majority,True)
        for q in range(j,5):
            result[q]+=fixed*sum((s.Integer(comb(n-j,k))*(-1)**k*exponential[q-j-k]
                                  for k in range(min(n-j,q-j)+1)),s.Integer(0))
    return [s.expand(c) for c in result]

def sub(left,right,a,b):
    return [s.expand(a*x+b*y) for x,y in zip(left,right)]

def main(output):
    f=sub(source((2,2)+(1,)*5),source((3,)+(1,)*6),s.Rational(3,15),s.Rational(-2,15))
    h=sub(source((2,2)+(1,)*2),source((3,)+(1,)*3),s.Rational(3,9),s.Rational(-2,9))
    e=sub(source((3,2,1,1)),source((4,1,1,1)),s.Rational(2,6),s.Rational(-1,6))
    d=s.Rational(1,2)
    eta=(3*(z-d)**2-d**3)/2
    kcat=s.Rational(1,18)-s.Rational(1,20)+s.Rational(1,144)-s.Rational(1,5760)
    delta=kcat+z**3/3-d*z**2/2-z*eta/3
    assertions=0
    for name,values in [('f',f),('h',h),('e',e)]:
        for coefficient in values[:3]:
            assert coefficient==0,name
            assertions+=1
    assert e[3]==0
    assert s.expand(f[3]+s.Rational(2,15)*eta)==0
    assert s.expand(h[3]+s.Rational(2,9)*eta)==0
    assert s.expand(e[4]+s.Rational(2,3)*z*eta+3*delta)==0
    assertions+=4
    branch_records=[]
    for sign in (-1,1):
        centre=d+sign*d**s.Rational(3,2)/s.sqrt(3)
        W=sign*d**s.Rational(9,2)/(9*s.sqrt(3))+d**5/15-d**6/90
        actual_h4=s.simplify((h[4]-s.Rational(5,3)*f[4]).subs(z,centre))
        actual_e4=s.simplify(e[4].subs(z,centre))
        assert s.simplify(actual_h4+12*W)==0
        assert s.simplify(actual_e4+3*W)==0
        assert s.simplify(actual_e4/actual_h4)==s.Rational(1,4)
        assertions+=3
        branch_records.append({'sign':sign,'centre':str(centre),'W':str(W),
                               'h4_after_actual_f_zero_correction':str(actual_h4),
                               'e4':str(actual_e4),'v_over_h_limit':'-1/2'})
    record={'status':'PASS','exact_symbolic_assertions':assertions,
            'method':'Independent specified-partition EPPF/root-count spectral enumeration; rational symbolic series through u^4 at rho=1/2.',
            'generic_e_cubic_identically_zero':True,
            'generic_e_quartic':str(e[4]),'branches':branch_records,
            'analytic_IFT_witness_executed':False,'full_target_return':False,
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'PASS','exact_symbolic_assertions':assertions,'output':str(output)}))

if __name__=='__main__':
    main(Path(sys.argv[1]))
