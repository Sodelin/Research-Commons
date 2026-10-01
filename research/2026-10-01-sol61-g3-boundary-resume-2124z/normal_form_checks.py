"""Exact finite controls for a hand-proved countable closure normal form.

The limit/classification theorem is not proved by these controls. No source
factor bound or all-factor nonattainment certificate is computed.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import platform
import sympy as s


def R(q, exponent):
    return sum((q**j for j in range(exponent)), F(0))


def log_interval(x, terms=20):
    """Rational enclosure for -log(x), for 0<x<=1."""
    z=(1-x)/(1+x)
    lo=2*sum((z**(2*j+1)/F(2*j+1) for j in range(terms)), F(0))
    rem=2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
    return lo,lo+rem


def main():
    ranks=[]
    for M in range(2,13):
        ex=[j*(j-1)//2 for j in range(2,M+1)]
        nodes=[F(j,M) for j in range(1,M)]
        mat=s.Matrix([[s.Rational(R(q,k)) for q in nodes] for k in ex])
        rank=mat.rank()
        assert rank==M-1
        ranks.append({'cap':M,'residual_nodes':len(nodes),'rank':rank})

    remainder_cases=0
    for exponent in range(1,46):
        for p,q in [(F(3,7),F(2,5)),(F(99,100),F(999,1000)),
                    (F(1,1000),F(1,1000)),(F(1,2),F(1,2))]:
            u=p*(1-q)
            z=u*R(q,exponent)
            assert z==p*(1-q**exponent)
            if z<=F(1,2):
                lo,hi=log_interval(1-z)
                assert lo>=z
                assert hi-z<=z*z
                remainder_cases+=1
            # The Jensen lower bound protects every fixed closed-factor limit.
            assert 1-p+p*q**exponent >= (1-p+p*q)**exponent

    poisson=[]
    w,r=F(3,7),F(2,5)
    for N in [8,16,32,64,128]:
        p=w/(N*(1-r))
        assert 0<p<1 and 0<r<1
        largest=F(0)
        for exponent in [1,3,6,10,15,21,28,36,45]:
            z=p*(1-r**exponent)
            assert z<=F(1,2)
            lo,hi=log_interval(1-z)
            target=w*R(r,exponent)
            assert N*lo>=target
            err=N*hi-target
            assert err<=target*target/N
            largest=max(largest,err)
        poisson.append({'N':N,'strict_p':str(p),
                        'max_log_error_certified_less_than':str(F(1,N)),
                        'actual_rational_enclosure_within_claim':largest<F(1,N)})

    # A finite summable strict-factor prefix challenges loss ordering/tail sum.
    pqs=[(F(1,2**i),F(1,2)) for i in range(1,41)]
    us=[p*(1-q) for p,q in pqs]
    assert us==sorted(us,reverse=True)
    C=F(1,2)
    assert sum(us,F(0))<C
    tail=[]
    for J in [4,8,16,24,32]:
        maxu=max(us[J:])
        assert maxu<=C/(J+1)
        for exponent in [1,3,6,10,15,21,28]:
            if exponent*maxu>F(1,2):
                continue
            lin=sum((u*R(q,exponent) for u,(_,q) in zip(us[J:],pqs[J:])),F(0))
            los=his=F(0)
            for p,q in pqs[J:]:
                lo,hi=log_interval(1-p+p*q**exponent)
                los+=lo;his+=hi
            assert los>=lin
            assert his-lin<=exponent**2*C*C/(J+1)
        tail.append({'J':J,'tail_factors':40-J,
                     'max_loss_sort_bound':True,'tail_remainder_bound':True})

    out={'status':'PASS','python':platform.python_version(),
         'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'residual_rank_controls':ranks,'exact_log_remainder_cases':remainder_cases,
         'poisson_strict_approximants':poisson,'summable_tail_controls':tail,
         'limits':['Finite exact rational/SymPy corroboration only',
                   'No countable-limit theorem established by computation',
                   'No exact total factor bound or cap-eight membership decision',
                   'No proof-assistant verification or full biological census']}
    Path(__file__).with_name('normal-form-checks.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
