"""Exact cap-eight ordinary-interior closure candidate and local obstruction.

This is NOT an all-factor rejection certificate. The source-specific endpoint
candidate, Jacobian rank and tangent polynomial are checked exactly.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import sympy as s

def log_interval(x,N=32):
    """Rigorous rational enclosure for -log(x), 0<x<=1."""
    x=F(x); z=(1-x)/(1+x)
    low=2*sum((z**(2*k+1)/F(2*k+1) for k in range(N)),F(0))
    rem=2*z**(2*N+1)/(F(2*N+1)*(1-z*z))
    return low,low+rem

def main():
    ex=[1,3,6,10,15,21,28]
    pars=[(s.Rational(2,5),s.Rational(3,10)),(s.Rational(3,5),s.Rational(7,10))]
    cols=[s.Matrix(ex),s.ones(7,1)]
    for p,q in pars:
        f=[1-p+p*q**l for l in ex]
        cols += [s.Matrix([(1-q**l)/f[i] for i,l in enumerate(ex)]),
                 s.Matrix([-p*l*q**(l-1)/f[i] for i,l in enumerate(ex)])]
    J=s.Matrix.hstack(*cols)
    assert J.rank()==6
    c=J.T.nullspace()[0]; c=c/c[0]
    assert all(x==0 for x in c.T*J)
    e1=s.Matrix([1,0,0,0,0,0,0]); assert s.Matrix.hstack(J,e1).rank()==7
    z=s.symbols('z'); P=sum(c[i]*z**l for i,l in enumerate(ex))
    Q=s.Poly(s.cancel(P/(z*(z-1)**2)),z)
    assert Q.degree()==25 and Q.count_roots(0,1)==0
    assert Q.eval(0)>0 and Q.eval(1)>0

    atoms=[F(0),F(21,200),F(3,20),F(7,20),F(1,2)]
    weights=[F(1,2),F(3,25),F(2,25),F(9,50),F(3,25)]
    assert sum(weights)==1 and all(w>0 for w in weights)
    moments=[]
    for l in ex:
        m=sum((w*x**l for w,x in zip(weights,atoms)),F(0))
        formula=F(1,2)**l*F(1,2)*(F(3,5)+F(2,5)*F(3,10)**l)*(F(2,5)+F(3,5)*F(7,10)**l)
        assert m==formula
        moments.append(m)
    # No ordinary exposing polynomial can have 4 positive double roots and 0:
    assert 2*(len(atoms)-1)+1>len(ex) # nine roots counted > seven

    cf=[F(int(x.p),int(x.q)) for x in c]
    def H_interval(p,q):
        low=high=F(0)
        for ci,l in zip(cf,ex):
            lo,hi=log_interval(1-p+p*q**l)
            low+=ci*(lo if ci>=0 else hi)
            high+=ci*(hi if ci>=0 else lo)
        return low,high
    neg=H_interval(F(2,5),F(3,10)); pos=H_interval(F(7,10),F(3,10))
    assert neg[1]<-F(1,100) and pos[0]>F(1,25)

    result={'status':'PASS','cap':8,'exponents':ex,
      'atoms':[str(x) for x in atoms],'weights':[str(w) for w in weights],
      'moments':[str(m) for m in moments],
      'ordinary_moment_interior_zero_count':{'required':9,'available':7},
      'inner_parameter_jacobian_rank':6,'including_killing_ratio_rank':7,
      'normal_coefficients':[str(x) for x in c],
      'normal_P':'sum c_j*z^lambda_j = z*(1-z)^2*Q(z)',
      'Q_degree':Q.degree(),'Q_roots_closed_unit_interval':0,
      'Q_positive_at_endpoints':True,
      'positive_infinitesimal_probability_tangent_normal':'-P(q)<0 for every 0<q<1',
      'global_conic_separator_refuted':{'negative_example_H_less_than':'-1/100',
         'positive_example_H_greater_than':'1/25','rigorous_rational_log_series_terms':32},
      'limits':'Closure membership and ordinary moment interior proved. Local fixed-three-factor inverse-function obstruction proved by exact rank. Neither all-factor nonattainment nor actual closure-boundary membership established.'}
    Path(__file__).with_name('boundary-attack-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['normal_coefficients','moments']},indent=2))

if __name__=='__main__': main()
