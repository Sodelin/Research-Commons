"""Exact exposed-atom control blocking the divisible-semigroup shortcut."""
import json
from fractions import Fraction as F
from pathlib import Path
import sympy as s

def main():
    x=s.symbols('x'); ex=[0,1,3,6,10]
    atoms=[s.Rational(1,4),s.Rational(1,2)]
    rows=[[a**l for l in ex] for a in atoms]
    rows += [[0 if l==0 else l*a**(l-1) for l in ex] for a in atoms]
    c=s.Matrix(rows).nullspace()[0]
    P=sum(ci*x**l for ci,l in zip(c,ex))
    square=(x-atoms[0])**2*(x-atoms[1])**2
    Q=s.Poly(s.cancel(P/square),x)
    assert all(a>0 for a in Q.all_coeffs())
    moments=[sum((a**l for a in atoms))/2 for l in ex]
    assert sum(ci*m for ci,m in zip(c,moments))==0
    assert moments[0]==1
    assert moments[2]!=moments[1]**3
    for a in atoms:
        assert P.subs(x,a)==0 and s.diff(P,x).subs(x,a)==0
    result={'status':'PASS','exponents':ex,
      'source_atoms':[str(a) for a in atoms],'source_weights':['1/2','1/2'],
      'source_positive_baseline':'1/2','source_factor_probability':'1/2','source_factor_ratio':'1/2',
      'moments':[str(m) for m in moments],
      'exposing_polynomial_coefficients':[str(ci) for ci in c],
      'quotient_coefficients':[str(ci) for ci in Q.all_coeffs()],
      'quotient_strict_positive':True,'double_roots_exact':True,'zero_expectation_exact':True,
      'root_deterministic_obstruction':str(moments[2]-moments[1]**3),
      'limits':'The no-square-root conclusion is a support/independence hand proof using this exact exposing polynomial. No claim of finite-factor membership decidability follows.'}
    Path(__file__).with_name('divisibility-checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
