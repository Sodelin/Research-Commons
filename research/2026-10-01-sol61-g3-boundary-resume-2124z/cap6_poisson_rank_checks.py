"""Finite exact polynomial/rank control, not analytic-IFT verification."""
import json
import platform
from pathlib import Path
import sympy as s

r=s.symbols('r')
la=[1,3,6,10,15]
R=[sum(r**k for k in range(l)) for l in la]
mat=s.Matrix([[l,R[i],s.diff(R[i],r),1-r**(2*l),-l*r**(2*l-2)]
              for i,l in enumerate(la)])
det=s.factor(mat.det(method='domain-ge'))
out={'python':platform.python_version(),'sympy':s.__version__,
     'exponents':la,
     'columns':['lambda','R(r)','Rprime(r)','1-r^(2lambda)',
                'd_q(1-q^lambda) at q=r^2'],
     'determinant_factorization':str(det),'rational_controls':[]}
for x in [s.Rational(1,5),s.Rational(1,3),s.Rational(1,2),
          s.Rational(2,3),s.Rational(4,5)]:
    value=det.subs(r,x)
    assert value!=0
    out['rational_controls'].append({'r':str(x),'determinant':str(value)})
Path(__file__).with_name('cap6-poisson-rank-checks.json').write_text(
    json.dumps(out,indent=2)+'\n')
print('PASS exact polynomial determinant and 5 rational rank controls')
