"""Exact factor/product and elementary positivity certificate on r>0."""
from pathlib import Path
import hashlib,json,resource,time
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
t0=time.monotonic();root=Path(__file__).parent;r=S.symbols('r')
src=root/'two-slice-resultant-pilot.json';x=json.loads(src.read_text())
g=S.Poly.from_list([int(v) for v in x['gcd_coefficients_descending']],r,domain=S.ZZ)
content,factors=S.factor_list(g)
product=S.Poly(content,r);records=[]
for f,e in factors:
    product*=f**e
    if f.as_expr()==r:
        kind='r>0'
    elif f.as_expr()==r*r-r+1:
        assert S.expand((r-S.Rational(1,2))**2+S.Rational(3,4))==f.as_expr()
        kind='(r-1/2)^2+3/4>0'
    elif all(c>=0 for c in f.all_coeffs()) and f.eval(0)>0:
        kind='nonnegative coefficients and positive constant'
    else:
        assert f.degree()==34
        assert f.coeff_monomial(r**32)==-1 and f.coeff_monomial(r**2)==-1
        group=(r**34+r**33-r**32+9*r**31)+(9*r**3-r**2+r+1)
        rem=S.Poly(f.as_expr()-group,r)
        assert all(c>=0 for c in rem.all_coeffs())
        assert S.expand(r**31*(r**3+(r-S.Rational(1,2))**2+S.Rational(35,4))
                        +r*(9*(r-S.Rational(1,18))**2+S.Rational(35,36))+1)==group
        kind='two explicit positive square groups plus nonnegative-coefficient remainder'
    records.append({'degree':int(f.degree()),'multiplicity':int(e),
                    'coefficients_descending':[str(v) for v in f.all_coeffs()],
                    'positivity_reason':kind})
assert product==g and content>0
# Verify the returned gcd divides both exact slice resultant records.
for rec in x['records']:
    E=S.Poly.from_list([int(v) for v in rec['primitive_coefficients_descending']],r,domain=S.ZZ)
    assert E.rem(g).is_zero
# Recompute gcd independently from the two retained coefficient lists.
E3,E5=[S.Poly.from_list([int(v) for v in rec['primitive_coefficients_descending']],r,domain=S.ZZ) for rec in x['records']]
assert S.gcd(E3,E5)==g
out={'status':'PASS complete exact gcd and positivity certificate for every r>0',
     'gcd_degree':int(g.degree()),'content':str(content),'factor_records':records,
     'positive_root_count':'0 by elementary factor positivity; no sampled extrapolation',
     'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
     'seconds':time.monotonic()-t0,'sympy':S.__version__,
     'scope':'Exact resultant gcd and positive factor/product checks. Critical-locus/source implications remain hand theorems.'}
(root/'positive-gcd-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','gcd_degree','positive_root_count','seconds']}))
