"""Bounded critical-locus check of the recovered cap-eight left normal.

Even coprimality here would not show it is a global boundary normal.
"""
import json,time,hashlib,platform
from pathlib import Path
import sympy as s
p,q=s.symbols('p q'); start=time.perf_counter()
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'2026-10-01-sol61-g3-interior-2025z'/'boundary-attack-checks.json'
if not SOURCE.is_file():
    SOURCE=Path('/workspace/shared/g3-interior-2025z/boundary-attack-checks.json')
raw=SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='1e363df45e2147e1e0ed8a3d0d47ec2bd208edb64f656bf32c312d0a4205ee14'
r=json.loads(raw)
c=[s.Rational(x) for x in r['normal_coefficients']]; ex=r['exponents'];d=len(ex)
f=[s.Poly(1-p+p*q**l,p,q,domain=s.QQ) for l in ex]
P=s.Poly(0,p,q,domain=s.QQ);Q=P
for i,(cj,l) in enumerate(zip(c,ex)):
    z=s.Poly(1,p,q,domain=s.QQ)
    for j in range(d):
        if j!=i:z*=f[j]
    P+=z*s.Poly(cj*(1-q**l),p,q,domain=s.QQ)
    Q+=z*s.Poly(cj*l*q**(l-1),p,q,domain=s.QQ)
# At strict p>0, gradient-q zero iff Q=0, independent of its -p factor.
removed=[]
for name,z in [('P',P),('Q',Q)]:
    k=0
    while True:
        quotient,rem=z.div(s.Poly(q-1,p,q,domain=s.QQ))
        if not rem.is_zero:break
        z=quotient;k+=1
    removed.append(k)
    if name=='P':P=z
    else:Q=z
print('degrees',P.total_degree(),Q.total_degree(),'q-1 factors',removed,flush=True)
# Integral primitive representatives permit finite-field coprimality control.
_,Pi=P.clear_denoms();_,Qi=Q.clear_denoms()
_,Pi=Pi.primitive();_,Qi=Qi.primitive()
prime=1009
Pm=s.Poly(Pi.as_expr(),p,q,modulus=prime);Qm=s.Poly(Qi.as_expr(),p,q,modulus=prime)
assert Pm.total_degree()==P.total_degree() and Qm.total_degree()==Q.total_degree()
g=Pm.gcd(Qm)
print('modular gcd',g.as_expr(), 'seconds',time.perf_counter()-start,flush=True)
result={'python':platform.python_version(),'sympy':s.__version__,
  'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'input_sha256':hashlib.sha256(raw).hexdigest(),
  'status':'PASS' if g.total_degree()==0 else 'INCONCLUSIVE',
  'normal_is_global_boundary_normal':'NOT ESTABLISHED',
  'removed_q_minus_one_factors':removed,'primitive_total_degrees':[P.total_degree(),Q.total_degree()],
  'prime':prime,'degrees_preserved_mod_prime':True,'modular_gcd':str(g.as_expr()),
  'coprime_over_rationals':g.total_degree()==0,
  'limits':'Only this recovered rational local normal is checked. Global normal classification, source factor bound and candidate membership remain unknown.'}
Path(__file__).with_name('critical-locus-checks.json').write_text(json.dumps(result,indent=2)+'\n')
