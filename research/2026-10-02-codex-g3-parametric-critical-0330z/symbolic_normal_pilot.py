"""Bounded exact symbolic normal-cofactor pilot; no full bivariate resultant."""
from pathlib import Path
import itertools,json,time,resource,hashlib
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
t=time.monotonic();r=S.symbols('r');ls=[1,3,6,10,15,21]
# determinant expansion deliberately bounded at 5! terms per cofactor.
rows=[[S.Poly(1,r) for l in ls],[S.Poly(l,r) for l in ls],
      [S.Poly(1-r**l,r) for l in ls],[S.Poly(l*r**(l-1),r) for l in ls],
      [S.Poly(1-r**(2*l),r) for l in ls],[S.Poly(l*r**(2*l-2),r) for l in ls]]
C=[]
for i in range(6):
    cols=[j for j in range(6) if j!=i];v=S.Poly(0,r)
    for perm in itertools.permutations(cols):
        inv=sum(perm[a]>perm[b] for a in range(5) for b in range(a+1,5))
        term=S.Poly((-1)**(inv+i),r)
        for k,j in enumerate(perm):term*=rows[k+1][j]
        v+=term
    C.append(v)
D=sum(C,S.Poly(0,r))
assert all(sum((rows[k][i]*C[i] for i in range(6)),S.Poly(0,r)).is_zero for k in range(1,6))
g=C[0]
for v in C[1:]:g=S.gcd(g,v)
B=[v.exquo(g) for v in C]
rec={'status':'PASS exact symbolic cofactor construction and normal identities',
     'lambda':ls,'C_degrees':[int(v.degree()) for v in C],
     'D_degree':int(D.degree()),'common_factor':str(S.factor(g.as_expr())),
     'common_factor_degree':int(g.degree()),'B_degrees':[int(v.degree()) for v in B],
     'B_coefficients_descending':[[str(x) for x in v.all_coeffs()] for v in B],
     'D_div_common_factor':str(S.factor(D.exquo(g).as_expr())),
     'seconds':time.monotonic()-t,'sympy':S.__version__,
     'scope':'Exact univariate cofactor algebra only. No critical-set isolation or source transfer.'}
Path(__file__).with_name('symbolic-normal-pilot.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:rec[k] for k in ['status','C_degrees','D_degree','common_factor','B_degrees','seconds']}))
