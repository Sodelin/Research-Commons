"""Bounded exact two-slice resultant pilot using normalized normal cofactors."""
from pathlib import Path
import hashlib,json,time,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
t0=time.monotonic();root=Path(__file__).parent;r,p=S.symbols('r p')
data=json.loads((root/'symbolic-normal-pilot.json').read_text())
B=[S.Poly.from_list([int(x) for x in cs],r,domain=S.ZZ) for cs in data['B_coefficients_descending']]
ls=data['lambda'];records=[];Elist=[]
for z in [3,5]:
    # Low p degree, univariate integer-polynomial coefficients in r.
    domain=S.ZZ.poly_ring(r)
    P=S.Poly(0,p,domain=domain);Q0=P
    ff=[S.Poly(1-p+p*z**l,p,domain=domain) for l in ls]
    for i,l in enumerate(ls):
        term=S.Poly(1,p,domain=domain)
        for j in range(6):
            if j!=i:term*=ff[j]
        P+=term.mul_ground(B[i].as_expr()*(1-z**l))
        Q0+=term.mul_ground(B[i].as_expr()*l*z**(l-1))
    Q=Q0.exquo(S.Poly(1-p,p,domain=domain))
    assert P.degree()==5 and Q.degree()==4
    res=S.Poly(P.resultant(Q),r,domain=S.ZZ)
    content,primitive=res.primitive()
    records.append({'q_slice':z,'resultant_degree':int(res.degree()),
         'primitive_coefficients_descending':[str(x) for x in primitive.all_coeffs()],
         'content':str(content),'seconds_from_start':time.monotonic()-t0})
    Elist.append(primitive)
    print(json.dumps({'q_slice':z,'degree':int(res.degree()),'seconds':time.monotonic()-t0}),flush=True)
    (root/f'slice-{z}-resultant.json').write_text(json.dumps(records[-1],indent=2)+'\n')
g=S.gcd(*Elist)
record={'status':'PASS two exact univariate slices and resultant gcd',
    'records':records,'gcd_degree':int(g.degree()),'gcd_factorization':str(S.factor(g.as_expr())),
    'gcd_coefficients_descending':[str(x) for x in g.all_coeffs()],
    'seconds':time.monotonic()-t0,'sympy':S.__version__,'source_sha256':hashlib.sha256((root/'symbolic-normal-pilot.json').read_bytes()).hexdigest()}
(root/'two-slice-resultant-pilot.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','gcd_degree','gcd_factorization','seconds']}))
