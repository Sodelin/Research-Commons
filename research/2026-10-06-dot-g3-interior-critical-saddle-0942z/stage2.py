import resource
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import sys,json,hashlib,time
from pathlib import Path
import sympy as s
start=time.monotonic(); p,q=s.symbols('p q')
raw=Path('stage1-result.json').read_bytes(); inp=json.loads(raw)
assert inp['status'].startswith('PASS') and inp['residue']=='1/2'
polys={name:s.Poly.from_dict({tuple(m):int(a) for m,a in data['terms']},(p,q),domain=s.ZZ) for name,data in inp['polynomials'].items()}
print('NEW stage2 exact resultant; input sha256',hashlib.sha256(raw).hexdigest(),flush=True)
pp=s.Poly(polys['P'].as_expr(),p,domain=s.ZZ.poly_ring(q)); qq=s.Poly(polys['Q'].as_expr(),p,domain=s.ZZ.poly_ring(q))
res=s.Poly(pp.resultant(qq),q,domain=s.ZZ)
out={'status':'PASS exact p-resultant computed; strict critical emptiness UNDECIDED','new_execution':True,'input_sha256':hashlib.sha256(raw).hexdigest(),'python':sys.version,'sympy':s.__version__,'degree_q':res.degree(),'is_zero':res.is_zero,'coefficients_descending':[str(int(a)) for a in res.all_coeffs()],'seconds':time.monotonic()-start}
Path('stage2-result.json').write_text(json.dumps(out,indent=2)+'\n')
print('resultant degree',res.degree(),'zero',res.is_zero,'seconds',out['seconds'],flush=True)
