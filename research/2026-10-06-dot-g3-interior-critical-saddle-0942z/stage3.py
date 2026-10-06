import resource
resource.setrlimit(resource.RLIMIT_CPU,(60,60))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import sys,json,hashlib,time
from pathlib import Path
import sympy as s
start=time.monotonic(); q,t=s.symbols('q t')
raw=Path('stage2-result.json').read_bytes(); inp=json.loads(raw)
assert not inp['is_zero']
f=s.Poly.from_list([int(a) for a in inp['coefficients_descending']],q,domain=s.ZZ)
content,f=f.primitive(); endpoints={}
slice_checks={}
p=s.symbols('p'); raw1=json.loads(Path('stage1-result.json').read_text())
polys={name:s.Poly.from_dict({tuple(m):int(a) for m,a in data['terms']},(p,q),domain=s.ZZ) for name,data in raw1['polynomials'].items()}
for v in (s.Rational(1,2),s.Rational(1,4)):
 gcd=s.gcd(s.Poly(polys['P'].as_expr().subs(q,v),p,domain=s.QQ),s.Poly(polys['Q'].as_expr().subs(q,v),p,domain=s.QQ))
 original=str(gcd.as_expr())
 for endpoint in (0,1):
  while not gcd.is_zero and gcd.degree()>0 and gcd.eval(endpoint)==0: gcd=gcd.exquo(s.Poly(p-endpoint,p,domain=s.QQ))
 cnt=int(gcd.count_roots(0,1)) if gcd.degree()>0 else 0
 slice_checks[str(v)]={'p_gcd':original,'strict_p_count':cnt}
 assert cnt==0, 'Interior q slice has strict critical pairs; inspect saved gcd'
for v in (0,1,s.Rational(1,2),s.Rational(1,4)):
 mult=0; linear=s.Poly(q*v.q-v.p,q,domain=s.ZZ) if isinstance(v,s.Rational) else s.Poly(q-v,q,domain=s.ZZ)
 while f.eval(v)==0:
  f=f.exquo(linear); mult+=1
 endpoints[str(v)]=mult
coeff=f.all_coeffs(); degree=f.degree()
# q=t/(1+t), so positive t is exactly0<q<1.
g=s.Poly(0,t,domain=s.ZZ)
for i,a in enumerate(coeff):
 power=degree-i
 g+=s.Poly(int(a)*t**power*(1+t)**i,t,domain=s.ZZ)
signs=[s.sign(a) for a in g.all_coeffs() if a]
variations=sum(1 for a,b in zip(signs,signs[1:]) if a!=b)
out={'status':'IN_PROGRESS exact interval root check','new_execution':True,'input_sha256':hashlib.sha256(raw).hexdigest(),'python':sys.version,'sympy':s.__version__,'primitive_content':str(content),'removed_known_slice_multiplicities':endpoints,'strict_interior_slice_checks':slice_checks,'reduced_degree':degree,'reduced_coefficients_descending':[str(int(a)) for a in f.all_coeffs()],'mobius_coefficients_descending':[str(int(a)) for a in g.all_coeffs()],'mobius_sign_variations':variations}
Path('stage3-result.json').write_text(json.dumps(out,indent=2)+'\n')
print('NEW stage3 reduced degree',degree,'removed',endpoints,'Mobius variations',variations,flush=True)
if variations==0:
 count=0; method='Descartes after exact q=t/(1+t); all nonzero transformed coefficients have one sign'
else:
 count=int(f.count_roots(0,1)); method='SymPy exact real-root count on [0,1] after removing all endpoint roots'
out['strict_q_root_count']=count; out['method']=method
out['status']='PASS no strict q roots; hence no strict critical pairs' if count==0 else 'UNKNOWN strict pair feasibility; resultant has strict q candidates'
out['seconds']=time.monotonic()-start
Path('stage3-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'q roots',count,'seconds',out['seconds'],flush=True)
