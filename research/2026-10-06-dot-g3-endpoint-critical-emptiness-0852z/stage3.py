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
for v in (0,1):
 mult=0; linear=s.Poly(q-v,q,domain=s.ZZ)
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
out={'status':'IN_PROGRESS exact interval root check','new_execution':True,'input_sha256':hashlib.sha256(raw).hexdigest(),'python':sys.version,'sympy':s.__version__,'primitive_content':str(content),'removed_endpoint_multiplicities':endpoints,'reduced_degree':degree,'reduced_coefficients_descending':[str(int(a)) for a in f.all_coeffs()],'mobius_coefficients_descending':[str(int(a)) for a in g.all_coeffs()],'mobius_sign_variations':variations}
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
