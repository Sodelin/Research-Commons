import resource
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import sys,json,hashlib,time
from pathlib import Path
import sympy as s
start=time.monotonic(); p,q=s.symbols('p q')
lams=(1,3,6,10,15,21); c=(297,-275,154,-54,11,-1)
print('NEW stage1',sys.version,'sympy',s.__version__,flush=True)
assert sum(c)==132
for k in range(1,6): assert sum(ci*li**k for ci,li in zip(c,lams))==0
f=[s.Poly(1-p+p*q**li,p,q,domain=s.ZZ) for li in lams]
P0=s.Poly(0,p,q,domain=s.ZZ); Q0=P0
for i in range(6):
 prod=s.Poly(1,p,q,domain=s.ZZ)
 for j in range(6):
  if j!=i: prod*=f[j]
 P0+=c[i]*s.Poly(1-q**lams[i],p,q,domain=s.ZZ)*prod
 Q0+=c[i]*lams[i]*s.Poly(q**(lams[i]-1),p,q,domain=s.ZZ)*prod
P=P0.exquo(s.Poly((q-1)**6,p,q,domain=s.ZZ))
Q=Q0.exquo(s.Poly((1-p)*(q-1)**5,p,q,domain=s.ZZ))
assert P*s.Poly((q-1)**6,p,q,domain=s.ZZ)==P0
assert Q*s.Poly((1-p)*(q-1)**5,p,q,domain=s.ZZ)==Q0
out={'status':'PASS exact construction and divisions; strict critical emptiness UNDECIDED','new_execution':True,'python':sys.version,'sympy':s.__version__,'lambda':list(lams),'normal':list(c),'polynomials':{}}
for name,poly in [('P',P),('Q',Q)]:
 data={'degree_p':poly.degree(p),'degree_q':poly.degree(q),'total_degree':poly.total_degree(),'terms':[[list(m),str(int(a))] for m,a in poly.terms()],'boundary':{}}
 for var in (p,q):
  for v in (0,1): data['boundary'][str(var)+'='+str(v)]=str(s.factor(poly.as_expr().subs(var,v)))
 out['polynomials'][name]=data
 print(name,'degrees',data['degree_p'],data['degree_q'],'terms',len(data['terms']),data['boundary'],flush=True)
out['seconds']=time.monotonic()-start
Path('stage1-result.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS stage1 seconds',out['seconds'],flush=True)
