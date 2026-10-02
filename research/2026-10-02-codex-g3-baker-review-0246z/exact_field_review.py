import sympy as s, json, time, resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(60,60)); resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
t=time.monotonic(); r=s.sqrt(2)/2; K=s.QQ.algebraic_field(r); p,q=s.symbols('p q'); lam=[1,3,6,10,15,21]
rows=[[1]*6,lam]
for z in [r,r*r]: rows.extend([[1-z**v for v in lam],[v*z**(v-1) for v in lam]])
a=[[K.from_sympy(s.sympify(z)) for z in row]+[K.one if i==0 else K.zero] for i,row in enumerate(rows)]
for k in range(6):
 j=next(i for i in range(k,6) if a[i][k]); a[k],a[j]=a[j],a[k]; v=a[k][k]; a[k]=[x/v for x in a[k]]
 for i in range(6):
  if i!=k:
   v=a[i][k]; a[i]=[x-v*y for x,y in zip(a[i],a[k])]
c=[row[-1] for row in a]
f=[s.Poly(1-p+p*q**v,p,q,domain=K) for v in lam]; one=s.Poly(1,p,q,domain=K); P=0*one; Q=0*one
for i,v in enumerate(lam):
 other=one
 for j in range(6):
  if j!=i: other*=f[j]
 P+=other*s.Poly(1-q**v,p,q,domain=K).mul_ground(c[i]); Q+=other*s.Poly(v*q**(v-1),p,q,domain=K).mul_ground(c[i])
P=P.exquo(s.Poly((q-1)**2,p,q,domain=K)); Q=Q.exquo(s.Poly((1-p)*(q-1),p,q,domain=K))
def mod(z):
 a,b=K.from_sympy(z).to_list() if len(K.from_sympy(z).to_list())==2 else (K.zero.to_list()+[s.Rational(0),z])[-2:]
 def rat(x):
  x=s.Rational(x); return int(x.p)*pow(int(x.q),-1,1009)%1009
 return (rat(a)*285+rat(b))%1009
# K primitive element is exactly sqrt(2)/2; each coefficient maps through the stated place.
record=json.loads(Path(__file__).with_name('irrational-residue-modular-critical-check.json').read_text())
for name,poly in [('P',P),('Q',Q)]:
 mapped={mon:mod(coeff) for mon,coeff in poly.terms() if mod(coeff)}
 expected={tuple(x[:2]):x[2] for x in record[name+'_terms_mod']}
 assert mapped==expected,(name,len(mapped),len(expected))
assert P.total_degree()==59 and Q.total_degree()==57
assert s.simplify(P.coeff_monomial(p**5*q**54)+1)==0
assert s.simplify(Q.coeff_monomial(p**4*q**53)+K.to_sympy(c[0]))==0
out={'exact_normal':[str(K.to_sympy(x)) for x in c],'exact_degrees':[P.total_degree(),Q.total_degree()],'all_modular_terms_match':True,'leading_terms_match':True,'seconds':time.monotonic()-t,'sympy':s.__version__}
Path(__file__).with_name('exact-field-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
