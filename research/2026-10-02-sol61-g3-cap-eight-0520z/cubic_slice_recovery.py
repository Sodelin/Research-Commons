#!/usr/bin/env python3
"""Exact cubic residual interpolation after the source weight-product theorem.
Author: GPT-6.1 Sol / continue_g_research, 2026-10-02. Hand theorem dependency explicit.
"""
from pathlib import Path
import itertools,json,time,hashlib,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(180,180))
resource.setrlimit(resource.RLIMIT_AS,(1200*1024**2,1200*1024**2))
root=Path(__file__).parent;t0=time.monotonic()
p,r=S.symbols('p r');lam=[1,3,6,10,15,21,28];d=7
# Genuine paired normal constraints; cofactor construction has no normalization division.
rows=[[S.Poly(1,r) for l in lam],[S.Poly(l,r) for l in lam],
      [S.Poly(1-r**l,r) for l in lam],[S.Poly(l*r**(l-1),r) for l in lam],
      [S.Poly(1-r**(2*l),r) for l in lam],[S.Poly(l*r**(2*l-2),r) for l in lam]]
C=[]
for i in range(d):
 cols=[j for j in range(d) if j!=i];v=S.Poly(0,r)
 for perm in itertools.permutations(cols):
  inv=sum(perm[j]>perm[k] for j in range(d-1) for k in range(j+1,d-1))
  term=S.Poly((-1)**(inv+i),r)
  for k,j in enumerate(perm):term*=rows[k][j]
  v+=term
 C.append(v)
assert all(sum((rows[k][i]*C[i] for i in range(d)),S.Poly(0,r)).is_zero for k in range(6))
g=C[0]
for v in C[1:]:g=S.gcd(g,v)
B=[v.exquo(g) for v in C]
assert all(not v.is_zero for v in B)
normal={'lambda':lam,'C_degrees':[int(v.degree()) for v in C], 'common_factor':str(S.factor(g.as_expr())),
 'B_degrees':[int(v.degree()) for v in B], 'B_coefficients_descending':[[str(x) for x in v.all_coeffs()] for v in B]}
(root/'both-active-normal.json').write_text(json.dumps(normal,indent=2)+'\n')
print('normal',normal['B_degrees'],'seconds',time.monotonic()-t0,flush=True)
indices=[a for a in itertools.product(range(4),repeat=4) if sum(a)<=3]
indices.sort(key=lambda a:(sum(a),a));assert len(indices)==35
xs=S.symbols('x0:4');us=S.symbols('u0:5');slice_recs=[];residuals=[]
for q in (3,5):
 f=[S.Poly(1-p+p*S.Integer(q)**l,p) for l in lam]
 basis=[S.prod(f[j] for j in range(d) if j!=i) for i in range(d)]
 # Source P and Q depend linearly on the weights, so cache actual coefficient columns.
 pc=[[basis[i].nth(k)*(1-S.Integer(q)**lam[i]) for i in range(d)] for k in range(6,-1,-1)]
 qc=[[basis[i].nth(k)*lam[i]*S.Integer(q)**(lam[i]-1) for i in range(d)] for k in range(6,-1,-1)]
 def weights(u):
  t=-sum(u);s=-sum(ui*l for ui,l in zip(u,lam))
  last=(s-lam[-2]*t)/S.Integer(lam[-1]-lam[-2]);prev=t-last
  return list(u)+[prev,last]
 def actual(u):
  w=weights(u)
  aa=[sum(c*wi for c,wi in zip(v,w)) for v in pc]
  bb=[sum(c*wi for c,wi in zip(v,w)) for v in qc]
  assert aa[0]==0
  pp=S.Poly.from_list(aa[1:],p);qq0=S.Poly.from_list(bb,p)
  qq=qq0.exquo(S.Poly(1-p,p));assert qq.degree()<=5
  a=[pp.nth(k) for k in range(5,-1,-1)];b=[qq.nth(k) for k in range(5,-1,-1)]
  mm=S.Matrix([[0]*i+a+[0]*(4-i) for i in range(5)]+[[0]*i+b+[0]*(4-i) for i in range(5)])
  det=mm.det(method='domain-ge')
  wp=S.prod(w);assert wp!=0
  return S.cancel(det/wp),det,w
 vals={a:actual([7*(1+j) for j in a]+[7])[0] for a in indices}
 FF=0
 for a in indices:
  coeff=sum((-1)**(sum(a)-sum(j))*S.prod(S.binomial(ai,ji) for ai,ji in zip(a,j))*vals[j]
            for j in itertools.product(*(range(ai+1) for ai in a)))
  basisexpr=S.prod(S.prod(xs[i]-1-k for k in range(ai))/S.factorial(ai) for i,ai in enumerate(a))
  FF+=coeff*basisexpr
 FF=S.Poly(S.expand(FF),*xs)
 assert FF.total_degree()<=3
 CR=S.Poly(sum(coeff*S.prod(us[i]**a[i] for i in range(4))*us[4]**(3-sum(a))/343 for a,coeff in FF.terms()),*us)
 assert CR.total_degree()==3
 # Every interpolation point is checked, plus unrelated exact points, including nonunit homogenization.
 fixtures=[[i+2,i+3,i+4,i+5,i+6] for i in range(10)]
 for u in fixtures:
  rr,det,w=actual(u)
  assert CR.as_expr().subs(dict(zip(us,u)))==rr
  assert S.prod(w)*CR.as_expr().subs(dict(zip(us,u)))==det
 for a in indices:assert FF.as_expr().subs(dict(zip(xs,[1+j for j in a])))==vals[a]
 ep=S.Poly(0,r)
 for aa,coeff in CR.terms():
  ep+=S.Poly(coeff,r)*S.prod(B[i]**aa[i] for i in range(5))
 content,primitive=ep.clear_denoms(convert=True)[1].primitive();residuals.append(primitive)
 rec={'q_slice':q,'method':'35-point exact simplex finite-difference cubic interpolation; genuine fixed-degree source determinants',
      'structural_dependency':'WEIGHT-PRODUCT-RESULTANT-LEMMA.md hand proof, not kernel verified',
      'free_weight_constraint':list(map(str,weights(us))), 'residual_terms':[[list(aa),str(c)] for aa,c in CR.terms()],
      'simplex_checks':35,'independent_numeric_determinant_controls':len(fixtures),
      'specialized_degree':int(ep.degree()),'specialized_content':str(content),
      'specialized_primitive_coefficients_descending':[str(c) for c in primitive.all_coeffs()]}
 slice_recs.append(rec)
 (root/f'cubic-slice-{q}.json').write_text(json.dumps(rec,indent=2)+'\n')
 print('slice',q,'terms',len(CR.terms()),'degree',ep.degree(),'seconds',time.monotonic()-t0,flush=True)
G=S.gcd(*residuals);gc,fs=S.factor_list(G)
rec={'status':'PASS exact residual interpolation/controls; strict nonvanishing conclusion depends on source structural hand proof',
     'normal':normal,'slices':slice_recs,'residual_gcd_degree':int(G.degree()),'residual_gcd':str(S.factor(G.as_expr())),
     'residual_gcd_coefficients_descending':[str(x) for x in G.all_coeffs()],
     'factors':[{'degree':int(f.degree()),'multiplicity':int(e),'coefficients_descending':[str(x) for x in f.all_coeffs()],
       'negative_monomials':[[int(mon[0]),str(c)] for mon,c in f.terms() if c<0]} for f,e in fs],
     'seconds':time.monotonic()-t0,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'sympy':S.__version__}
(root/'both-active-cubic-result.json').write_text(json.dumps(rec,indent=2)+'\n')
print('DONE gcd',G.degree(),S.factor(G.as_expr()),'seconds',time.monotonic()-t0,flush=True)
