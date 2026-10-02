#!/usr/bin/env python3
"""Exact source/weight-constraint controls for G3 resultant divisibility.
Contributor: GPT-6.1 Sol / advance_general_g3_g4, 2026-10-02.
No all-r residual nonvanishing or general-recognition claim is tested here.
"""
from pathlib import Path
from itertools import combinations
import hashlib,json,time
import sympy as S

p=S.symbols('p')

def weights(d,alpha,beta,lam):
 vs=S.symbols('u0:'+str(d-alpha-beta))
 if alpha==0 and beta==0:return list(vs),vs
 if alpha+beta==1:
  last=-sum(vs) if beta else -sum(v*l for v,l in zip(vs,lam))/lam[-1]
  return list(vs)+[last],vs
 t=-sum(vs);s=-sum(v*l for v,l in zip(vs,lam))
 last=(s-lam[-2]*t)/(lam[-1]-lam[-2]);prev=t-last
 return list(vs)+[prev,last],vs

def sylvester(P,Q,m,n):
 a=[P.coeff_monomial(p**i) for i in range(m,-1,-1)]
 b=[Q.coeff_monomial(p**i) for i in range(n,-1,-1)]
 rows=[]
 for i in range(n):rows.append([0]*i+a+[0]*(n-1-i))
 for i in range(m):rows.append([0]*i+b+[0]*(m-1-i))
 return S.Matrix(rows)

rows=[];begin=time.time()
for alpha,beta in ((0,0),(0,1),(1,0),(1,1)):
 d=5+alpha+beta;lam=[j*(j-1)//2 for j in range(2,d+2)]
 w,vs=weights(d,alpha,beta,lam)
 assert not alpha or S.expand(sum(wi*l for wi,l in zip(w,lam)))==0
 assert not beta or S.expand(sum(w))==0
 assert all(S.Poly(wi,*vs).total_degree()==1 for wi in w)
 assert all(S.Poly(S.gcd(a,b),*vs).total_degree()==0 for a,b in combinations(w,2))
 for q in (3,5):
  f=[1-p+p*S.Integer(q)**l for l in lam]
  PP=S.Poly(S.expand(sum(w[i]*(1-S.Integer(q)**lam[i])*S.prod(f[j] for j in range(d) if j!=i) for i in range(d))),p)
  QQ=S.Poly(S.expand(sum(w[i]*lam[i]*S.Integer(q)**(lam[i]-1)*S.prod(f[j] for j in range(d) if j!=i) for i in range(d))),p)
  if alpha:
   quotient,rem=S.div(QQ,S.Poly(1-p,p));assert rem.is_zero;QQ=quotient
  m=d-1-beta;n=d-1-alpha
  assert PP.degree()<=m and QQ.degree()<=n
  checks=[]
  for i,wi in enumerate(w):
   pivot=next(v for v in vs if S.diff(wi,v)!=0)
   solution=S.expand(-(wi-wi.coeff(pivot)*pivot)/wi.coeff(pivot))
   sub={pivot:solution}
   Pi=S.Poly(S.expand(PP.as_expr().subs(sub)),p);Qi=S.Poly(S.expand(QQ.as_expr().subs(sub)),p)
   assert S.rem(Pi,S.Poly(f[i],p)).is_zero
   assert S.rem(Qi,S.Poly(f[i],p)).is_zero
   checks.append({'i':i,'source_factor_divides_P':True,'source_factor_divides_Q_reduced':True})
  # A full numeric fixed-degree Sylvester control, with all constraints active.
  sample={v:i+2 for i,v in enumerate(vs)}
  Pnum=S.Poly(PP.as_expr().subs(sample),p);Qnum=S.Poly(QQ.as_expr().subs(sample),p)
  det=sylvester(Pnum,Qnum,m,n).det(method='domain-ge')
  assert det!=0
  rows.append({'alpha':alpha,'beta':beta,'d':d,'exponents':lam,'q_slice':q,'P_bound':m,'Q_reduced_bound':n,'fixed_sylvester_size':m+n,'resultant_weight_degree':m+n,'universal_weight_product_degree':d,'quotient_homogeneous_degree':m+n-d,'coordinate_factor_checks':checks,'pairwise_coordinate_gcd':'constant','numeric_fixed_resultant_nonzero':True,'numeric_resultant_sha256':hashlib.sha256(str(det).encode()).hexdigest()})
  print('PASS',alpha,beta,'d',d,'q',q,'quotient degree',m+n-d,flush=True)
rec={'status':'PASS','scope':'exact bounded source-factor and active-weight-ring controls; generic divisibility and homogeneity are hand proofs','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'sympy':S.__version__,'configurations':rows,'seconds':time.time()-begin}
Path(__file__).with_name('resultant-structure-checks.json').write_text(json.dumps(rec,indent=2,sort_keys=True)+'\n')
