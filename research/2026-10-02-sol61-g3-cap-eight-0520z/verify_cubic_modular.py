#!/usr/bin/env python3
"""Proposal checker using fresh coefficient-list source and integer Bareiss determinants.
The elementary source weight-product and unisolvence proofs remain hand bridges.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools,json,math,time,hashlib
import sympy as S
root=Path(__file__).parent;j=json.loads((root/'both-active-cubic-result.json').read_text());t=time.monotonic()
r=S.symbols('r');lam=[1,3,6,10,15,21,28];assert j['normal']['lambda']==lam
B=[S.Poly.from_list([S.Integer(v) for v in cs],r) for cs in j['normal']['B_coefficients_descending']]
assert len(B)==7 and all(not b.is_zero for b in B)
rows=[[1]*7,lam,[1-r**l for l in lam],[l*r**(l-1) for l in lam],[1-r**(2*l) for l in lam],[l*r**(2*l-2) for l in lam]]
for row in rows:assert sum((b*S.Poly(a,r) for a,b in zip(row,B)),S.Poly(0,r)).is_zero
# A nonzero row polynomial suffices for the null-vector identity; Descartes gives its strict-domain rank.
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for k,y in enumerate(b):z[i+k]+=x*y
 return z

def bareiss(aa):
 a=[v[:] for v in aa];n=len(a);prev=1;sign=1
 for k in range(n-1):
  if a[k][k]==0:
   z=next((i for i in range(k+1,n) if a[i][k]),None)
   if z is None:return 0
   a[k],a[z]=a[z],a[k];sign=-sign
  piv=a[k][k]
  for i in range(k+1,n):
   for z in range(k+1,n):
    top=a[i][z]*piv-a[i][k]*a[k][z]
    assert top%prev==0;a[i][z]=top//prev
   a[i][k]=0
  prev=piv
 return sign*a[-1][-1]

def source_det(q,free):
 assert len(free)==5
 total=-sum(free);moment=-sum(u*l for u,l in zip(free,lam))
 last=F(moment-21*total,7);prev=total-last;ww=list(map(F,free))+[prev,last]
 assert sum(ww)==sum(w*l for w,l in zip(ww,lam))==0
 assert all(w and w.denominator==1 for w in ww);ww=[w.numerator for w in ww]
 pp=[0]*7;qq=[0]*7
 for i in range(7):
  h=[1]
  for k in range(7):
   if k!=i:h=mul(h,[1,q**lam[k]-1])
  for k,c in enumerate(h):
   pp[k]+=ww[i]*(1-q**lam[i])*c
   qq[k]+=ww[i]*lam[i]*q**(lam[i]-1)*c
 assert pp[6]==0
 qr=[qq[0]]
 for k in range(1,6):qr.append(qq[k]+qr[-1])
 assert qq[6]==-qr[5]
 a=pp[5::-1];b=qr[::-1]
 matrix=[[0]*i+a+[0]*(4-i) for i in range(5)]+[[0]*i+b+[0]*(4-i) for i in range(5)]
 return bareiss(matrix),math.prod(ww)

def residual_value(terms,u):return sum((F(c)*math.prod(F(x)**a for x,a in zip(u,aa)) for aa,c in terms),F(0))
indices=[a for a in itertools.product(range(4),repeat=4) if sum(a)<=3];assert len(indices)==35
out=[];residuals=[]
for rec in j['slices']:
 q=rec['q_slice'];assert q in (3,5)
 terms=rec['residual_terms'];assert len(terms)==35
 assert len({tuple(a) for a,c in terms})==35 and all(len(a)==5 and sum(a)==3 for a,c in terms)
 # Unisolvent simplex is an identity check ONLY with the proven cubic degree bound.
 fixtures=[[7*(1+k) for k in a]+[7] for a in indices]
 # Different added controls from author's fixtures.
 fixtures += [[7*(2+i),7*(3+2*i),7*(4+3*i),7*(5+4*i),7*(6+5*i)] for i in range(1,11)]
 for u in fixtures:
  determinant,wp=source_det(q,u);assert residual_value(terms,u)*wp==determinant
 ep=S.Poly(0,r)
 for aa,c in terms:ep+=S.Poly(S.Rational(c),r)*math.prod(b**a for b,a in zip(B,aa))
 _,ei=ep.clear_denoms(convert=True);_,primitive=ei.primitive()
 proposal=S.Poly.from_list([S.Integer(c) for c in rec['specialized_primitive_coefficients_descending']],r)
 assert primitive==proposal;assert primitive.degree()==231
 residuals.append(proposal)
 out.append({'q':q,'fresh_integer_source_determinants':len(fixtures),'exact_specialization_identity':True})
G=S.gcd(*residuals);assert G==S.Poly(1,r)
assert j['residual_gcd_degree']==0
# Explicit degree-preserving modular coprimality certificate, lifted to Q by Gauss.
prime=1009
assert all(int(v.LC())%prime for v in residuals)
a,b=[v.set_modulus(prime) for v in residuals]
ss,tt,gg=S.gcdex(a,b)
assert gg==S.Poly(1,r,modulus=prime)
assert (ss*a+tt*b-1).is_zero
modrec={"prime":prime,"input_degrees_preserved":True,
        "s_coefficients_descending":[int(c)%prime for c in ss.all_coeffs()],
        "t_coefficients_descending":[int(c)%prime for c in tt.all_coeffs()]}
(root/"modular-bezout.json").write_text(json.dumps(modrec,indent=2)+"\n")
receipt={'status':'PASS','certificate_sha256':hashlib.sha256((root/'both-active-cubic-result.json').read_bytes()).hexdigest(),
 'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'source_build':'fresh ascending coefficient convolutions, integer Bareiss determinant',
 'all_six_normal_polynomial_identities':True,'controls':out,'exact_residual_gcd':1,'degree_preserving_modular_bezout_prime':prime,
 'scope':'The 35 nodes certify whole cubic identity under separately proved source divisibility/homogeneity; 20 additional controls are samples only. No Lean or arbitrary-input recognition.',
 'seconds':time.monotonic()-t}
(root/'modular-coefficient-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
