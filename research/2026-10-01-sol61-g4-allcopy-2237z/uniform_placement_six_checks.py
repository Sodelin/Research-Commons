#!/usr/bin/env python3
"""Exact universal supplied-one-bigon pad recovery certificate.

This checks a finite polynomial certificate, not an empirical ideal plateau.
"""
import json
from fractions import Fraction as Q
from hashlib import sha256
from math import comb
from pathlib import Path
import sys
import sympy as S

x,y,g,r=S.symbols('x y g r')
lam=lambda n:S.Integer(comb(n,2))
def edge(k,j,t):
 if k==0:return S.Integer(j==0)
 if j==0:return S.Integer(0)
 prefix=S.prod(lam(i) for i in range(j+1,k+1))
 return S.expand(prefix*sum(t**lam(i)/S.prod(lam(h)-lam(i) for h in range(j,k+1) if h!=i) for i in range(j,k+1)))
def bare(k,j):
 return S.expand(sum(S.binomial(k,a)*g**a*(1-g)**(k-a)
  *sum(edge(a,b,x)*edge(k-a,j-b,y) for b in range(max(0,j-(k-a)),min(a,j)+1))
  for a in range(k+1)))
def run():
 here=Path(__file__).parent
 polys={k:S.sympify(v,locals={'g':g,'r':r}) for k,v in json.loads((here/'commutator-generators.json').read_text()).items()}
 certificates=json.loads((here/'exceptional-cubic-certificates.json').read_text())
 V=S.zeros(6)
 for j in range(1,7):
  V[j-1,j-1]=1
  for k in range(j+1,7):V[k-1,j-1]=V[k-2,j-1]*lam(k)/(lam(k)-lam(j))
 B=S.Matrix([[bare(k,j) if j<=k else 0 for j in range(1,7)] for k in range(1,7)])
 H=S.simplify(V.inv()*B*V)
 # Derive the positive delta4=0 parameterization from current-lineage routing.
 X,Y=S.symbols('X Y');u=g;v=1-g;A=u*X;C=v*Y
 d=(v*A**3+u*C**3-3*u*v*(A-C)**2)/5
 delta=B[3,0]-(1-S.Rational(9,5)*B[1,1]+B[2,2]-B[3,3]/5)
 assert S.expand(delta.subs({x:1-X,y:1-Y})-d)==0
 t=3*g*(1-g)*(r-1)**2/((1-g)*r**3+g)
 xx=1-r*t/g;yy=1-t/(1-g)
 assert S.cancel(delta.subs({x:xx,y:yy}))==0
 mode_checks=[]
 for i,j,key in [(5,3,'m53'),(6,2,'m62'),(6,4,'m64')]:
  N,D=S.fraction(S.cancel(H[i-1,j-1].subs({x:xx,y:yy})))
  quotient,rem=S.div(N,polys[key],g,r)
  assert rem==0
  # Verify exactly that the removed numerator factors are only forbidden
  # g=0, g=1, r=1 factors, apart from a nonzero rational constant.
  ratio=S.cancel(quotient/(g**4*(g-1)**4*(r-1)**9))
  assert not ratio.free_symbols and ratio!=0
  df=S.factor(D)
  mode_checks.append({'mode':[i,j],'stripped_polynomial':key,
                      'removed_nonzero_constant':str(ratio),
                      'denominator':str(df),'source_identity_verified':True})
 f1=r**3-9*r**2+27*r-9;f2=9*r**3-27*r**2+9*r-1
 R1=S.resultant(polys['m53'],polys['m62'],g)
 R2=S.resultant(polys['m53'],polys['m64'],g)
 common=81*r**24*(r-1)**11*f1*f2
 assert S.expand(S.gcd(R1,R2)-common)==0
 # A separate explicit univariate Bezout identity verifies the gcd step.
 U,Vb,G=S.gcdex(R1,R2,r)
 assert S.expand(U*R1+Vb*R2-G)==0
 assert S.cancel(G/common)==S.Rational(1,729)
 exceptional=[]
 for cert,fi,target in zip(certificates,[f1,f2],[g,g-1]):
  assert S.expand(S.sympify(cert['cubic'])-fi)==0
  a,b,c=(S.sympify(cert[key],locals={'g':g,'r':r}) for key in ['U','V','W'])
  assert S.expand(a*polys['m53']+b*polys['m62']+c*fi-target)==0
  exceptional.append({'cubic':str(fi),'forced_target':str(target),'identity_verified':True})
 # Exact rational source fixtures check the reconstruction equation at every
 # possible mode used by the algorithm. One fixture is cap4-degenerate.
 fixtures=[(Q(1,2),Q(3,4),Q(1,3)),(Q(2,3),Q(1,3),Q(1,2)),
           (Q(37,42),Q(5,6),Q(1,2)),(Q(9,10),Q(3,10),Q(1,5))]
 reconstruction=[]
 modes=[(4,2),(5,3),(6,2),(6,4)]
 for theta in fixtures:
  Hb=H.subs(dict(zip([x,y,g],map(S.Rational,theta))))
  a,b=S.Rational(1,3),S.Rational(1,2);Z=a*b
  D1=S.diag(*(a**lam(k) for k in range(1,7)))
  D2=S.diag(*(b**lam(k) for k in range(1,7)))
  Hp=D1*Hb*D2
  mode=next((n,j) for n,j in modes if Hb[n-1,j-1]!=0)
  n,j=mode;ratio=S.cancel(Hp[n-1,j-1]/(Z**lam(j)*Hb[n-1,j-1]))
  assert ratio==a**(lam(n)-lam(j))
  recovered_a=S.real_root(ratio,int(lam(n)-lam(j)))
  assert recovered_a==a and Z/recovered_a==b
  reconstruction.append({'bare':[str(z) for z in theta],'mode':list(mode),
                         'positive_root_power':int(lam(n)-lam(j)),
                         'recovered_leading':str(recovered_a),'recovered_trailing':str(Z/recovered_a)})
 return {'status':'PASS','python':sys.version,'sympy':S.__version__,
  'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
  'generator_sha256':sha256((here/'commutator-generators.json').read_bytes()).hexdigest(),
  'exceptional_certificate_sha256':sha256((here/'exceptional-cubic-certificates.json').read_bytes()).hexdigest(),
  'source_mode_identities':mode_checks,
  'resultant_53_62':str(S.factor(R1)),'resultant_53_64':str(S.factor(R2)),
  'resultant_gcd':str(common),
  'resultant_bezout':{'U':str(U),'V':str(Vb),'G':str(G),'identity_verified':True},
  'exceptional_cubic_identities':exceptional,
  'exact_pad_reconstruction_controls':reconstruction,
  'conclusion':'No positive supplied independent bigon has all four count modes42,53,62,64 zero; both unknown pads are reconstructed through6.',
  'limits':['The source positivity and spectral-centralizer/observability bridges have hand proofs.',
            'Uniform six is for a supplied bare one-bigon with two unknown ordinary pads.',
            'Unknown bare equality, arbitrary same-L products and unknown-size recognition remain separate open obligations.']}

if __name__=='__main__':
 print(json.dumps(run(),indent=2,sort_keys=True))
