#!/usr/bin/env python3
"""Local exact complete-forest sharp six-root known-bigon placement certificate.

All source parameters have finite algebraic encodings.
The spectral centralizer/observability argument is a separate hand proof.
"""
from functools import lru_cache
from fractions import Fraction as Q
from itertools import product
from math import comb,factorial,prod
from hashlib import sha256
from pathlib import Path
import json
import sys
import sympy as S
import obstruction_checks as F

x,y,g,r=S.symbols('x y g r')
P=8*r**9-72*r**8+216*r**7-104*r**6+72*r**5-36*r**4+25*r**3-27*r**2+9*r-1
u=S.Rational(1,3)
xx=-(4*r**3-12*r**2+6*r-1)/(2*r**3+1)
yy=(2*r**3-3*r**2+6*r-2)/(2*r**3+1)

def size(t):return 1 if isinstance(t,str) else size(t[0])+size(t[1])
def history_den(t):return 1 if isinstance(t,str) else (size(t)-1)*history_den(t[0])*history_den(t[1])
def edge_forest(f,t):
 k=sum(size(v) for v in f);j=len(f)
 if not k:return S.Integer(1)
 h=S.Rational(factorial(k-j),prod(history_den(v) for v in f))
 den=prod(comb(q,2) for q in range(j+1,k+1))
 return h/S.Integer(den)*S.sympify(F.death(k,j,t))
@lru_cache(None)
def bare(f):
 return S.expand(sum(g**sum(size(f[i]) for i in range(len(f)) if bits&(1<<i))
  *(1-g)**sum(size(f[i]) for i in range(len(f)) if not bits&(1<<i))
  *edge_forest(tuple(f[i] for i in range(len(f)) if bits&(1<<i)),x)
  *edge_forest(tuple(f[i] for i in range(len(f)) if not bits&(1<<i)),y)
  for bits in range(1<<len(f))))
@lru_cache(None)
def cuts(t):
 if isinstance(t,str):return ((t,),)
 return ((t,),)+tuple(F.canonical(a+b) for a in cuts(t[0]) for b in cuts(t[1]))
def refinements(f):
 return tuple(F.canonical(sum(parts,())) for parts in product(*(cuts(t) for t in f)))
def contract(f,small):
 token={root:f'R{i}' for i,root in enumerate(small)}
 def replace(t):
  if t in token:return token[t]
  assert isinstance(t,tuple)
  return F.join(replace(t[0]),replace(t[1]))
 return F.canonical(replace(t) for t in f)
def shape(t):return '*' if isinstance(t,str) else tuple(sorted((shape(t[0]),shape(t[1])),key=repr))
def orbit(f):return tuple(sorted((shape(t) for t in f),key=repr))
def death(k,j,t):
 if k==0:return S.Integer(j==0)
 if j==0:return S.Integer(0)
 return S.sympify(F.death(k,j,t))
def row_count(k,j):
 return S.expand(sum(S.binomial(k,a)*g**a*(1-g)**(k-a)
  *sum(death(a,b,x)*death(k-a,j-b,y)
        for b in range(max(0,j-(k-a)),min(a,j)+1))
  for a in range(k+1)))
def residue(expr):
 N,D=S.fraction(S.cancel(expr.subs({g:u,x:xx,y:yy})))
 return N,D,S.rem(N,P,r)

def run():
 lo,hi=S.Rational(54,100),S.Rational(541,1000)
 assert S.Poly(P,r).count_roots(lo,hi)==1
 # Exact rational interval lower bounds, not fitted numerical roots.
 assert -4*hi**3+12*lo**2-6*hi+1>0
 assert 2*lo**3-3*hi**2+6*lo-2>0
 assert S.cancel(1-xx-6*r*(r-1)**2/(2*r**3+1))==0
 assert S.cancel(1-yy-3*(r-1)**2/(2*r**3+1))==0
 four_delta=(g**4*(1-S.Rational(9,5)*x+x**3-x**6/5)
            +(1-g)**4*(1-S.Rational(9,5)*y+y**3-y**6/5)
            -(1-S.Rational(9,5)*row_count(2,2)+row_count(3,3)-row_count(4,4)/5))
 assert residue(four_delta)[2]==0
 counts=[]
 # Verify full forest commutation, all ten orbits at input5, all lower caps.
 for k in range(1,6):
  states=[f for d in F.merger_forests(tuple(f'A{i}' for i in range(1,k+1))).values() for f in d]
  reps={orbit(f):f for f in states}
  for f in reps.values():
   diff=sum(edge_forest(h,S.Rational(2,3))*bare(contract(f,h))
            -bare(h)*edge_forest(contract(f,h),S.Rational(2,3))
            for h in refinements(f))
   assert residue(diff)[2]==0
  counts.append({'input_roots':k,'labelled_forests':len(states),'orbits_checked':len(reps),'all_commutators_zero':True})
 # Independent count-operator construction, six-root separating mode.
 lam=lambda k:S.Integer(comb(k,2))
 V=S.zeros(6)
 for j in range(1,7):
  V[j-1,j-1]=1
  for k in range(j+1,7):V[k-1,j-1]=V[k-2,j-1]*lam(k)/(lam(k)-lam(j))
 Bmat=S.Matrix([[row_count(k,j) if j<=k else 0 for j in range(1,7)] for k in range(1,7)])
 H=S.simplify(V.inv()*Bmat*V)
 N,D,R=residue(H[5,1])
 U,W,G=S.gcdex(N,P,r)
 assert G==1 and S.expand(U*N+W*P)==1
 # True physical A-clade scalar for E(1/3) B E(1/2) minus pad swap.
 # Uses ALL spectral rows, including the modes that vanish only at the root.
 q=S.Matrix([S.Rational(2,j*(j+1)) for j in range(1,7)])
 diag=lambda z:S.diag(*(z**lam(j) for j in range(1,7)))
 response=(V*(diag(S.Rational(1,3))*H*diag(S.Rational(1,2))
            -diag(S.Rational(1,2))*H*diag(S.Rational(1,3)))*V.inv()*q)[5]
 AN,AD,AR=residue(response)
 AU,AW,AG=S.gcdex(AN,P,r)
 assert AG==1 and S.expand(AU*AN+AW*P)==1
 roots=S.polys.polytools.intervals(P,eps=S.Rational(1,10**12))
 selected=[a for a,m in roots if a[0]>=lo and a[1]<=hi]
 assert len(selected)==1
 approx=sum(selected[0])/2
 return {'status':'PASS','python':sys.version,'sympy':S.__version__,
  'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
  'forest_engine_sha256':sha256(Path(F.__file__).read_bytes()).hexdigest(),
  'exact_source':{'root_polynomial':str(P),'root_interval':['54/100','541/1000'],
                  'g':'1/3','x':str(xx),'y':str(yy),
                  'positivity':'exact rational interval inequalities; 0<x,y<1'},
  'full_forest_commutation_checks':counts,
  'sixth_mode_numerator':str(N),'sixth_mode_denominator':str(D),
  'sixth_mode_coprime_certificate':{'U':str(U),'W':str(W),'U_numerator_plus_W_P':'1'},
  'actual_A_clade':{'A_copies':6,'total_copies_on_four_taxa':9,
                   'left_pads':['1/3','1/2'],'right_pads':['1/2','1/3'],
                   'difference_numerator':str(AN),'difference_denominator':str(AD),
                   'coprime_certificate':{'U':str(AU),'W':str(AW),'U_numerator_plus_W_P':'1'}},
  'illustrative_only':{'r':str(S.N(approx,20)),'x':str(S.N(xx.subs(r,approx),20)),
                      'y':str(S.N(yy.subs(r,approx),20)),
                      'A_clade_difference':str(S.N((AN/AD).subs(r,approx),20))},
  'limits':['The known-bare-box spectral-centralizer theorem is a hand argument, not this finite replay.',
            'Full equality through5 covers all forest coordinates by exchangeability and all orbit checks.',
            'Sharp6 concerns this fixed known algebraic bigon and fixed total ordinary duration.',
            'Unknown bare parameters, arbitrary same-L chains and unknown-size stopping remain open.',
            'Research certificate; no product-specific implementation or unknown-box closure is claimed.']}

if __name__=='__main__':
 print(json.dumps(run(),indent=2,sort_keys=True))
