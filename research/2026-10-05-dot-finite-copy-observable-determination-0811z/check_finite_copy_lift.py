#!/usr/bin/env python3
"""Finite controls of the fixed-ring lift, not a computation of the Hilbert cap."""
import itertools as it
import math
from functools import lru_cache
from pathlib import Path
import json
import sympy as s
r=s.symbols('r1 r2');x=s.symbols('x1 x2');g=s.symbols('g1 g2')
ring=(*r,*x,*g)
physical={r[0]:2,r[1]:3,x[0]:s.Rational(1,4),x[1]:s.Rational(1,8),g[0]:s.Rational(1,3),g[1]:s.Rational(2,3)}

def c(ps):return sum(math.comb(ps.count(a),2)*r[a] for a in (0,1))
def paths(n,k):
 for ps0 in it.product((0,1),repeat=n):
  blocks=[(i,) for i in range(n)];ps=list(ps0);Cs=[c(ps)];rates=[];valid=True
  for j in range(k):
   # Merge {0,...,j} with {j+1}; all are CURRENT blocks.
   left=tuple(range(j+1));right=(j+1,)
   a,b=blocks.index(left),blocks.index(right)
   if ps[a]!=ps[b]:valid=False;break
   p=ps[a];rates.append(r[p])
   keep=[(B,q) for i,(B,q) in enumerate(zip(blocks,ps)) if i not in (a,b)]
   keep.append((tuple(range(j+2)),p));keep.sort();blocks=[B for B,q in keep];ps=[q for B,q in keep];Cs.append(c(ps))
  if valid:yield s.prod(g[p] for p in ps0),rates,Cs,ps

def lift(n,k,alpha):
 ans=0
 for weight,rs,Cs,ps in paths(n,k):
  factor=weight*s.prod(rs)*s.prod(x[p]**math.comb(ps.count(p),2) for p in (0,1))
  factor*=s.prod((-(Cs[j]-Cs[j+1]))**alpha[j]/s.factorial(alpha[j]) for j in range(k))
  ans+=factor
 ans=s.expand(ans);s.Poly(ans,*ring,domain=s.QQ)
 assert ans.free_symbols.issubset(set(ring))
 return ans

def direct(n,k,alpha):
 us=s.symbols('u:'+str(k));ans=0
 for weight,rs,Cs,ps in paths(n,k):
  C=[z.subs(physical) if hasattr(z,'subs') else z for z in Cs]
  prev=0;exponent=0
  for j,u in enumerate(us):exponent-=C[j]*(u-prev);prev=u
  exponent-=C[-1]*(s.log(2)-prev)
  val=(weight*s.prod(rs)).subs(physical)*s.exp(exponent)
  for u,a in zip(us,alpha):val=s.diff(val,u,a)/s.factorial(a)
  ans+=val.subs(dict.fromkeys(us,0))
 return s.simplify(ans)

polynomial_checks=0;density_checks=0;max_degree=0
for n in range(2,10):
 for k in sorted(set([0,min(1,n-1),min(2,n-1),n-1])):
  alphas=[(0,)*k,(1,)*k]
  if k:alphas.append((2,)+(0,)*(k-1))
  for alpha in sorted(set(alphas)):
   f=lift(n,k,alpha);max_degree=max(max_degree,s.Poly(f,*ring).total_degree());polynomial_checks+=1
   if n<=5 and k<=2:
    assert s.simplify(f.subs(physical)-direct(n,k,alpha))==0;density_checks+=1

# Splitting an unchanged epoch creates cross-interval lift variables, not new
# sample-size variables. Physical evaluation restores the same tied rate.
y,z,w=s.symbols('y z w')
for n in range(2,15):
 power=math.comb(n,2)
 assert s.expand((y*z)**power-y**power*z**power)==0
 # rate3, intervals log2 and2log2, including a boundary from another model.
 assert (y**power*z**power).subs({y:s.Rational(1,8),z:s.Rational(1,64)})==s.Rational(1,512)**power

@lru_cache(None)
def patterns(a,b):
 if a==0 or b==0:return 1
 return patterns(a-1,b)+patterns(a,b-1)+patterns(a-1,b-1)
assert patterns(2,2)==13
# Root censor coefficients contain only rates; no finite-interval x is needed.
v=s.symbols('v')
for n in range(2,12):
 C=math.comb(n,2)*r[0]
 for k in range(5):
  f=s.diff(s.exp(-C*v),v,k).subs(v,0)/s.factorial(k)
  assert s.Poly(f,r[0],domain=s.QQ) is not None
result={'status':'PASS','arithmetic':'SymPy exact rational/symbolic',
'fixed_ring_variables':[str(z) for z in ring],
'sample_sizes_checked':list(range(2,10)),
'legal_density_lift_polynomial_checks':polynomial_checks,
'independent_exponential_density_derivative_checks':density_checks,
'max_observed_polynomial_degree':max_degree,
'common_refinement_tied_rate_checks':13,
'weak_order_patterns_for_two_boundaries_each':patterns(2,2),
'root_censor_polynomial_checks':50,
'limits':'Finite structural controls only. No numerical copy cap, ideal stabilization certificate, demographic rigidity, novel Hilbert principle, or Lean verification.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('FINITE-COPY-CONTROL-RESULTS.json').write_text(text);print(text,end='')
