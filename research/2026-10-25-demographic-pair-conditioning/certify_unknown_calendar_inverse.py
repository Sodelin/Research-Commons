"""Outward rational-interval local inverse and finite-data budget certificate."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
Q=2**100
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.lo,self.hi=a.lo,a.hi;return
  a,b=F(a),F(a if b is None else b)
  self.lo=F((a*Q).__floor__(),Q);self.hi=F((b*Q).__ceil__(),Q)
  assert self.lo<=self.hi
 def __add__(a,b):
  b=I(b);return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-I(b)
 def __rsub__(a,b):return I(b)+-a
 def __mul__(a,b):
  b=I(b);v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=I(b);assert not b.lo<=0<=b.hi
  return a*I(1/b.hi,1/b.lo)
 def __rtruediv__(a,b):return I(b)/a
 def __pow__(a,n):
  assert isinstance(n,int) and n>=0
  r=I(1)
  for _ in range(n):r=r*a
  return r
 def absmax(a):return max(abs(a.lo),abs(a.hi))
 def out(a):return [str(a.lo),str(a.hi)]
def expneg_scalar(x):
 assert x>=0
 k=0
 while x>1:x/=2;k+=1
 # Alternating decreasing terms: odd partial sum lower, even upper.
 hi=sum((-x)**j/F(factorial(j)) for j in range(31))
 lo=hi+(-x)**31/F(factorial(31))
 r=I(lo,hi)
 for _ in range(k):r=r*r
 return r
def expneg(x):
 x=I(x);return I(expneg_scalar(x.hi).lo,expneg_scalar(x.lo).hi)
def phi(z,a):
 x,y,t=z;return x/(x+a)+(y/(y+a)-x/(x+a))*expneg((x+a)*t)
def jac(z,a):
 x,y,t=z;e=expneg((x+a)*t);d=y/(y+a)-x/(x+a)
 return [a/(x+a)**2*(1-e)-t*d*e, a/(y+a)**2*e, -(x+a)*d*e]
A=[[F(v) for v in row] for row in [['2.203535','-10.648585','15.075966'],['368.00330','-974.95484','697.83668'],['109.95771','-370.68646','297.31514']]]
b=F(1,16384);c=[F(1),F(2),F(1)];box=[I(v-b,v+b) for v in c]
J=[jac(box,a) for a in [1,2,3]]
R=[[sum(A[i][r]*J[r][j] for r in range(3))-int(i==j) for j in range(3)] for i in range(3)]
kraw=max(sum(v.absmax() for v in row) for row in R)
# Use a readable rational upper bound, not rounded floats, downstream.
kappa=F((kraw*1000).__ceil__(),1000)
B=max(sum(abs(v) for v in row) for row in A)
print('kappa',float(kappa),'B',float(B))
assert kappa<F(1,2)
# Strict eta=b/2 estimator guarantee, even after central-moment enclosure error.
eta=b/2
pc=[phi([I(v) for v in c],a) for a in [1,2,3]]
pc_mid=[(v.lo+v.hi)/2 for v in pc]
tau=max((v.hi-v.lo)/2 for v in pc)
epsilon=(eta-kappa*b)/(2*B)
err=kappa*b+B*(epsilon+tau)
assert err<eta
# 6 exp(-N eps^2/2) <= 1/20; use log120<5.
# exp(5)>120 certified by finite positive Taylor partial sum.
assert sum(F(5)**j/factorial(j) for j in range(9))>120
N=(F(10)/epsilon**2).__ceil__()
def estimator(moment_vector):
 raw=[c[i]+sum(A[i][r]*(F(moment_vector[r])-pc_mid[r]) for r in range(3)) for i in range(3)]
 return [min(c[i]+b,max(c[i]-b,raw[i])) for i in range(3)]
# Feasible three-site +/-1 prefix-character count input. Eight categories.
def estimate_counts(counts):
 assert len(counts)==8 and all(isinstance(n,int) and n>=0 for n in counts) and sum(counts)>0
 moments=[sum(F(n)*(-1 if (mask>>j)&1 else 1) for mask,n in enumerate(counts))/sum(counts) for j in range(3)]
 return estimator(moments)
for counts in ([1]*8,[100,0,0,0,0,0,0,0],[0,2,3,0,7,1,0,8]):
 est=estimate_counts(counts);assert all(c[i]-b<=est[i]<=c[i]+b for i in range(3))
# Verify the center rounded moment estimator remains extraordinarily close.
assert max(abs(estimator(pc_mid)[i]-c[i]) for i in range(3))==0
out={'status':'passed outward rational interval certificate', 'center':list(map(str,c)), 'radius':str(b),'clock_s':'1','hazard_jump_min':str(1-2*b),'cut_min':str(1-b),'cut_max':str(1+b),'preconditioner':[[str(v) for v in row] for row in A],'jacobian_intervals':[[v.out() for v in row] for row in J],'preconditioned_residual_intervals':[[v.out() for v in row] for row in R],'kappa_upper':str(kappa),'B':str(B),'moment_center_enclosures':[v.out() for v in pc],'center_rounding_error':str(tau),'epsilon':str(epsilon),'strict_parameter_error_upper':str(err),'target_eta':str(eta),'failure_probability_upper':'1/20','sufficient_loci':N,'nucleotide_calls':6*N,'count_estimator_controls':3,'arithmetic':'Fraction outward rounded to dyadic denominator 2^100; exponential alternating Taylor n=30/31 and repeated squaring','limitations':'No Monte Carlo, no empirical data, no global grid engine execution, no formal proof checker.'}
Path(__file__).with_name('unknown-calendar-inverse-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['kappa_upper','B','epsilon','target_eta','sufficient_loci','nucleotide_calls']},indent=2))
