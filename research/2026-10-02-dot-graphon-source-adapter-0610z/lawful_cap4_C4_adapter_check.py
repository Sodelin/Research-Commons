"""Hidden C4 diagnostic on an EXISTING accepted lawful positive cap4 replica.
No new replica/source construction, observation primitive, or all-prefix result.
The rational box is an input to the inherited exact existence certificate.
Contributor: dot / continue_lean_proofs_two, 2026-10-02.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import json,hashlib,time,sys
import sympy as S
P=Path(__file__).parent;t=time.monotonic();C=Path(sys.argv[1]) if len(sys.argv)>1 else P/'ordinary-cap4-certificate.json'
j=json.loads(C.read_text());names='x1 y1 g1 z1 x2 y2 g2 z2 x3 y3 g3 z3'.split();radius=F(1,10**25)

class I:
 def __init__(self,a,b=None):self.lo=F(a);self.hi=F(a if b is None else b);assert self.lo<=self.hi
 def __add__(self,o):
  if not isinstance(o,I):o=I(o)
  return I(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,o):return self+(-o if isinstance(o,I) else -I(o))
 def __rsub__(self,o):return I(o)-self
 def __mul__(self,o):
  if not isinstance(o,I):o=I(o)
  ss=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
  return I(min(ss),max(ss))
 __rmul__=__mul__
 def __pow__(self,n):
  assert n>=0
  if n==0:return I(1)
  if n%2==0 and self.lo<=0<=self.hi:return I(0,max(abs(self.lo),abs(self.hi))**n)
  return I(min(self.lo**n,self.hi**n),max(self.lo**n,self.hi**n))
 def reciprocal(self):assert self.lo>0;return I(1/self.hi,1/self.lo)
 def __truediv__(self,o):return self*(o if isinstance(o,I) else I(o)).reciprocal()
 def record(self):
  den=10**50;lo=self.lo.numerator*den//self.lo.denominator;hi=-((-self.hi.numerator*den)//self.hi.denominator)
  return {'outward_rational_lower':str(F(lo,den)),'outward_rational_upper':str(F(hi,den))}

parameters={name:I(value) for name,value in j['fixed'].items()}
for name,center in zip(j['variables'],j['center']):parameters[name]=I(F(center)-radius,F(center)+radius)
assert set(parameters)==set(names) and all(0<x.lo<=x.hi<1 for x in parameters.values())

def beta2(x,y,g):h=1-g;return g*g*x+h*h*y+2*g*h
def etaC4(x,y,g):
 h=1-g
 return g**4*x**4+h**4*y**4+4*g**3*h*x*x+4*g*h**3*y*y+4*g*g*h*h*x*y+2*g*g*h*h

# Exact symbolic 16-color cycle density confirms the compact formula, not an
# inferred observable formula. This remains a hidden graphon statistic.
x,y,g=S.symbols('x y g');h=1-g
cycle=0
for aa in product((0,1),repeat=4):
 weight=S.prod(g if a==0 else h for a in aa)
 edges=S.prod(x if aa[k]==aa[(k+1)%4]==0 else y if aa[k]==aa[(k+1)%4]==1 else 1 for k in range(4))
 cycle+=weight*edges
assert S.expand(cycle-etaC4(x,y,g))==0
ratio=I(1);cells=[]
for k in range(1,4):
 xx,yy,gg=[parameters[f'{a}{k}'] for a in ('x','y','g')]
 bb=beta2(xx,yy,gg);ee=etaC4(xx,yy,gg);rr=ee/(bb**4)
 assert rr.lo>1
 cells.append({'cell':k,'beta2':bb.record(),'etaC4':ee.record(),'eta_over_beta2_fourth':rr.record()})
 ratio*=rr
# Leading ordinary pad is a0/q. With q=(product connectors)(product beta2),
# all connector/pad factors cancel in eta_total / a0^4.
a0=F(1,10);gap=I(a0**4)*(ratio-1);assert gap.lo>0
result={'status':'PASS_EXACT_LAWFUL_SOURCE_HIDDEN_STATISTIC_CHECK','context_utc':'2026-10-02T06:20:00Z','inherited_source':'THREE-BIGON-CAP4-ORDINARY-REPLICA and independent REVIEW; no new replica claimed','input_certificate_sha256':hashlib.sha256(C.read_bytes()).hexdigest(),'scope':'Conditional on existing exact source-root existence in the certified box, all full forest laws through4 agree with E(1/10), while hidden graphon C4 is strictly different.','ordinary_target_pair_survival':str(a0),'ordinary_hidden_C4':str(a0**4),'cell_C4_formula':str(S.expand(etaC4(x,y,g))),'cells':cells,'normalized_C4_ratio':ratio.record(),'hidden_C4_gap':gap.record(),'observable_consequence':'No function of only the complete capped<=4 forest data, nonlinear or otherwise, universally recovers this C4 statistic over unknown positive serial lengths. Higher caps remain open.','not_claimed':['C4 is an authorized primitive observation','new biological source construction','all-prefix fixed-target replica','no finite adapter at any higher cap','unrestricted G4 completion','Lean verification'],'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-t}
(P/'lawful-cap4-C4-adapter-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2));print('orientation only gap',float(gap.lo),float(gap.hi))
