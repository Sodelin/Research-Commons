import resource
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
from fractions import Fraction as F
import json,time,sys
from pathlib import Path
sys.set_int_max_str_digits(1000000)
start=time.monotonic()
class I:
 def __init__(self,a,b=None):self.a=F(a);self.b=F(a if b is None else b);assert self.a<=self.b
 def __add__(self,o):
  o=o if isinstance(o,I) else I(o);return I(self.a+o.a,self.b+o.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,o):return self+-o if isinstance(o,I) else self+I(-F(o))
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  o=o if isinstance(o,I) else I(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b];return I(min(v),max(v))
 __rmul__=__mul__
 def inv(self):assert self.a*self.b>0;return I(1/self.b,1/self.a)
 def __truediv__(self,o):return self*(o if isinstance(o,I) else I(o)).inv()
 def __pow__(self,n):
  assert n>=0
  ans=I(1)
  for _ in range(n):ans=ans*self
  return ans
 def mag(self):return max(abs(self.a),abs(self.b))
 def dump(self):return [str(self.a),str(self.b)]
inp=json.loads(Path('stage5-v2-result.json').read_text());p=I(*inp['box'][0]);q=I(*inp['box'][1]);r=F(1,2)
ls=[1,3,6,10,15,21];matrix=[]
for l in ls:
 f=1-p+p*q**l;assert f.a>0
 matrix.append([I(l),I(1-r**l),I(-l*r**(l-1)),(1-q**l)/f,-p*l*q**(l-1)/f])
def idet(mat):
 mat=[row[:] for row in mat];ans=I(1)
 for j in range(len(mat)):
  choices=[k for k in range(j,len(mat)) if mat[k][j].a*mat[k][j].b>0]
  if not choices:return None
  k=max(choices,key=lambda k:min(abs(mat[k][j].a),abs(mat[k][j].b)))
  if k!=j:mat[k],mat[j]=mat[j],mat[k];ans=-ans
  pivot=mat[j][j];ans=ans*pivot
  for k in range(j+1,len(mat)):
   ratio=mat[k][j]/pivot
   for l in range(j+1,len(mat)):mat[k][l]=mat[k][l]-ratio*mat[j][l]
 return ans
checks=[]
for omitted in range(6):
 rows=[i for i in range(6) if i!=omitted];det=idet([matrix[i] for i in rows])
 rec={'rows_zero_based':rows,'determinant_interval':None if det is None else det.dump()};checks.append(rec)
 if det is not None and det.a*det.b>0:
  print('PASS rank-five minor rows',rows,'det interval',float(det.a),float(det.b),flush=True)
  out={'status':'PASS rank-five tangent minor uniformly nonzero on certified critical box','new_execution':True,'input_box':inp['box'],'columns':['Lambda','D(r)','Dprime(r)','H_p','H_q'],'residue':'1/2','checks':checks,'seconds':time.monotonic()-start}
  Path('stage6-result.json').write_text(json.dumps(out,indent=2)+'\n');print('seconds',out['seconds'],flush=True);break
else:raise AssertionError('No minor certified; unknown rank')
