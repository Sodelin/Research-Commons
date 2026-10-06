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
for l in ls[1:]:
 f=1-p+p*q**l
 matrix.append([I(l),I(1-r**l),I(-l*r**(l-1)),(1-q**l)/f,-p*l*q**(l-1)/f,I(1-r**(2*l))])
for j in range(5):
 choices=[k for k in range(j,5) if matrix[k][j].a*matrix[k][j].b>0];assert choices
 k=max(choices,key=lambda k:min(abs(matrix[k][j].a),abs(matrix[k][j].b)))
 if k!=j:matrix[k],matrix[j]=matrix[j],matrix[k]
 pivot=matrix[j][j]
 for k in range(j+1,5):
  ratio=matrix[k][j]/pivot
  for l in range(j+1,6):matrix[k][l]=matrix[k][l]-ratio*matrix[j][l]
t=[I(0) for _ in range(5)]
for j in reversed(range(5)):t[j]=(matrix[j][5]-sum((matrix[j][k]*t[k] for k in range(j+1,5)),I(0)))/matrix[j][j]
H=[[I(*v) for v in row] for row in inp['jacobian_box']]
B=(t[3]*H[0][0]*t[3]+t[3]*H[0][1]*t[4]+t[4]*H[1][0]*t[3]+t[4]*H[1][1]*t[4])/8
assert B.a>0
out={'status':'PASS exact positive one-retained-factor local-defect coefficient B','new_execution':True,'residue':'1/2','critical_box':inp['box'],'t_intervals':[v.dump() for v in t],'B_interval':B.dump(),'seconds':time.monotonic()-start}
Path('stage7-result.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],float(B.a),float(B.b),'seconds',out['seconds'],flush=True)
