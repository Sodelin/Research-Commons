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
inp=json.loads(Path('stage1-result.json').read_text());ls=inp['lambda'];cs=[F(a,int(inp['normal_sum'])) for a in inp['normal']]
p0=F('0.605990392211040');q0=F('0.510276570646996');rad=F(1,10**12)
p=I(p0-rad,p0+rad);q=I(q0-rad,q0+rad)
assert 0<p.a<p.b<1 and 0<q.a<q.b<1
G=[F(0),F(0)];J0=[[F(0),F(0)],[F(0),F(0)]];J=[[I(0),I(0)],[I(0),I(0)]];floor=F(1)
for c,l in zip(cs,ls):
 f0=1-p0+p0*q0**l;f=1-p+p*q**l;assert f.a>0;floor=min(floor,f.a)
 G[0]+=c*(1-q0**l)/f0;G[1]-=c*p0*l*q0**(l-1)/f0
 vals0=[(1-q0**l)**2/f0**2,-l*q0**(l-1)/f0**2,(-p0*l*(l-1)*q0**(l-2)/f0 if l>1 else F(0))+p0**2*l*l*q0**(2*l-2)/f0**2]
 vals=[(1-q**l)**2/f**2,-l*q**(l-1)/f**2,(-p*l*(l-1)*q**(l-2)/f if l>1 else I(0))+p**2*l*l*q**(2*l-2)/f**2]
 for ij,k in [((0,0),0),((0,1),1),((1,0),1),((1,1),2)]:J0[ij[0]][ij[1]]+=c*vals0[k];J[ij[0]][ij[1]]=J[ij[0]][ij[1]]+c*vals[k]
det=J0[0][0]*J0[1][1]-J0[0][1]*J0[1][0];assert det!=0
A=[[J0[1][1]/det,-J0[0][1]/det],[-J0[1][0]/det,J0[0][0]/det]]
E=[[I(int(i==j))-sum((A[i][k]*J[k][j] for k in range(2)),I(0)) for j in range(2)] for i in range(2)]
kappa=max(sum(E[i][j].mag() for j in range(2)) for i in range(2));eta=max(abs(sum(A[i][j]*G[j] for j in range(2))) for i in range(2))
margin=rad-eta-kappa*rad;assert kappa<1 and margin>0
hdet=J[0][0]*J[1][1]-J[0][1]*J[1][0]
classification='saddle' if hdet.b<0 else ('strict minimum' if hdet.a>0 and J[0][0].a>0 else ('strict maximum' if hdet.a>0 and J[0][0].b<0 else 'undetermined'))
out={'status':'PASS exact rational contraction certifies one unique strict critical point in box','new_execution':True,'residue':'1/2','python':sys.version,'normal':inp['normal'],'normal_sum':inp['normal_sum'],'center':[str(p0),str(q0)],'radius':str(rad),'box':[p.dump(),q.dump()],'positive_denominator_floor':str(floor),'gradient_at_center':[str(x) for x in G],'jacobian_at_center':[[str(x) for x in row] for row in J0],'jacobian_box':[[x.dump() for x in row] for row in J],'inverse_center_jacobian':[[str(x) for x in row] for row in A],'I_minus_AJ':[[x.dump() for x in row] for row in E],'kappa':str(kappa),'eta':str(eta),'self_map_margin':str(margin),'hessian_determinant_interval':hdet.dump(),'critical_classification':classification,'seconds':time.monotonic()-start}
Path('stage5-v2-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],flush=True);print('kappa<=',float(kappa),'eta<=',float(eta),'margin>=',float(margin),'Hessian classification',classification,flush=True);print('seconds',out['seconds'],flush=True)
