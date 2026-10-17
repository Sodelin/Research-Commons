from pathlib import Path
from fractions import Fraction as F
from math import isqrt,lcm
import json,gzip,hashlib,sys
assert not sys.flags.optimize
P=Path(__file__).resolve().parent;d=json.load(open(P/'RESULT.json'));base=json.load(open(P.parent/'thermal-budget-execution/scaled_K_rows.json'));den=base['denominator'];n=240;cs=list(range(4))+list(range(236,240));scale=2**48
assert hashlib.sha256((P.parent/'thermal-budget-execution/scaled_K_rows.json').read_bytes()).hexdigest()==d['input_hashes']['scaled_K_rows.json']
def norm(v,den):
 r=isqrt(v);return F(r+(r*r<v),den)
last=-F(d['domain']);checked=0;fallback=0
for rec in sorted(d['cells'],key=lambda r:F(r['lo'])):
 lo,hi=F(rec['lo']),F(rec['hi']);assert lo==last and lo<hi;last=hi
 if 'witness' not in rec:
  assert F(rec['upper'])==4;fallback+=1;continue
 raw=(P/rec['witness']).read_bytes();assert hashlib.sha256(raw).hexdigest()==rec['witness_sha256'];Z=json.loads(gzip.decompress(raw));xr,xi=Z['real'],Z['imag'];assert Z['scale']==scale
 c=(lo+hi)/2;h=(hi-lo)/2;bc=F(rec['center_beta']);be=F(rec['beta_error']);assert bc*bc<=1-c*c/4<=(bc+be)**2
 dd=lcm(den,2*c.denominator,scale);rsq=0
 for i,row in enumerate(base['rows']):
  vals={j:[F(a,den),F(0)] for j,a,b in row};vals.setdefault(i,[F(0),F(0)]);vals[i][0]+=c*(F(1,2) if i in cs else 1);vals[i][1]=bc if i in cs else 0
  entries=[(j,int(a*dd),int(b*dd)) for j,(a,b) in vals.items()]
  for j in range(n):
   re=-dd*scale if i==j else 0;im=0
   for k,a,b in entries:re+=a*xr[k][j]-b*xi[k][j];im+=a*xi[k][j]+b*xr[k][j]
   rsq+=re*re+im*im
 assert rsq==int(rec['residual_squared']) and dd==int(rec['K_denominator'])
 def ns(ii,jj):return norm(sum(xr[i][j]**2+xi[i][j]**2 for i in ii for j in jj),scale)
 e=norm(rsq,dd*scale);z=ns(range(n),range(n));l=ns(cs,range(n));r=ns(range(n),cs);a=ns(cs,cs);q=e+(h+be)*z
 assert q==F(rec['q']) and q<1
 err=2*l*(e+(h+be)*r)/(1-q)+2*(F(d['domain'])*h/2+be)*a
 fz=F(2)
 for i in range(4):
  for j in (0,2):
   re=int(i==j)+2*bc*F(xi[i][j],scale);im=-2*bc*F(xr[i][j],scale)
   fz+=(1 if i in(1,3) else -1)*(re*re+im*im)
 assert fz==F(rec['fZ']) and err==F(rec['error'])
 bound=min(F(4),max(F(0),fz+4*err+2*err*err));assert F(rec['upper'])>=bound
 checked+=1
assert last==F(d['domain'])
print('PASS saved-cell replay:',checked,'validated witnesses;',fallback,'worst-case cells;',len(d['cells']),'contiguous cells')
