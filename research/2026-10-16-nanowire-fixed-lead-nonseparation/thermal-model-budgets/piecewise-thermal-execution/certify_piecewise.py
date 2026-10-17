"""Bounded direct interval thermal certificate; floating inverses only propose witnesses."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt,lcm,factorial
import numpy as np,json,hashlib,gzip,sys,time
if sys.flags.optimize:raise RuntimeError('Assertions required')
D=Path(__file__).resolve().parent;P=D.parent/'thermal-budget-execution';n=240;scale=2**48
hashes={'scaled_K_rows.json':'71c89f64f5b084daab8bb570ff61ad87705d4b150051a8d5196c56b8309d6d03','PRIOR-CONDUCTANCE-RESULT.json':'9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647'}
for name,h in hashes.items():assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
base=json.loads((P/'scaled_K_rows.json').read_text());den=base['denominator'];cs=list(range(4))+list(range(236,240));cset=set(cs)
kb=F(1380649,10**29)/F(1602176634,10**31);theta=kb/1000;limit=F(1,1000); eta=F(1,1000)
prior=json.loads((P/'PRIOR-CONDUCTANCE-RESULT.json').read_text()); f0=F(prior['values']['plus']['g_LL']['upper']);assert prior['electron_indices']==[0,2] and prior['hole_indices']==[1,3]
def rootup(a):q=isqrt(a);return q+(q*q<a)
def norm(a,d):return F(rootup(a),d)
records=[];attempts=0;t0=time.time()
def cell(lo,hi,depth):
 global attempts
 attempts+=1;c=(lo+hi)/2;h=(hi-lo)/2
 # beta center enclosure with width 2^-48
 v=(1-c*c/4)*scale*scale;bint=isqrt(v.numerator//v.denominator);bc=F(bint,scale);berr=F(1,scale)
 assert bc*bc<=1-c*c/4<=(bc+berr)**2 and bc>F(1,2)
 dd=lcm(den,c.denominator*2,scale);rows=[];K=np.zeros((n,n),complex)
 for i,old in enumerate(base['rows']):
  rr={j:[F(a,den),F(0)] for j,a,b in old}
  if i not in rr:rr[i]=[F(0),F(0)]
  rr[i][0]+=c*(F(1,2) if i in cset else 1);rr[i][1]=bc if i in cset else F(0)
  row=[]
  for j,(a,b) in rr.items():
   aa=a*dd;bb=b*dd;assert aa.denominator==bb.denominator==1
   row.append((j,int(aa),int(bb)));K[i,j]=complex(float(a),float(b))
  rows.append(row)
 Z=np.linalg.inv(K);zr=[[int(round(float(v.real)*scale)) for v in row] for row in Z];zi=[[int(round(float(v.imag)*scale)) for v in row] for row in Z]
 rsq=0
 for i,row in enumerate(rows):
  for j in range(n):
   a=-(dd*scale if i==j else 0);b=0
   for k,u,v in row:a+=u*zr[k][j]-v*zi[k][j];b+=u*zi[k][j]+v*zr[k][j]
   rsq+=a*a+b*b
 sq=lambda ii,jj:sum(zr[i][j]**2+zi[i][j]**2 for i in ii for j in jj)
 z=norm(sq(range(n),range(n)),scale); e=norm(rsq,dd*scale);lz=norm(sq(cs,range(n)),scale);rz=norm(sq(range(n),cs),scale);az=norm(sq(cs,cs),scale)
 delta=h+berr;q=e+delta*z;up=F(4);err=None;fz=None
 if q<1:
  ae=lz*(e+delta*rz)/(1-q)
  # |beta(x)-bc| <= limit*h/(4 beta_min)+berr, beta_min>=1/2.
  be=limit*h/2+berr;err=2*ae+2*be*az
  fz=F(2)
  for i in range(4):
   for j in (0,2):
    re=(1 if i==j else 0)+2*bc*F(zi[i][j],scale);im=-2*bc*F(zr[i][j],scale)
    fz+=(1 if i in (1,3) else -1)*(re*re+im*im)
  up=min(F(4),max(F(0),fz+4*err+2*err*err))
 # Deterministic bounded recursion: 16 initial cells, depth<=4, <=496 possible attempts.
 if up>F(1,10) and depth<4:
  del Z,zr,zi,K
  cell(lo,c,depth+1);cell(c,hi,depth+1);return
 # Outward rational quantization prevents denominator explosion when summing cell bounds.
 up=F((up.numerator*10**12+up.denominator-1)//up.denominator,10**12)
 rec={'lo':str(lo),'hi':str(hi),'depth':depth,'q':str(q),'upper':str(up),'center_beta':str(bc),'beta_error':str(berr),'z':str(z),'e':str(e),'lZ':str(lz),'rZ':str(rz),'aZ':str(az),'residual_squared':str(rsq),'K_denominator':str(dd),'error':str(err),'fZ':str(fz)}
 if q<1 and up<4:
  name=f'witness-{len(records):03d}.json.gz';raw=json.dumps({'scale':scale,'real':zr,'imag':zi},separators=(',',':')).encode();data=gzip.compress(raw,mtime=0);(D/name).write_bytes(data);rec['witness']=name;rec['witness_sha256']=hashlib.sha256(data).hexdigest()
 records.append(rec)
 if len(records)%16==0:print('leaves',len(records),'attempts',attempts,'seconds',round(time.time()-t0,1),flush=True)
for j in range(16):cell(-limit+2*limit*j/16,-limit+2*limit*(j+1)/16,0)
# Uniform Fermi kernel bound; no quadrature or numerical exponentials are accepted.
inside=sum((F(r['hi'])-F(r['lo']))*F(r['upper']) for r in records)/(4*theta)
v=limit/theta;exp_lower=sum(v**k/F(factorial(k)) for k in range(25));tail=min(F(1),2/(1+exp_lower));warm=min(F(4),inside+4*tail)
# |fT-f0| <= fT+f0 <= warm+f0, using nonnegative readouts.
thermal_error=warm+f0;Q=1-(warm+2*eta+thermal_error)
out={'status':'CERTIFIED' if Q>0 else 'INCONCLUSIVE','temperature_K':'1/1000','theta':str(theta),'eta':str(eta),'drift':'0','domain':str(limit),'attempts':attempts,'leaves':len(records),'inside_upper':str(inside),'tail_probability_upper':str(tail),'warm_upper':str(warm),'thermal_error_upper':str(thermal_error),'Q_lower':str(Q),'input_hashes':hashes,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'cells':records,'displays':{'inside':float(inside),'tail':float(tail),'warm':float(warm),'Q':float(Q)},'seconds':time.time()-t0}
(D/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'],out['displays'],out['attempts'],out['leaves'],flush=True)
