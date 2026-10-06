import resource
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
import json,time,sys,hashlib
from pathlib import Path
import mpmath as mp
start=time.monotonic();mp.mp.dps=60
inp=json.loads(Path('stage3-result.json').read_text());cs=[int(x) for x in inp['reduced_coefficients_descending']]
def ev(a,b):
 v=cs[0];bp=b
 for c in cs[1:]:v=v*a+c*bp;bp*=b
 return (v>0)-(v<0)
prev=(1,ev(1,1000));brackets=[]
for i in range(2,1000):
 z=ev(i,1000)
 if z*prev[1]<0:brackets.append([prev[0],i,1000])
 if z==0:brackets.append([i,i,1000])
 prev=(i,z)
print('Rational sign-change brackets',brackets,flush=True)
raw1=json.loads(Path('stage1-result.json').read_text());lams=raw1['lambda'];C=[mp.mpf(a)/mp.mpf(raw1['normal_sum']) for a in raw1['normal']]
def grad(p,q):
 fs=[1-p+p*q**l for l in lams]
 return (sum(c*(1-q**l)/f for c,l,f in zip(C,lams,fs)),sum(-c*p*l*q**(l-1)/f for c,l,f in zip(C,lams,fs)))
found=[];tried=0
for lo,hi,den in brackets:
 q0=mp.mpf(lo+hi)/(2*den)
 for p0 in ['0.01','0.1','0.3','0.5','0.7','0.9','0.99']:
  tried+=1
  try:
   p,q=mp.findroot(grad,(mp.mpf(p0),q0),tol=mp.mpf('1e-45'),maxsteps=60)
   residual=max(abs(x) for x in grad(p,q))
   if 0<p<1 and 0<q<1 and residual<mp.mpf('1e-35') and min(p,1-p,q,1-q)>mp.mpf('1e-8'):
    if not any(abs(p-mp.mpf(v['p']))+abs(q-mp.mpf(v['q']))<mp.mpf('1e-20') for v in found):
     row={'p':mp.nstr(p,60),'q':mp.nstr(q,60),'residual':mp.nstr(residual,8)};found.append(row);print('NUMERIC ONLY',row,flush=True)
  except Exception as e:pass
out={'status':'EXPLORATORY numerical candidates only; no strict critical existence certificate','new_execution':True,'input_sha256':hashlib.sha256(Path('stage3-result.json').read_bytes()).hexdigest(),'sign_change_brackets':brackets,'candidate_pairs':found,'tries':tried,'seconds':time.monotonic()-start,'python':sys.version,'mpmath':mp.__version__}
Path('stage4-result.json').write_text(json.dumps(out,indent=2)+'\n');print('done',out['seconds'],flush=True)
