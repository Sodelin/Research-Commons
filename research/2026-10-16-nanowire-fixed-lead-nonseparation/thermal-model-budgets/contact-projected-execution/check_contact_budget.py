"""Exact saved-witness contact norm certificate; no new inverse or floating acceptance."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import hashlib,json,sys
if sys.flags.optimize: raise RuntimeError('Assertions required')
HERE=Path(__file__).resolve().parent
P=HERE.parent/'thermal-budget-execution'
expected={'inverse_gaussian_integer.json':'3a3e46c5d43f89edddf13895a8d203409b89f2c3a4f3cd8ff5d55e01390975fd','scaled_K_rows.json':'71c89f64f5b084daab8bb570ff61ad87705d4b150051a8d5196c56b8309d6d03','RESULT.json':'21c3fb460b49d07fdbfb0e1ead390ddc89a93ea5c301b903a180cf72005ca14b','PRIOR-CONDUCTANCE-RESULT.json':'9e1eb9198562c8696d005819c6ffb8aa40d236c5afa4d3ff80d8ce3b96906647'}
for name,h in expected.items(): assert hashlib.sha256((P/name).read_bytes()).hexdigest()==h
Z=json.loads((P/'inverse_gaussian_integer.json').read_text()); R=json.loads((P/'RESULT.json').read_text()); K=json.loads((P/'scaled_K_rows.json').read_text())
x,y=Z['real'],Z['imag']; s=Z['denominator'];n=240;contacts=list(range(4))+list(range(236,240));cs=set(contacts)
assert s==2**48 and len(x)==len(y)==n and all(len(a)==n for a in x+y)
# Independently replay residual from saved sparse K; source reconstruction already reviewed separately.
d=K['denominator'];res=0
for i,row in enumerate(K['rows']):
 for j in range(n):
  re=-(d*s if i==j else 0);im=0
  for h,a,b in row: re+=a*x[h][j]-b*y[h][j];im+=a*y[h][j]+b*x[h][j]
  res+=re*re+im*im
assert res==int(R['residual_squared_integer'])
def ceilroot(a):
 q=isqrt(a);return q+(q*q<a)
def normsum(rows,cols):return sum(x[i][j]**2+y[i][j]**2 for i in rows for j in cols)
def upnorm(squared,den):
 c=ceilroot(squared);assert c*c>=squared and (c==0 or (c-1)**2<squared);return F(c,den)
zsq=normsum(range(n),range(n)); assert zsq==int(R['inverse_squared_integer'])
e=upnorm(res,d*s); z=upnorm(zsq,s);assert e<1
M=z/(1-e);eps=e*M;rho=1/M;assert rho==F(R['rho_lower'])
lsq=normsum(contacts,range(n));rsq=normsum(range(n),contacts);asq=normsum(contacts,contacts)
# K0'=I-Pi/2. Integer numerator weights 1 at contacts, 2 in interior; denominator 2s^2.
br=[];bi=[]
for i in contacts:
 rr=[];ii=[]
 for j in contacts:
  re=im=0
  for h in range(n):
   w=1 if h in cs else 2
   re+=w*(x[i][h]*x[h][j]-y[i][h]*y[h][j])
   im+=w*(x[i][h]*y[h][j]+y[i][h]*x[h][j])
  rr.append(re);ii.append(im)
 br.append(rr);bi.append(ii)
bsq=sum(t*t for mat in (br,bi) for row in mat for t in row)
lz=upnorm(lsq,s);rz=upnorm(rsq,s);az=upnorm(asq,s);bz=upnorm(bsq,2*s*s)
l=lz+eps;r=rz+eps;a0=az+eps;b0=bz+eps*(lz+rz)+eps**2
prior=json.loads((P/'PRIOR-CONDUCTANCE-RESULT.json').read_text());f0=F(prior['values']['plus']['g_LL']['upper']);assert 0<f0<F(1,250)
eta=F(1,1000);kb=F(1380649,10**29)/F(1602176634,10**31);oldT=F(R['temperature_K'])
# Four predetermined windows, one sufficient analytic theta rule. No optimization/search beyond these four.
results=[]
for div in (2,4,8,16):
 W=rho/div;q=M*W;assert 0<W<min(rho,F(1)) and q<1
 # beta_W>=1-W^2/4, a rational lower bound from sqrt(t)>=t for 0<=t<=1.
 beta=1-W*W/4;assert beta>0
 a=min(a0+l*r*W/(1-q),1/beta)
 b=b0+l*r*((1-q)**-2-1+W/(4*beta*(1-q)**2))
 D=W*a/(2*beta)+2*b;L=4*D # N=2
 theta=min(W/100,1/(1000*L)); pu=2*theta/W # exp(v)>=v implies p<=pu
 assert 0<pu<1 and theta>0
 # m1<=2theta log2<=2theta; physical 0<=f<=4; drift=0.
 warm=f0+2*L*theta+4*pu
 Q=1-(warm+2*eta+2*L*theta)/(1-pu)
 assert Q>0
 T=theta/kb
 vals={'window_divisor':div,'W':W,'q':q,'beta_lower':beta,'a':a,'b':b,'L':L,'theta':theta,'p_upper':pu,'warm_upper':warm,'Q_lower':Q,'temperature_K':T,'improvement_factor':T/oldT}
 results.append({k:str(v) if isinstance(v,F) else v for k,v in vals.items()}|{'decimal_displays':{k:float(v) for k,v in vals.items() if isinstance(v,F)}})
summary={'status':'PASS','scope':'same positive saved 60-site model B=2 meV, eta=.001, drift0; four predetermined windows; no new inverse','input_sha256':expected,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'squared_integer_norms':{'lZ':str(lsq),'rZ':str(rsq),'aZ':str(asq),'bZ':str(bsq)},'bZ_denominator':str(2*s*s),'central_bounds':{k:str(v) for k,v in {'e':e,'z':z,'M':M,'epsilon':eps,'lZ':lz,'rZ':rz,'aZ':az,'bZ':bz,'l':l,'r':r,'a0':a0,'b0':b0,'f0_upper':f0}.items()},'central_decimal_displays':{k:float(v) for k,v in {'lZ':lz,'rZ':rz,'aZ':az,'bZ':bz,'epsilon':eps}.items()},'results':results}
(HERE/'RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: hashes, exact full saved residual, contact norm sums/outward roots, four rational thermal certificates')
print(summary['central_decimal_displays'])
for row in results:print(row['window_divisor'],{k:row['decimal_displays'][k] for k in ('L','temperature_K','Q_lower','improvement_factor')})
