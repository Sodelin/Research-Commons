from math import exp,log,log1p,lgamma,sqrt,ceil
from pathlib import Path
import json,time,hashlib
P=Path(__file__).parent
assert not (P/'RESULT.json').exists()
def lc(x):
 x=abs(x);return x+log1p(exp(-2*x))-log(2)
def lse(xs):
 m=max(xs);return m+log(sum(exp(x-m) for x in xs))
rows=[];start=time.monotonic()
for n in [100,300,1000,3000,10000]:
 M=ceil(log(n))+24
 probs=[lgamma(n+1)-lgamma(k+1)-lgamma(n-k+1)-n*log(2) for k in range(n+1)]
 residuals=[]
 for i in range(1,M+1):
  t=exp(-i);h=sqrt(2*i*t)
  residuals.append(-lse([probs[k]-t*(k-n/2)**2+lc(h*(k-n/2)) for k in range(n+1)]))
 # |rho| <= n(b+t/4), b<=h^2/8=i*exp(-i)/4.
 r=exp(-1);tail=n/4*r**(M+1)*((M+2)/(1-r)+r/(1-r)**2)
 rows.append({'n':n,'cells':M,'sum_rho_float':sum(residuals),'rho_over_log_n':sum(residuals)/log(n),'negative_part_over_log_n':sum(max(0,-x) for x in residuals)/log(n),'positive_part_over_log_n':sum(max(0,x) for x in residuals)/log(n),'analytical_omitted_tail_bound':tail,'floating_roundoff_certified':False})
result={'status':'EXPLORATORY_FLOAT_SCREEN_ONLY','source':'t_i=exp(-i); h_i=sqrt(2*i*exp(-i)); g_i=exp(h_i)/(1+exp(h_i)); rho_n=-log E_fair[exp(-t_i S^2)cosh(h_i S)]','claim_boundary':'No exact target equality, no fixed-target rival, no asymptotic theorem and no interval-certified signs. Tests possible cancellation, not a certificate.','rows':rows,'elapsed_seconds':time.monotonic()-start,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(P/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
