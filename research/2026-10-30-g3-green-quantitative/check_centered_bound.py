from fractions import Fraction as F
from pathlib import Path
import json
cases=[]
for rho,sigma in [(F(1,9),F(4,9)),(F(1,4),F(1,2)),(F(3,5),F(4,5))]:
 for N in range(2,13):
  w=[(sigma/rho-1)*(sigma/rho)**i for i in range(N)]
  a=[(1/rho-1)*rho**(-i) for i in range(N)]
  mu=sum(a)/sum(w);V=sum(x*x/y for x,y in zip(a,w))-sum(a)**2/sum(w)
  assert V>0
  # Choose the equality-achieving prefix on the two-moment affine space, with P(1)=1.
  Q=[-(a[i]/w[i]-mu)/V for i in range(N)]+[F(0)]
  q=[Q[i]-(Q[i-1] if i else 0) for i in range(N+1)];p=[q[i]*rho**(-i) for i in range(N+1)]
  assert sum(p)==1 and all(sum(v*z**i for i,v in enumerate(p))==0 for z in [rho,sigma])
  T=sum(p[i]*p[j]*rho**i*sigma**j for i in range(N+1) for j in range(i+1,N+1))+sum(v*v*(rho*sigma)**i for i,v in enumerate(p))/2
  assert -T==1/(2*V)
  closed=(1-rho)**2/(rho*(sigma-rho))*sum((rho*sigma)**(-i) for i in range(N))-(rho**(-N)-1)**2/((sigma/rho)**N-1)
  assert V==closed
  cases.append({'rho':str(rho),'sigma':str(sigma),'N':N,'V':str(V),'sharp_energy':str(-T)})
# Conservative uniform source constant bookkeeping.
assert F(12,4*3600**2)*64==F(1,67500)
out={'status':'PASS','sharp_two_moment_rational_cases':len(cases),'uniform_constant_bookkeeping':'1/67500','scope':'Exact algebra/equality controls, not nonlinear remainder or physical norm certificate','cases':cases}
Path(__file__).with_name('centered-bound-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
