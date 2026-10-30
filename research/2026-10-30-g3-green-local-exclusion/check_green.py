from fractions import Fraction as F
from pathlib import Path
import json
cases=[]
for r,w in [(F(2),F(2,9)),(F(3,2),F(1,5)),(F(5,4),F(1,3))]:
 rho,sigma=w/r,w*r;sh=(r-1/r)/2;ch=(r+1/r)/2
 for degree in range(2,13):
  H=[F(((i*7+degree*3)%13)-6) for i in range(degree-1)]
  if not any(H):H[0]=1
  p=[F(0)]*(degree+1)
  for i,h in enumerate(H):p[i]+=h*rho*sigma;p[i+1]-=h*(rho+sigma);p[i+2]+=h
  N=len(p)-1
  assert all(sum(v*z**i for i,v in enumerate(p))==0 for z in [rho,sigma])
  q=[w**i*v for i,v in enumerate(p)]
  def f(i):return sum(((r**abs(i-j)-r**(-abs(i-j)))/2)*v for j,v in enumerate(q))
  assert all(f(i)==0 for i in [-2,-1,0,N,N+1,N+2])
  assert all(f(i-1)-2*ch*f(i)+f(i+1)==2*sh*q[i] for i in range(N+1))
  T=sum(p[i]*p[j]*rho**i*sigma**j for i in range(N+1) for j in range(i+1,N+1))+sum(v*v*(rho*sigma)**i for i,v in enumerate(p))/2
  energy=sum((f(i+1)-f(i))**2 for i in range(-1,N+1))+2*(ch-1)*sum(f(i)**2 for i in range(N+1))
  assert T==-energy/(4*sh) and T<0
  cases.append({'exp_c':str(r),'weight':str(w),'degree':degree,'ordered_quadratic':str(T),'energy':str(energy)})
out={'status':'PASS','case_count':len(cases),'scope':'Exact rational controls for derived all-finite-vector Green identity; finite checks not the universal proof','cases':cases}
Path(__file__).with_name('green-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
