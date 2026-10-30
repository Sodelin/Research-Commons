from fractions import Fraction as F
from pathlib import Path
import json
checks=0
for N in range(1,21):
 u=[F(i+2,i+3) for i in range(N+1)];t=[F((i+1)**2) for i in range(N+1)];v=[a*b for a,b in zip(u,t)]
 for endpoint_zero in [False,True]:
  q=[F((i*5+N*3)%11-5) for i in range(N+1)]
  if endpoint_zero:q[-1]=-sum(q[:-1])
  p=[a/b for a,b in zip(q,u)];prefix=[];total=F(0)
  for x in q:total+=x;prefix.append(total)
  T=sum(p[i]*p[j]*u[i]*v[j] for i in range(N+1) for j in range(i+1,N+1))+sum(p[i]**2*u[i]*v[i] for i in range(N+1))/2
  rhs=t[N]*prefix[N]**2/2-sum((t[j+1]-t[j])*prefix[j]**2 for j in range(N))/2
  assert T==rhs
  if endpoint_zero and any(q):assert T<0
  checks+=1
out={'status':'PASS','exact_rational_controls':checks,'identity':'T=1/2*t_N*Q_N^2-1/2*sum_(j<N)(t_(j+1)-t_j)*Q_j^2','scope':'Finite controls of elementary Abel identity; universal proof retained in note; not full-word profile acquisition.'}
Path(__file__).with_name('abel-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
