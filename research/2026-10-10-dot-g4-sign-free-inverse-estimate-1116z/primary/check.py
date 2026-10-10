from fractions import Fraction as F
from math import comb,prod
from pathlib import Path
import json,hashlib,time
N=12
lam=lambda n:n*(n-1)//2

def ordinary(q):
 E=[[F(0) for j in range(N+1)] for n in range(N+1)]
 E[0][0]=F(1)
 for n in range(1,N+1):
  for j in range(1,n+1):
   E[n][j]=prod(F(lam(l)) for l in range(j+1,n+1))*sum((q**lam(k)/prod(F(lam(l)-lam(k)) for l in range(j,n+1) if l!=k) for k in range(j,n+1)),F(0))
  assert sum(E[n])==1 and all(x>=0 for x in E[n])
 return E

def bigon(q,g):
 E=ordinary(q);B=[[F(0) for j in range(N+1)] for n in range(N+1)]
 for n in range(N+1):
  for k in range(n+1):
   w=comb(n,k)*g**k*(1-g)**(n-k)
   for a in range(k+1):
    for b in range(n-k+1):B[n][a+b]+=w*E[k][a]*E[n-k][b]
  assert sum(B[n])==1 and all(x>=0 for x in B[n])
 return B

def inverse(A):
 I=[[F(0) for j in range(N+1)] for n in range(N+1)]
 for n in range(N+1):
  I[n][n]=1/A[n][n]
  for j in range(n-1,-1,-1):I[n][j]=-sum((A[n][k]*I[k][j] for k in range(j,n)),F(0))/A[n][n]
 for n in range(N+1):
  for j in range(n+1):assert sum((A[n][k]*I[k][j] for k in range(j,n+1)),F(0))==int(n==j)
 return I

start=time.monotonic();fixtures=[]
for q,g in [(F(1,2),F(1,2)),(F(1,2),F(1,3)),(F(3,4),F(1,20)),(F(1,10),F(1,2)),(F(9,10),F(1,3))]:
 B=bigon(q,g);I=inverse(B)
 bad=[{'n':n,'j':j,'entry':str(I[n][j]),'expected_sign':(-1)**(n-j)} for n in range(1,N+1) for j in range(1,n+1) if (-1)**(n-j)*I[n][j]<0]
 fixtures.append({'q':str(q),'g':str(g),'N':N,'checkerboard_violations':bad,'inverse_row_l1':[str(sum(map(abs,row))) for row in I], 'exact_source_stochastic_and_inverse_checks':True})
 E=ordinary(q);Ei=inverse(E);assert all((-1)**(n-j)*Ei[n][j]>=0 for n in range(1,N+1) for j in range(1,n+1))
result={'scope':'Exploratory exact finite count-kernel inverse diagnostic; no full-forest theorem or heat-scale bound','elapsed_seconds':time.monotonic()-start,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'fixtures':fixtures,'ordinary_checkerboard_controls':'PASS all same-q fixtures through N=12'}
p=Path(__file__).parent/'RESULT.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'elapsed_seconds':result['elapsed_seconds'],'script_sha256':result['script_sha256'],'fixtures':[{'q':x['q'],'g':x['g'],'violations':len(x['checkerboard_violations']),'first':x['checkerboard_violations'][:1]} for x in fixtures]},indent=2))
