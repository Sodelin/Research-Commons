"""Independent finite transcription checks, not the uniform proof."""
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
import json,hashlib
def multiply(a,b,K):
 c=[Q() for _ in range(K+1)]
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   if i+j<=K:c[i+j]+=x*y
 return c
def log_by_powers(a,K):
 assert a[0]==1
 u=a[:];u[0]=Q();out=[Q()]*(K+1);p=[Q(1)]+[Q()]*K
 for j in range(1,K+1):
  p=multiply(p,u,K)
  out=[x+Q((-1)**(j+1),j)*y for x,y in zip(out,p)]
 return out
def direct(n,r,z,K):
 out=[Q()]*(K+1)
 for j in range(n+1):
  initial=[Q()]*j+[Q(comb(n,j))*r**comb(j,2)]
  bern=[Q(comb(n-j,h)*(-1)**h) for h in range(n-j+1)]
  exp=[(-z*comb(n-j,2))**h/factorial(h) for h in range(K+1)]
  term=multiply(multiply(initial,bern,K),exp,K)
  out=[x+y for x,y in zip(out,term)]
 return log_by_powers(out,K)
def pcoef(k,r,z):
 out=[Q()]*(k+1)
 for j in range(k+1):
  for h in range(k-j+1):
   out[j+h]+=r**comb(j,2)*Q(1,factorial(j))*(j*z)**h/factorial(h)
 return log_by_powers(out,k)[k]
cases=[]
for k in range(3,8):
 for r,z in ((Q(2,7),Q(3,5)),(Q(5,8),Q(7,3))):
  m=k+1
  c={n:(Q((-1)**(k-n)*comb(k,n)) if n<=k else Q())+2*Q((-1)**(k+1-n)*comb(k+1,n)) for n in range(2,m+1)}
  moments={j:sum(c[n]*comb(n,j) for n in c if n>=j) for j in range(2,m+1)}
  assert all(moments[j]==0 for j in range(2,k)) and moments[k]!=0
  paired=[Q()]*(k+1)
  for n,v in c.items():paired=[a+v*b for a,b in zip(paired,direct(n,r,z,k))]
  expected=factorial(k)*moments[k]*pcoef(k,r,z)
  assert all(a==0 for a in paired[:k]) and paired[k]==expected
  cases.append({'k':k,'m':m,'r':str(r),'z':str(z),'leading':str(expected)})
assert sum((Q((-1)**(j-1))*Q(j)**(3-j-1)*Q(1)**(3-j)/factorial(3-j) for j in range(1,4)),Q())==Q(-1,6)
assert sum((Q((-1)**(j-1))*Q(j)**(4-j-1)*Q(3)**(4-j)/factorial(4-j) for j in range(1,5)),Q())==Q(-7,4)
assert Q(1)-2+Q(3,4)+Q(1,40)==Q(-9,40)
out={'status':'PASS','method':'direct routing via coefficient convolution; finite logarithm powers; mixed triangular binomial moments',
'controls':cases,'small_k_signs_and_uniform_numeric_bound':True,
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'scope':'finite transcription support only; the uniform rare-arm and additive-semigroup arguments were reviewed by hand'}
Path(__file__).with_name('INDEPENDENT-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','mixed_moment_cases':len(cases),'checker_sha256':out['checker_sha256']}))

