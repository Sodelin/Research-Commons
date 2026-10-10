from fractions import Fraction as F
from math import prod, factorial, comb
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
lam=lambda n:n*(n-1)//2
@lru_cache(None)
def O(n,j,q):
 if not n:return F(j==0)
 if j<1 or j>n:return F(0)
 return prod(lam(k) for k in range(j+1,n+1))*sum((q**lam(k)/prod(lam(l)-lam(k) for l in range(j,n+1) if l!=k) for k in range(j,n+1)),F(0))
@lru_cache(None)
def eppf(s,q):
 if not s:return F(1)
 n=sum(s); k=len(s)
 return O(n,k,q)*F(factorial(k)*prod(factorial(x) for x in s),factorial(n)*comb(n-1,k-1))
@lru_cache(None)
def B(s,q,g):
 n=sum(s);v=F(0)
 for bits in product([0,1],repeat=len(s)):
  a=tuple(x for x,b in zip(s,bits) if b); b=tuple(x for x,z in zip(s,bits) if not z)
  v+=g**sum(a)*(1-g)**sum(b)*eppf(a,q)*eppf(b,q)
 return v

def stats(q,g):
 d=(3*B((2,2,1,1),q,g)-2*B((3,1,1,1),q,g))/9
 e=(2*B((3,2,1,1),q,g)-B((4,1,1,1),q,g))/6
 return d,e
found=[]
for q in [F(i,10) for i in range(1,10)]:
 for g in [F(i,100) for i in range(1,51)]:
  d,e=stats(q,g)
  if d*e<0:
   found.append({'q':str(q),'g':str(g),'d6':str(d),'e':str(e)})
   break
 if found:break
out={'kind':'EXACT_CAP_SEVEN_EQUAL_ARM_SIGN_TEST','found':found,'admitted_scope':'same positive arm duration t=-log(q), same strict IID inheritance g','no_later_cap_or_master_claim':True}
Path(__file__).with_name('RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
