"""Fixed rational fixture for the equal-arm extra-term sign premise."""
from fractions import Fraction as F
from math import prod,factorial,comb
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
lam=lambda n:n*(n-1)//2
@lru_cache(None)
def ordinary(n,j,q):
 if n==0:return F(j==0)
 if j<1 or j>n:return F(0)
 return prod(lam(k) for k in range(j+1,n+1))*sum((q**lam(k)/prod(lam(l)-lam(k) for l in range(j,n+1) if l!=k) for k in range(j,n+1)),F(0))
@lru_cache(None)
def eppf(s,q):
 if not s:return F(1)
 n=sum(s);k=len(s)
 return ordinary(n,k,q)*F(factorial(k)*prod(factorial(x) for x in s),factorial(n)*comb(n-1,k-1))
@lru_cache(None)
def cell(s,x,y,g):
 z=F(0)
 for a in product([0,1],repeat=len(s)):
  left=tuple(v for v,b in zip(s,a) if b);right=tuple(v for v,b in zip(s,a) if not b)
  z+=g**sum(left)*(1-g)**sum(right)*eppf(left,x)*eppf(right,y)
 return z

def stats(x,y,g):
 p22=cell((2,2,1,1),x,y,g);p3=cell((3,1,1,1),x,y,g)
 p32=cell((3,2,1,1),x,y,g);p4=cell((4,1,1,1),x,y,g)
 return (3*p22-2*p3)/9,(2*p32-p4)/6,[p22,p3,p32,p4]

def count(n,j,x,y,g):
 return sum((F(comb(n,k))*g**k*(1-g)**(n-k)*ordinary(k,a,x)*ordinary(n-k,j-a,y) for k in range(n+1) for a in range(j+1)),F(0))

def c(n,x,y,g):
 return count(n,n-2,x,y,g)+F(n*(n-1),4)*count(n-1,n-1,x,y,g)-F(n*(n-1)**2,4*(2*n-3))*count(n-2,n-2,x,y,g)-F(n*(n-1)*(n-2),4*(2*n-3))*count(n,n,x,y,g)
x=y=F(1,5);g=F(17,50)
d,e,rows=stats(x,y,g)
controls={
'exact_D6':d==F(5926106296,50067901611328125),
'exact_extra_e':e==F(-25054764879056,156462192535400390625),
'opposite_sign':d>0>e,
'signed_band_matches_count_primitive':c(6,x,y,g)==-comb(6,4)*d,
'ordinary_limit_g0':stats(x,y,F(0))[:2]==(0,0),
'ordinary_limit_g1':stats(x,y,F(1))[:2]==(0,0),
'zero_duration_identity':stats(F(1),F(1),g)[:2]==(0,0),
'arm_exchange':stats(x,y,g)==stats(y,x,1-g),
'count_rows_stochastic':all(sum(count(n,j,x,y,g) for j in range(n+1))==1 and all(count(n,j,x,y,g)>=0 for j in range(n+1)) for n in range(8)),
'original_eppf_entries_positive':all(v>0 for v in rows)}
assert all(controls.values())
result={'status':'EXACT_RATIONAL_FIXED_FIXTURE_PASS','source':{'left_pair_survival':str(x),'right_pair_survival':str(y),'inheritance_parent_0':str(g),'arm_duration':'log(5)','COMMON_kernel':'ordinary E_log(5)'},'D6_signed_per_label_band':str(d),'extra_e':str(e),'c6_count_primitive':str(c(6,x,y,g)),'original_partition_eppf':dict(zip(['p6_2211','p6_3111','p7_3211','p7_4111'],map(str,rows))),'controls':controls,'scope':'Rejects sign(D6)=sign(e) on actual equal-arm cells. No target matching, all-word sign, or G4 closure claim.'}
Path(__file__).with_name('FIXED-FIXTURE-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
