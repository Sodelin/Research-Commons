from fractions import Fraction as F
from math import comb
import json
L=lambda n:n*(n-1)//2
g=F(2,3);a=b=F(1,2)
def cell(n):return sum(comb(n,j)*g**j*(1-g)**(n-j)*a**L(j)*b**L(n-j) for j in range(n+1))
def target(n):return F(3,4)**L(n)*cell(n)*F(1,2)**L(n)
assert target(2)==F(13,48)
assert target(3)==F(81,4096)
assert target(3)-target(2)**3==-F(5,55296)
print(json.dumps(dict(status='PASS',target='E(3/4)B(1/2,1/2,2/3)E(1/2), survivals',b2=str(target(2)),b3=str(target(3)),b3_minus_b2_cubed=str(target(3)-target(2)**3),scope='Actual routing-polynomial rational check, not a controllability theorem'),indent=2))
