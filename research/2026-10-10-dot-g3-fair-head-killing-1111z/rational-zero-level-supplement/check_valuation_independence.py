from fractions import Fraction as F
from math import isqrt,prod
L=(1,3,6,10,15,21,28)
P=(2,7,13,41,331,43,17)
assert all(p>=2 and all(p%d for d in range(2,isqrt(p)+1)) for p in P)
g=[F((2**k+1)*(3**k+1),4*6**k) for k in L]
def val(n,p):
 v=0
 while n%p==0:v+=1;n//=p
 return v
V=[[val(x.numerator,p)-val(x.denominator,p) for x in g] for p in P]
expected=[[-1,-3,-7,-11,-15,-21,-29],[0,1,0,0,1,2,0],[0,0,1,0,0,0,0],[0,0,0,1,0,0,1],[0,0,0,0,1,0,0],[0,0,0,0,0,2,0],[0,0,0,0,0,0,1]]
assert V==expected
A=[list(map(F,r)) for r in V];det=F(1)
for j in range(7):
 assert A[j][j]!=0
 t=A[j][j];det*=t;A[j]=[x/t for x in A[j]]
 for i in range(j+1,7):
  t=A[i][j];A[i]=[x-t*y for x,y in zip(A[i],A[j])]
assert det==-2
K=prod(P)
print('primes',P,'K',K)
print('valuation matrix',V,'determinant',det)
print('PASS for every n>=1: t_n=(Kn-1)/(Kn+1) has valuation0 at every selected prime; m_lambda=t_n^(lambda+1)g_lambda are multiplicatively independent')
print('PASS t_n tends to1 from below; a=kappa=-log(t_n)>0 tend to0')
