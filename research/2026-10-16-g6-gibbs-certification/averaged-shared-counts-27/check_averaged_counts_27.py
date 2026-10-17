from fractions import Fraction as F
from math import comb
from itertools import product

def law(bits,p):
    q=F(1)
    for bit in bits:q*=p if bit else 1-p
    return q
n=0
for a in range(5):
 for b in range(5):
  r=a+b; h=F(1,2); ell=F(1,10); delta=F(1,40); v=h*(1-h); z=ell-h
  exact=F(0); l2=F(0)
  for bits in product((0,1),repeat=r):
   heavy=law(bits,h); light=law(bits,ell)
   altlight=(law(bits[:a],ell+delta)*law(bits[a:],ell-delta)+law(bits[:a],ell-delta)*law(bits[a:],ell+delta))/2
   null=(heavy+light)/2; alt=(heavy+altlight)/2
   exact+=(alt-null)**2/null
   l2+=(altlight-light)**2/heavy
  assert exact<=l2/2
  x=(abs(z)+delta)**2/v
  total=sum(F(comb(r,j)*j*j*(j-1)*(j-1))*x**(j-2) for j in range(2,r+1))
  def fall(q):
   if r<q:return 0
   ans=1
   for i in range(q):ans*=r-i
   return ans
  closed=sum(F(c*fall(q))*x**(q-2)*(1+x)**(r-q) for q,c in ((4,1),(3,4),(2,2)) if r>=q)
  assert total==closed
  assert l2<=delta**4/(4*v*v)*total
  n+=1
print(f'PASS: {n} exact rational allocation cases; mixture chi-square domination, orthogonal Taylor bound and falling-factorial sum identity. Finite algebra checks only; no asymptotic or physical theorem verification.')
