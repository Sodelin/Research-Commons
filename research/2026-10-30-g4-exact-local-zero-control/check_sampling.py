from fractions import Fraction as F
from math import comb,factorial
from itertools import product
import json
from check_defect import diag,defect,L

def integral(n,k,a):
 rates=[L(n-j) for j in range(k+1)]
 assert len(set(rates))==len(rates)
 return sum(a**v/F(__import__('functools').reduce(lambda x,y:x*y,[w-v for w in rates if w!=v],1)) for v in rates)
def arm(n,blocks,a):
 k=sum(s-1 for s in blocks)
 return F(factorial(k)*__import__('functools').reduce(lambda x,y:x*y,map(factorial,blocks),1),2**k)*integral(n,k,a)
def particular(n,blocks,a,b,g):
 singles=n-sum(blocks)
 if singles<0:return F(0)
 ans=F(0)
 for routing in product([0,1],repeat=len(blocks)):
  left=[s for s,z in zip(blocks,routing) if z==0];right=[s for s,z in zip(blocks,routing) if z==1]
  for k in range(singles+1):
   nl=sum(left)+k;nr=n-nl
   ans+=comb(singles,k)*g**nl*(1-g)**nr*arm(nl,left,a)*arm(nr,right,b)
 return ans
def mass(n,blocks,a,b,g):
 if sum(blocks)>n:return F(0)
 denom=factorial(n-sum(blocks))
 for s in blocks:denom*=factorial(s)
 for s in set(blocks):denom*=factorial(blocks.count(s))
 return F(factorial(n),denom)*particular(n,blocks,a,b,g)
def test():
 out=[];checked=0
 for a,b,g in product([F(1,10),F(1,2),F(9,10)],repeat=3):
  for r in range(4,7):
   get=lambda n,bs:mass(n,bs,a,b,g)
   t,d=get(r,[3]),get(r,[2,2]);tn,dn=get(r+1,[3]),get(r+1,[2,2])
   p4,p32,p222=[get(r+1,bs) for bs in [[4],[3,2],[2,2,2]]]
   assert t==F(r-2,r+1)*tn+F(4,r+1)*p4+F(2,r+1)*p32
   assert d==F(r-3,r+1)*dn+F(3,r+1)*p32+F(6,r+1)*p222
   dev=F(r-3,r-1)*t-F(2,r-1)*d
   devn=F(r-2,r)*tn-F(2,r)*dn
   assert dev==defect(r,a,b,g)
   c=F(r*(r-3),(r-1)*(r+1));R=(4*(r-3)*p4+(2*r-12)*p32-12*p222)/((r-1)*(r+1))
   assert dev==c*devn+R
   q=diag(r+1,a,b,g)/diag(r,a,b,g)
   rho=dev/diag(r,a,b,g);rhon=devn/diag(r+1,a,b,g)
   assert rhon-rho==(1/(c*q)-1)*rho-R/(c*diag(r+1,a,b,g))
   checked+=1
   if a==b==F(1,2) and g in [F(1,2),F(1,10)] and r==4:
    out.append(dict(a=str(a),b=str(b),g=str(g),r=r,dev=str(dev),dev_next=str(devn),R=str(R),P4=str(p4),P32=str(p32),P222=str(p222),rho_delta=str(rhon-rho)))
 return dict(status='PASS',actual_cell_checks=checked,examples=out,scope='Rational controls, not universal proof or ordinary-return witnesses')
if __name__=='__main__':print(json.dumps(test(),indent=2))
