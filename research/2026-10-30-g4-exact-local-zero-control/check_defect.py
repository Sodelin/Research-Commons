from fractions import Fraction as F
from math import comb
import json
L=lambda n:n*(n-1)//2
def zero(n,a):return a**L(n)
def one(n,a):
 return (a**L(n-1)-a**L(n))/F(L(n)-L(n-1))
def two(n,a):
 ls=[L(n),L(n-1),L(n-2)]
 return sum(a**x/F(__import__('functools').reduce(lambda u,v:u*v,[y-x for y in ls if y!=x],1)) for x in ls)
def diag(r,a,b,g):
 return sum(F(comb(r,k))*g**k*(1-g)**(r-k)*zero(k,a)*zero(r-k,b) for k in range(r+1))
def defect(r,a,b,g):
 q=1-g
 tri=sum(F(comb(r-3,k))*g**k*q**(r-3-k)*(g**3*3*two(k+3,a)*zero(r-3-k,b)+q**3*3*two(r-k,b)*zero(k,a)) for k in range(r-2))
 pair=sum(F(comb(r-4,k))*g**k*q**(r-4-k)*(g**4*2*two(k+4,a)*zero(r-4-k,b)+q**4*2*two(r-k,b)*zero(k,a)+2*g*g*q*q*one(k+2,a)*one(r-2-k,b)) for k in range(r-3))
 return F(r-3,r-1)*comb(r,3)*tri-F(2,r-1)*3*comb(r,4)*pair
if __name__=='__main__':
 vals=[F(1,10),F(1,2),F(9,10)]
 results=[]
 for a in vals:
  for b in vals:
   for g in vals:
    ds=[defect(r,a,b,g) for r in range(4,7)]
    rho=[ds[r-4]/diag(r,a,b,g) for r in range(4,7)]
    results.append(dict(a=str(a),b=str(b),g=str(g),dev=list(map(str,ds)),rho=list(map(str,rho)),delta=list(map(str,[rho[i+1]-rho[i] for i in range(2)]))))
 print(json.dumps(results,indent=2))
