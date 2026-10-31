from fractions import Fraction as F
from math import prod
import json
rows=[]
for k in range(2,9):
 m=k+1;c=F(1,3)*F(3,4)**k*F(1,2)**(k+1)
 n=m
 while True:
  d=F(prod(range(n-m+1,n+1)),n**m)
  bound=(F(1,n)+1-d)/d
  if bound<c:break
  n*=2
 assert d>0 and bound<c
 rows.append(dict(k=k,m=m,n=n,parity=str(c),extension_bound=str(bound)))
print(json.dumps({'status':'PASS_EXACT_FINITE_EXTENSION_OBSTRUCTION','rows':rows},indent=2))
