from fractions import Fraction as F
from math import comb
import json
V=[F(1,100),F(1,10),F(1,2),F(9,10),F(99,100)]
cases=0
for a in V:
 for b in V:
  for g in V:
   d=[sum(F(comb(n,j))*g**j*(1-g)**(n-j)*a**comb(j,2)*b**comb(n-j,2) for j in range(n+1)) for n in range(13)]
   assert all(d[n]**2>=d[n-1]*d[n+1] for n in range(1,12))
   assert d[10]*d[4]<d[8]*d[5]
   assert all(d[n+1]<d[n] for n in range(1,12))
   assert all(d[r-1]*d[r]>=d[r+1]*d[r-2] for r in range(4,12))
   cases+=1
print(json.dumps({'exact_rational_cases':cases,'max_arity':12,'status':'PASS','scope':'finite controls of classical source instantiation; not proof or G4 closure'},indent=2))
