#!/usr/bin/env python3
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import json
G=[[Q(3,10),Q(1,10),Q(7,20),Q(1,4)],[Q(1,10),Q(3,10),Q(1,4),Q(7,20)]]
H=[[G[1][0],G[1][1],G[0][2],G[0][3]],[G[0][0],G[0][1],G[1][2],G[1][3]]]
r=[1,2,3,4]
assert all(sum(row)==1 and min(row)>0 for row in G+H)
assert G!=H and G[::-1]!=H
checks=0
# An arbitrary symmetric old-state functional depends on exchange orbits.
# Equality per orbit proves all such linear functionals in these finite controls.
for m in range(2,11):
 for z in product(range(2),repeat=m):
  zz=tuple(1-x for x in z)
  for a in range(4):
   x=Q(1);xx=Q(1);y=Q(1);yy=Q(1)
   for i,j in zip(z,zz):x*=G[i][a];xx*=G[j][a];y*=H[i][a];yy*=H[j][a]
   assert x+xx==y+yy;checks+=1

def K(A):return [[sum(A[i][a]*A[j][a]*r[a] for a in range(4)) for j in range(2)] for i in range(2)]
def coefficient(A):
 M=K(A);ans=Q(0)
 for z in product(range(2),repeat=4):
  n=z.count(0);w=Q(1,16)*Q(2)**(-comb(n,2)-comb(4-n,2))
  ans+=w*M[z[0]][z[1]]*M[z[2]][z[3]]
 return ans
x,y=coefficient(G),coefficient(H)
assert x==Q(7113377,81920000) and y==Q(7124897,81920000)
assert x-y==Q(-9,64000) and (x-y)/64==Q(-9,4096000)
result={'status':'PASS','arithmetic':'stdlib Fraction only','symmetric_orbit_column_checks':checks,
'conditional_four_label_coefficient_G':str(x),'conditional_four_label_coefficient_H':str(y),
'unconditional_difference_delta_squared':str((x-y)/64),
'limits':'Controls support the source-valid observation-family obstruction. Full-law equality is disproved; no global expansion identification or minimal sampling claim.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('LATER-FOREST-CONTROL-RESULTS.json').write_text(text);print(text,end='')
