from fractions import Fraction as F
from itertools import product
from math import prod
import json
rows=[]
eps,delta,eta=F(1,3),F(1,4),F(1,2)
for k in range(1,5):
 states=list(product([-1,1],repeat=k));n=len(states)
 P=[[delta/n+(1-delta)*((1+eps*prod(s)*t[-1])/2 if s[1:]==t[:-1] else 0) for t in states] for s in states]
 assert all(sum(row)==1 for row in P)
 assert all(sum(P[i][j] for i in range(n))==1 for j in range(n))
 assert min(map(min,P))>=delta/n
 def prob(word):
  v=[F(1,n) for _ in states]
  for idx,y in enumerate(word):
   v=[v[i]*(1+eta*y*s[-1])/2 for i,s in enumerate(states)]
   if idx+1<len(word):v=[sum(v[i]*P[i][j] for i in range(n)) for j in range(n)]
  return sum(v)
 for ell in range(1,k+1):
  assert all(prob(w)==F(1,2**ell) for w in product([-1,1],repeat=ell))
 c=eps*(1-delta)**k*eta**(k+1)
 assert all(prob(w)==F(1,2**(k+1))*(1+c*prod(w)) for w in product([-1,1],repeat=k+1))
 rows.append({'k':k,'states':n,'prefix_match_through':k,'parity_coefficient':str(c),'minimum_transition':str(min(map(min,P))),'minimum_emission':str((1-eta)/2)})
print(json.dumps({'status':'PASS_EXACT_RATIONAL_EXTERNAL_MODEL_ONLY','epsilon':str(eps),'reset_delta':str(delta),'emission_eta':str(eta),'rows':rows},indent=2))
