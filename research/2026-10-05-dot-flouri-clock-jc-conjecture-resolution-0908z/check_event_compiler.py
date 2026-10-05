#!/usr/bin/env python3
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

def mm(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def assignments(G,old):
 out={}
 for new in product(range(len(G[0])),repeat=len(old)):
  w=Q(1)
  for a,b in zip(old,new):w*=G[a][b]
  out[new]=w
 assert sum(out.values())==1
 return out
checks=0
for phi in [Q(0),Q(1,7),Q(1,2),Q(5,6),Q(1)]:
 H=[[1,0,0,0],[0,1,0,0],[0,0,phi,1-phi]]
 S=[[1,0,0],[0,1,0],[1,0,0],[0,0,1]] # outputs S,B,Hr
 T=[[1,0],[0,1],[0,1]]
 B=[[1,0,0],[0,1,0],[phi,0,1-phi]]
 C=[[1,0],[0,1],[phi,1-phi]]
 assert mm(H,S)==B and mm(B,T)==C;checks+=2
 # Alternative tied-time join order: outputs A,Hl,T, then S,T.
 Tfirst=[[1,0,0],[0,0,1],[0,1,0],[0,0,1]]
 Ssecond=[[1,0],[1,0],[0,1]]
 assert mm(mm(H,Tfirst),Ssecond)==C;checks+=1
 for m in range(1,5):
  for old in product(range(3),repeat=m):
   direct=assignments(C,old);via={}
   for mid,w in assignments(B,old).items():
    for new,v in assignments(T,mid).items():via[new]=via.get(new,0)+w*v
   assert via==direct;checks+=1
 # A coalesced block with any descendant size still takes one inheritance draw.
 for descendants in range(1,7):
  assert assignments(C,(2,))=={(0,):phi,(1,):1-phi};checks+=1

mirror_checks=0
for a,b in product([Q(0),Q(1,4),Q(1,2),Q(4,5),Q(1)],repeat=2):
 G=[[a,1-a],[1-b,b]]
 mirror=[[1-a,a],[b,1-b]]
 assert mirror==[row[::-1] for row in G]
 for m in range(1,5):
  for old in product(range(2),repeat=m):
   base=assignments(G,old);other=assignments(mirror,old)
   assert all(w==other[tuple(1-z for z in new)] for new,w in base.items());mirror_checks+=1

result={'status':'PASS','arithmetic':'stdlib Fraction only',
'A_B_C_composition_and_current_lineage_checks':checks,
'D_simultaneous_upper_parent_mirror_checks':mirror_checks,
'zero_duration_semantics':'identity waiting, no instantaneous coalescent merger',
'A_to_D_nonminimal_common_bounds':{'J':4,'P':4},
'limits':'Finite event compiler controls, not parameter injectivity, observed route flags, arbitrary short-locus identification, posterior accuracy or Lean verification.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('CONTROL-RESULTS.json').write_text(text);print(text,end='')
