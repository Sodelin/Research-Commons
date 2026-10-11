"""Own exact coefficient audit of the raw-target restriction identities.
No external implementation is imported or executed. Coordinates, retained
aggregate values and own/cross outputs are independent formal variables.
"""
from fractions import Fraction as Q
from itertools import product
from hashlib import sha256
from pathlib import Path
P=Path(__file__).parent
# Retained variables: coordinate x[0:8], arbitrary g[8:16], arbitrary
# own output u[16:128], arbitrary cross contribution a[128:240], targets y.
def add(row,j,q):
 row[j]=row.get(j,Q(0))+q
 if not row[j]:del row[j]
def lin(*terms):
 d={}
 for j,q in terms:add(d,j,Q(q))
 return d
blocks=sorted({tuple(x for x in range(8) if (x&a).bit_count()%2==b) for a in range(1,8) for b in range(2)})
roots=[]
for c in blocks:
 for signs in product((-1,1),repeat=3):
  r=[0]*8
  for i,s in zip(c,(1,)+signs):r[i]=s
  roots.append(r)
assert len(roots)==112
for t,r in enumerate(roots):
 old=lin((16+t,-Q(1,2)),(128+t,1),(240+t,1))
 new=dict(old)
 for i,q in enumerate(r):
  # old full centre: r_ti/4*(g_i+2x_i); old fl includes r_ti*x_i.
  add(old,8+i,Q(q,4));add(old,i,Q(q,2));add(old,i,-Q(q,2))
  add(new,8+i,Q(q,4))
 assert old==new
for i in range(8):
 old=lin((i,1),(8+i,Q(1,2)),(8+i,-Q(1,2)),(352+i,1))
 new=lin((i,1),(352+i,1))
 assert old==new
# Selected sign-target pair transform V and exactly its centre preconditioner.
for z in (Q(2),Q(-2)):
 V=((Q(1),Q(1)),(-z/2,z/2))
 I=((Q(1,2),-1/z),(Q(1,2),1/z))
 for A,B in ((V,I),(I,V)):
  assert all(sum(A[i][k]*B[k][j] for k in range(2))==int(i==j) for i in range(2) for j in range(2))
print('PASS:112 sign and8 coordinate raw targets agree for independent retained aggregate/own/cross variables')
print('PASS:both signed selected target2x2 bases and their literal inverses agree exactly')
print('LIMIT:restriction sets only deleted initial dirt to0; no complete800-column program or Gaussian replay executed')
print('SOURCE:PR425 e11ccea1d092beb1b01b4ee4ce49da478234254c; PR4332992f234bcb2538cb70f4d026aa8d08250b1040c')
