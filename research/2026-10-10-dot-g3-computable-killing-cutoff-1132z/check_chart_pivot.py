from fractions import Fraction as F
from pathlib import Path
import json
R=Path(__file__).resolve().parent
L=(1,3,6,10,15,21,28)
J=[]
for k in L:
 row=[F(k),F(1)]
 for q in (F(1,2),F(1,3)):
  z=q**k
  row.extend([2*(1-z)/(1+z),-F(k)*q**(k-1)/(1+z)])
 J.append(row)
A=J[:6]
B=[r[:]+[F(int(i==j)) for j in range(6)] for i,r in enumerate(A)]
for j in range(6):
 i=next(i for i in range(j,6) if B[i][j]);B[j],B[i]=B[i],B[j]
 z=B[j][j];B[j]=[x/z for x in B[j]]
 for i in range(6):
  if i!=j:
   z=B[i][j];B[i]=[x-z*y for x,y in zip(B[i],B[j])]
AI=[r[6:] for r in B]
assert all(sum(A[i][k]*AI[k][j] for k in range(6))==int(i==j) for i in range(6) for j in range(6))
assert all(sum(AI[i][k]*A[k][j] for k in range(6))==int(i==j) for i in range(6) for j in range(6))
K=max(sum(abs(x) for x in r) for r in AI)
print('PASS first-six chart matrix invertible; both exact products A*Ainv and Ainv*A equal I')
print('K=||Ainv||infinity=',K)
(R/'chart-pivot.json').write_text(json.dumps({'Lambda':L,'J':[[str(x) for x in r] for r in J],'A_inverse':[[str(x) for x in r] for r in AI],'K':str(K)},indent=2)+'\n')
