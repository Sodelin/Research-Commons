"""Own exact finite controls; the universal proof is in candidate15."""
from math import comb
import sympy as s
for n in [2,4,6,10,60]:
    m=n//2; rows=[]
    for k in range(m):
        row=[]
        for start in range(m):
            counts=[0]*n;counts[start]=1
            for _ in range(2*k):
                counts=[(counts[i-1] if i else 0)+(counts[i+1] if i+1<n else 0) for i in range(n)]
            row.append(counts[start])
        rows.append(row)
    deficits=[]
    for k in range(1,m):
        d=[comb(2*k,k)-v for v in rows[k]]
        assert d[k-1]==1 and all(v==0 for v in d[k:])
        deficits.append(d)
    basis=s.Matrix(deficits+[[1]*m])
    assert basis.det()==1
    assert s.Matrix(rows).det()!=0
    print('PASS length',n,'triangular determinant',basis.det(),'moment matrix rank',m)
n=60;A=s.zeros(n);K=s.zeros(n)
for j in range(n-1):A[j,j+1]=A[j+1,j]=1;K[j,j+1]=1;K[j+1,j]=-1
a=s.symbols('a0:60');V=s.diag(*a)
# Off-parity trace cancellations are symbolic and exact at full size.
W=s.eye(n)
for k in range(30):
    assert s.trace(W*A)==0
    assert s.trace(W*(V*A+A*V))==0
    assert all(W[j,j]==W[n-1-j,n-1-j] for j in range(n))
    W=W*K*K
print('PASS full 60-site symbolic trace cancellations for k=0,...,29; SymPy',s.__version__)
