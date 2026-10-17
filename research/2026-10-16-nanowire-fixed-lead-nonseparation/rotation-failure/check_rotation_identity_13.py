"""Own bounded exact check of the fixed-60-site rotation's admission failure."""
import sympy as s
n=60
A=s.zeros(n);K=s.zeros(n)
for j in range(n-1):
    A[j,j+1]=A[j+1,j]=1
    K[j,j+1]=1;K[j+1,j]=-1
comm=lambda X,Y:X*Y-Y*X
D=comm(K,A);E=comm(K,D)
expectedD=s.zeros(n);expectedD[0,0]=2;expectedD[n-1,n-1]=-2
expectedE=s.zeros(n)
for i,j in [(0,1),(1,0),(n-2,n-1),(n-1,n-2)]:expectedE[i,j]=-2
assert D==expectedD and E==expectedE
# One independent symbol per onsite entry, preserving the full original size.
a=s.symbols('a0:60');V=s.diag(*a);C=comm(K,V)
expectedC=s.zeros(n)
for j in range(n-1):expectedC[j,j+1]=expectedC[j+1,j]=a[j+1]-a[j]
assert C==expectedC
print('PASS: exact symbolic 60-site identities; SymPy',s.__version__)
print('[K,A] nonzero entries (zero-based):',[(i,j,D[i,j]) for i in range(n) for j in range(n) if D[i,j]])
print('[K,[K,A]] nonzero entries:',[(i,j,E[i,j]) for i in range(n) for j in range(n) if E[i,j]])
print('[K,diag(a)] has only neighboring symmetric entries a[j+1]-a[j].')
print('Scope: fixed generator exp(theta K), continuous admission near zero only.')
