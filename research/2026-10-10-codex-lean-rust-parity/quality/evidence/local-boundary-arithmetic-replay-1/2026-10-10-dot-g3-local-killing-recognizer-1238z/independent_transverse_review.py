"""Independent Fraction/cofactor check; no neighborhood or cutoff evaluation."""
from fractions import Fraction as F
from pathlib import Path
import json, math
P=Path(__file__).parent
cert=json.loads((P/'transverse-certificate.json').read_text())
L=(1,3,6,10,15,21,28)
c=cert['c']
J=[]
for l in L:
    row=[F(l), F(1)]
    for v in (2,3):
        q=F(1,v); f=(1+q**l)/2
        row += [(q**l-1)/f, F(l,2)*q**(l-1)/f]
    J.append(row)

def det(M):
    n=len(M); a=[]; den=1
    for r in M:
        d=math.lcm(*(x.denominator for x in r)); den*=d
        a.append([int(x*d) for x in r])
    sign=1; prev=1
    for k in range(n-1):
        j=next((j for j in range(k,n) if a[j][k]),None)
        if j is None: return F(0)
        if j!=k: a[k],a[j]=a[j],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                v=pivot*a[i][j]-a[i][k]*a[k][j]
                assert v%prev==0
                a[i][j]=v//prev
        for i in range(k+1,n): a[i][k]=0
        prev=pivot
    return F(sign*a[-1][-1],den)

assert all(sum(c[i]*J[i][j] for i in range(7))==0 for j in range(6))
d6=det(J[:6]); d7=det([r+[F(i==0)] for i,r in enumerate(J)])
assert d6 and d7
assert d7/d6==F(c[0],c[-1])>0
assert all(J[i][j]==F(cert['jacobian_rows'][i][j]) for i in range(7) for j in range(6))
print('PASS independent row-scaled integer Bareiss determinants: six and seven columns full rank')
print('PASS independent determinant ratio equals c_1/c_28 > 0')
print('PASS independently rebuilt log-moment derivatives and full normal annihilation')
print('PASS certificate rows agree exactly; no inverse matrix was consumed')
print('No cutoff, base point, chart box, output radius, QE certificate or source computed.')
