from fractions import Fraction as F
from pathlib import Path
import json

L=[1,3,6,10,15,21,28]
c=[-7844455869249906219770661963537978086986704,
105390350242235735016226643936995742841926340,
-1605030922943759975324171524620294430732933125,
24524880652259591643428797130387478968872639375,
-280129932672131919320829979372363581722030028300,
461875570693459839305533042687141292894301124344,
-204763033645016737481604144902518353475165741930]

def inv(a):
    n=len(a); a=[list(map(F,row))+[F(i==j) for j in range(n)] for i,row in enumerate(a)]
    for j in range(n):
        i=next(i for i in range(j,n) if a[i][j])
        a[i],a[j]=a[j],a[i]
        z=a[j][j]; a[j]=[x/z for x in a[j]]
        for i in range(n):
            if i!=j:
                z=a[i][j]; a[i]=[x-z*y for x,y in zip(a[i],a[j])]
    return [r[n:] for r in a]

# Logarithmic moment derivatives in log A,log B and the four head coordinates.
J=[]
for l in L:
    row=[F(l),F(1)]
    for q in (F(1,2),F(1,3)):
        p=F(1,2); f=1-p+p*q**l
        row.extend([(q**l-1)/f,p*l*q**(l-1)/f])
    J.append(row)
assert all(sum(F(c[i])*J[i][j] for i in range(7))==0 for j in range(6))
assert c[0]<0 and c[-1]<0
Ji=inv(J[:6])
assert all(sum(J[i][k]*Ji[k][j] for k in range(6))==F(i==j) for i in range(6) for j in range(6))
ratio=-sum(J[-1][k]*Ji[k][0] for k in range(6))
assert ratio==F(c[0],c[-1]) and ratio>0
# The extra signed-q column, after positive p/(1-p) scaling, is e_1.
full=[row+[F(i==0)] for i,row in enumerate(J)]
inv(full)
print('PASS: six exact boundary columns annihilated by inherited c')
print('PASS: first-six boundary Jacobian invertible')
print('PASS: seven-column signed-q Jacobian invertible')
print('PASS: transverse normalized moment derivative = c_1/c_28 > 0')
print('PASS: Gamma sign = sign(m_28-R), because c_28 < 0')
print('c_1/c_28 =', ratio)
Path(__file__).with_name('transverse-certificate.json').write_text(json.dumps({'Lambda':L,'c':c,'normalized_transverse_ratio':str(ratio),'jacobian_rows':[[str(x) for x in row] for row in J],'first_six_inverse':[[str(x) for x in row] for row in Ji]},indent=2)+'\n')
