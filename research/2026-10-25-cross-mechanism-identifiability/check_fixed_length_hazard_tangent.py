from fractions import Fraction as F
import json

def det(A):
    A=[r[:] for r in A];d=F(1)
    for i in range(len(A)):
        k=next(j for j in range(i,len(A)) if A[j][i])
        if k!=i:A[i],A[k]=A[k],A[i];d=-d
        a=A[i][i];d*=a
        for j in range(i+1,len(A)):
            q=A[j][i]/a
            for t in range(i,len(A)):A[j][t]-=q*A[i][t]
    return d

def evaluate(p,z):return sum(a*z**j for j,a in enumerate(p))
rows=[]
for L in range(1,9):
    # lambda0=s=1, Delta=log(2), hence every z and c is rational.
    z=[F(1,2**(r+1)) for r in range(1,L+2)]
    c=[F(r,(r+1)**2)*(1-z[r-1]) for r in range(1,L+2)]
    p=[F(1)]
    for x in z[:L]:
        q=[F(0)]*(len(p)+1)
        for j,a in enumerate(p):q[j]-=x*a;q[j+1]+=a
        p=q
    A=[[c[r]*z[r]**j for j in range(L)] for r in range(L)]
    D=det(A); formula=F(1)
    for v in c[:L]:formula*=v
    for r in range(L):
        for t in range(r+1,L):formula*=z[t]-z[r]
    assert D==formula and D!=0
    assert p[-1]==1 and p[0]!=0
    assert all(c[r]*evaluate(p,z[r])==0 for r in range(L))
    next_derivative=c[L]*evaluate(p,z[L]);assert next_derivative!=0
    rows.append(dict(L=L,rank=L,first_hazard_derivative=str(p[0]),next_moment_derivative=str(next_derivative),determinant=str(D)))
# The explicit one-site collision: exp(-(2+1)*tau)=1/2, tau=log(2)/3.
phi1=F(2,3)*(1-F(1,2))+F(1,2)*F(1,3)
assert phi1==F(1,2)
assert F(1,16)!=F(125,729) # rules out equality at the second ordinate
print(json.dumps({'status':'passed exact rational controls','tangent_cases':rows,'explicit_L1_first_ordinate':str(phi1),'second_ordinate_inequality_exact_cube_check':True,'scope':'Tangent and explicit L1 checks only; nonlinear IFT family established by written proof, not solver execution.'},indent=2))
