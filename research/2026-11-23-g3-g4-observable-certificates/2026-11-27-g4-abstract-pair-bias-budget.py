from fractions import Fraction as F
from math import prod
from random import Random
import json
rng=Random(2325)
def check(cells):
    J=F(1);B=F(0);D=F(0)
    P=Q=F(1);smooth=F(1)
    for a,b,g in cells:
        w=g*(1-g);m=g*a+(1-g)*b
        j=(g*a**3+(1-g)*b**3-m**3)/m**3
        J*=1+j;B+=w*(2*g-1)**2
        D+=w*(a-b)**2/m**2
        p=g*g*a+(1-g)**2*b+2*w
        q=(1-2*w)*m+2*w
        assert p-q==w*(2*g-1)*(a-b)
        assert 0<p<=1 and 0<q<=1 and j>=2*w*(a-b)**2/m**2
        P*=p;Q*=q;smooth*=m
    assert D<=(J-1)/2
    assert (P-Q)**2<=(J-1)*B/2
    return J-1,B,P,Q
for j in range(800):
    n=rng.randrange(1,20)
    A=[tuple(F(rng.randrange(1,101),101) for _ in range(3)) for _ in range(n)]
    check(A)
J,B,P,Q=check([(F(1,20),F(19,20),F(1,2))]*20)
assert J>0 and B==0 and P==Q
J,B,P,Q=check([(F(1,20),F(19,20),F(1,4))])
assert B>0 and P!=Q
for n in [4,8,16,32]:
    J,B,P,Q=check([(1-F(1,n),1-F(1,10*n),F(1,4))]*n)
    assert P!=Q and B==F(3*n,64)
print(json.dumps(dict(schema='commons.pair-bias-budget.v1',randomWords=800,balancedExact=1,biasedNegative=1,
                      growingBiasBudget=4,lean='not_run')))
