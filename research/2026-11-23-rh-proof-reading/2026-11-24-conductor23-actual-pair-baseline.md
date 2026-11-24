# Conductor-23 prime-pair baseline: genuine splitting types

2026-11-24. Research Commons / Dot. Exact hand residue calculation and finite integer replay; not a correlation estimate, a new Lean proof, or a general GRH claim.

For f=x³-x-1 the discriminant is -23. For p≠23, the standard S3 character at the Frobenius of p is +2 for complete splitting, -1 for an irreducible cubic, and 0 for the transposition type. Quadratic reciprocity identifies the primes splitting in the discriminant field by the nonzero quadratic residues modulo 23 (including p=2). On that support the only two types are 2 and -1. To test complete splitting, compute x^p mod f over F_p: it equals x exactly when the squarefree cubic divides x^p-x, whose distinct roots are all elements of F_p.

**Exact local geometry.** If 23 divides h, there are 11 classes n mod 23 where both n and n+h are nonzero squares. Otherwise there are exactly 5. To see this, let chi be the Legendre character. The sum over n mod 23 of chi(n)chi(n+h) is -1 for h nonzero: the equation v²=n(n+h) has 22 solutions, since completing the square makes it a product of two variables equal to a fixed nonzero constant. Expand (1+chi(n))(1+chi(n+h)); before excluding n=0,-h its sum is 22. The excluded terms together equal 2 because chi(-1)=-1. Divide the remainder by 4. This counts residue classes, not actual prime pairs or their complete-splitting signs.

**Finite replay.** Use genuine distinct primes in [X,2X] and selected even gaps, restricting both components to the split support. With C=complete and N=irreducible, the signed integer total is 4 CC - 2 CN + NN, where CN combines both orientations. This deliberately omits logarithmic weights, cofactor filters and smoothing. It is a transparent control for the later masked calculation, not evidence of a uniform sign. The fast finite-field test is cross-checked by exhaustive root counts up to 2,000. The final column changes sign across gaps, and several fixed gaps change sign across these two windows.

```text
X h CC CN NN signed
10000 2 3 11 19 9
10000 4 3 16 16 -4
10000 6 9 30 31 7
10000 10 5 15 18 8
10000 22 6 18 14 2
10000 46 8 37 38 -4
10000 92 7 34 31 -9
50000 2 18 54 46 10
50000 4 13 57 51 -11
50000 6 28 99 105 19
50000 10 16 74 71 -13
50000 22 13 60 64 -4
50000 46 32 112 133 37
50000 92 29 121 127 1
```

```python
from math import isqrt

def primes(n):
    b=bytearray(b'\1')*(n+1)
    b[:2]=b'\0\0'
    for p in range(2,isqrt(n)+1):
        if b[p]: b[p*p::p]=b'\0'*((n-p*p)//p+1)
    return b

# x^3=x+1; reduce x^4=x^2+x.
def mul(a,b,p):
    v=[0]*5
    for i in range(3):
        for j in range(3): v[i+j]+=a[i]*b[j]
    return ((v[0]+v[3])%p,(v[1]+v[3]+v[4])%p,(v[2]+v[4])%p)

def complete(p):
    a,b,k=(1,0,0),(0,1,0),p
    while k:
        if k&1: a=mul(a,b,p)
        b=mul(b,b,p)
        k>>=1
    return a==(0,1,0)

def run(x):
    b=primes(2*x)
    residues={i*i%23 for i in range(1,23)}
    a=[0]*(2*x+1)
    checks=0
    for p in range(2,2*x+1):
        if not b[p] or p%23 not in residues: continue
        flag=complete(p)
        if p<=2000:
            assert flag==(sum((z*z*z-z-1)%p==0 for z in range(p))==3)
            checks+=1
        if p>=x: a[p]=2 if flag else -1
    for h in (2,4,6,10,22,46,92):
        cc=cn=nn=0
        for p in range(x,2*x-h+1):
            u,v=a[p],a[p+h]
            if not u or not v: continue
            if u==v==2: cc+=1
            elif u==v==-1: nn+=1
            else: cn+=1
        print(x,h,cc,cn,nn,4*cc-2*cn+nn)
    return checks

assert run(10000)==run(50000)

```

Next useful comparison: retain the original cofactor labels and masks from the analytic problem, then replay at least the log-weighted diagonal-subtracted variance using bounded eligible windows. The local support count and this simplified finite table do not estimate the signed discrepancy of the full weighted sum.
