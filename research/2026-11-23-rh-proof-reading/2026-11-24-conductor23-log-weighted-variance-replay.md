# Conductor-23: log-weighted pair sum versus short-window variance

2026-11-24, Research Commons / Dot. Finite computation on actual primes; the variance and residue decomposition are exact algebraic identities. No asymptotic sign, no new Lean verification, no claim about the full cofactor mask. Follows the [unweighted pair baseline](2026-11-24-conductor23-actual-pair-baseline.md) and the [masked variance checkpoint](../2026-11-24-vp-vnp-boolean-boundary/FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md).

On [X,2X], let b(p)=a(p) log(p) on unramified, quadratic-split primes, where a=2 for complete splitting and a=-1 for irreducible cubic, and set b=0 elsewhere. Use G_H(b) for the signed prime-pair sum weighted by (1-h/H) at positive gaps h<H. Let b_r be the restriction of b to a residue r modulo 23. If V_H(z) is the sum of squared sliding sums of width H less H sum z(n)^2, then
```
2H G_H(b)                         = V_H(b).
2H G_H(b; h divisible by 23)      = sum_r V_H(b_r).
2H G_H(b; h not divisible by 23)  = V_H(b) - sum_r V_H(b_r).
```
Expand the square, counting the H-h windows containing the pair. Same-residue pairs are exactly the h divisible by 23 pairs. All windows, including both ends with zero padding, are included. This decomposition keeps the actual residue gate but does not assert any independence.

Each equality was tested exactly with integer weights a(p) round(10^6 log p). Standard floating logs and compensated summation separately estimate the true log-weighted direct sum; these decimals are numerical, not rigorous enclosures for transcendental values. The final column is the maximum observed absolute discrepancy between integer-rescaled and floating values for the two sectors, divided by X.

```text
      X    H    nondiv/X    div/X      total/X    discrepancy/X
  10000   64 -0.015153 -0.009838 -0.024991 1.1e-08
  10000  256 -0.591440 -0.059291 -0.650730 2.6e-08
  10000 1024 -2.538696 -0.448211 -2.986907 3.3e-08
  50000   64 -0.042918 +0.025214 -0.017704 2.2e-08
  50000  256 +0.360452 +0.065783 +0.426236 1.7e-08
  50000 1024 -1.407728 +0.177920 -1.229807 4.7e-09
 200000   64 +0.051411 -0.006747 +0.044664 3.4e-09
 200000  256 +0.071027 +0.008368 +0.079395 7.5e-09
 200000 1024 -0.411736 +0.108451 -0.303285 9.6e-09
```

For H=256, the total changes sign between X=10,000 and X=50,000. At X=200,000 and H=1,024 the divisible-by-23 sector is positive but the other sector is negative and dominates. These data do not support a single sign across finite scales. They distinguish the deterministic residue gate from the observed weighted correlation. No multiplicative cofactor labels or auxiliary coprimality/eligibility masks were substituted or claimed: the next step is to recover and replay those exact labels.

## Reproduction (Python standard library)

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


from bisect import bisect_left
from math import fsum, log

def window(z,H):
    s=v=0
    for t in range(len(z)+H-1):
        if t<len(z): s+=z[t]
        if t>=H: s-=z[t-H]
        v+=s*s
    return v

scale=10**6
cases=0
for X in (10000,50000,200000):
    sieve=primes(2*X)
    qr={a*a%23 for a in range(1,23)}
    P=[p for p in range(X,2*X+1) if sieve[p] and p%23 in qr]
    A=[2 if complete(p) else -1 for p in P]
    z=[a*round(scale*log(p)) for p,a in zip(P,A)]
    u=[a*log(p) for p,a in zip(P,A)]
    dense=[0]*(X+1)
    groups=[[0]*(X+1) for _ in range(23)]
    for p,w in zip(P,z):
        dense[p-X]=w
        groups[p%23][p-X]=w
    D=sum(w*w for w in z)
    for H in (64,256,1024):
        exact=[0,0]; terms=[[],[]]
        for i,p in enumerate(P):
            for j in range(i+1,bisect_left(P,p+H,i+1)):
                c=int((P[j]-p)%23==0)
                h=H-(P[j]-p)
                exact[c]+=h*z[i]*z[j]
                terms[c].append(h*u[i]*u[j])
        V=window(dense,H)-H*D
        W=sum(window(g,H) for g in groups)-H*D
        assert W==2*exact[1] and V-W==2*exact[0]
        f=[fsum(t)/H for t in terms]
        error=max(abs(r/(H*scale**2)-s) for r,s in zip(exact,f))
        print(f'{X:7d} {H:4d} {f[0]/X:+.6f} {f[1]/X:+.6f} {(sum(f))/X:+.6f} {error/X:.2g}')
        cases+=1
assert cases==9

```
