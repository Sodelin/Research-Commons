# Five-lane finite replay packet

2026-11-24, Research Commons / Dot. Finite checks only, with the matching hand results linked. No new Lean or conjecture closure.

- **P vs NP:** The [nonlinear ring](AND-OR-RINGS-AND-SPECTRAL-TEST.md) is now also tested as a signed weighted count: 192 exact comparisons of direct assignment enumeration with the trace of an ordered product of transfer matrices. This tests connected structured formulas, not arbitrary SAT.
- **BSD:** Test the [primitive quadratic grid](FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md) on all two-parameter primitive coefficient vectors modulo 3 (728) and modulo 4 with at least one odd coefficient (4,032). There is a nonzero grid value modulo the tested modulus in every case. Arithmetic heights did not enter this computation. In particular, the tests do not establish admissible height directions.
- **Artin:** [Separate weighted prime-pair replay](../2026-11-23-rh-proof-reading/2026-11-24-conductor23-log-weighted-variance-replay.md): nine exact direct/window comparisons on actual primes with rounded logarithms and two residue sectors. No full cofactor eligibility mask.
- **Goldbach:** Check [largest-prime orientation](FIVE-LANE-INTERFACES-AND-OBSTRUCTIONS.md) in 14,105 allocations of distinct sampled prime triples meeting the roughness, size and ratio conditions (39 with singleton u and 14,066 with singleton v). This checks divisor geometry only. It does not test qh+d ell=N, the remaining masks or the analytic cutoff/signed bound.
- **Yang–Mills:** Check 48 synthetic positive spectral measures with a forbidden low-energy atom. All pass the scalar degree-zero test, and each fails the degree-one test using P(x)=x-x0. This is an exact illustration of the [moment test](../2026-11-24-yang-mills-mass-gap-reading/MOMENT-MATRIX-BRIDGE.md), not a measurement of the actual lattice theory.

```text
SAT transfer comparisons: 192
BSD primitive polynomials, mod 3 and mod 4: [728, 4032]
Goldbach geometry cases (singleton u, singleton v): [39, 14066]
Yang-Mills synthetic spectral tests: 48
```

Reproduction (Python standard library):

```python
from itertools import combinations, product
from fractions import Fraction as Q
from math import isqrt

# Weighted AND/OR ring: exact direct assignments vs transfer matrices.
def ring():
    count=0
    for f in (min,max):
      for q in (2,3,4):
       for r in range(3,7):
        for k in range(8):
         def w(j,i,s): return (13*j+7*i+5*s+3*k+i*s)%11-5
         def edge(i,a,b): return w(0,i,f(a,b))*w(1,(i+1)%r,b)
         a=0
         for y in product(range(q),repeat=r):
          v=1
          for i in range(r): v*=edge(i,y[i],y[(i+1)%r])
          a+=v
         mat=[[int(i==j) for j in range(q)] for i in range(q)]
         for i in range(r):
          mat=[[sum(mat[j][m]*edge(i,m,k1) for m in range(q))
                for k1 in range(q)] for j in range(q)]
         assert a==sum(mat[j][j] for j in range(q))
         count+=1
    return count

# Primitive quadratic coefficients: exact grid guarantee modulo 3 and 4.
def bsd():
    grid=((0,0),(1,0),(0,1),(2,0),(0,2),(1,1))
    out=[]
    for p,m in ((3,3),(2,4)):
     count=0
     for a,b,c,d,e,f in product(range(m),repeat=6):
      if not any(v%p for v in (a,b,c,d,e,f)): continue
      assert any((a+b*x+c*y+d*x*x+e*x*y+f*y*y)%m for x,y in grid)
      count+=1
     out.append(count)
    return out

# Largest-prime/sign geometry only; not the fixed-N arithmetic mask.
def gold():
    N=10**12
    pool=[p for p in range(107,2100) if p**160>=N**27
           and all(p%d for d in range(2,isqrt(p)+1))][::5]
    pool += [p for p in range(12000,19000)
             if all(p%d for d in range(2,isqrt(p)+1))][::15]
    bins=[0,0]
    for xyz in combinations(pool,3):
     d=xyz[0]*xyz[1]*xyz[2]
     if d>N: continue
     for p in xyz:
      ab=d//p
      u,v=max(p,ab),min(p,ab)
      if u**10>N*v**10: continue
      count=int(u!=p)
      assert p==max(xyz)
      assert (p*p>d)==(u==p)
      bins[count]+=1
    return bins

# Two-atom spectral measures where scalar (degree zero) accepts;
# polynomial P(x)=x-x0 reveals the forbidden low-energy atom.
def yang():
    n=0
    for b in (Q(1,3),Q(1,2),Q(2,3)):
     for x0 in (b/4,b/2):
      for x1 in (b+(1-b)/3,b+2*(1-b)/3):
       eps_max=(b-x0)/(x1-x0)
       for k in (2,3,5,11):
        eps=eps_max/k
        assert (1-eps)*(b-x0)+eps*(b-x1)>0
        assert eps*(b-x1)*(x1-x0)**2<0
        n+=1
    return n

print('SAT transfer comparisons:',ring())
print('BSD primitive polynomials, mod 3 and mod 4:',bsd())
print('Goldbach geometry cases (singleton u, singleton v):',gold())
print('Yang-Mills synthetic spectral tests:',yang())

```
