"""Independent bounded exact checks, not an asymptotic proof or matrix simulation."""
from fractions import Fraction as F
from math import comb
import json
checks=0
for N in range(3,65):
 r=comb(N,2); Delta=2*(N-1); sqrt_n=N**10; n=sqrt_n**2
 R=F(r*Delta,sqrt_n)
 assert R<=F(N,4); checks+=1
 assert F(12*r*r*Delta*Delta,sqrt_n)<=F(1,4); checks+=1
 # e^-2 < 1/4 gives this rigorous rational upper bound on Q0.
 Qcap=F(N+1,4**N)+F(2**N,4**(2*(N-1)))
 assert Qcap<=F(3,32); checks+=1
 ccap=(1-F(1,4**Delta))/(1+Qcap)
 assert ccap>=F(51,56)>F(3,4); checks+=1
 assert 16*n*R**4/N**4 <= F(256*r**4,n); checks+=1
 for s in range(1,N+1):
  gap=s*(N-s+1)
  assert gap>=N
  if 2<=s<=N-1: assert gap>=Delta
  checks+=1
for N in range(3,9):
 pairs=[(1<<i)|(1<<j) for i in range(N) for j in range(i+1,N)]
 for a in pairs:
  assert a.bit_count()==2; checks+=1
  for b in pairs:
   if a!=b:
    # Distinct pair flips have no diagonal matrix elements after composition.
    assert a^b != 0
    checks+=1
print(json.dumps({'status':'PASS','exact_checks':checks,'N_scalar_range':[3,64],
 'N_flip_range':[3,8], 'method':'integer combinatorics and Fraction inequalities',
 'limitation':'Not a numerical entropy, packing, all-N, or formal proof certificate.'},indent=2))
