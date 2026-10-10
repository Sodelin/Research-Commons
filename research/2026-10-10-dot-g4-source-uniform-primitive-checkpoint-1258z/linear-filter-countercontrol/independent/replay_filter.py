"""Independent cap-five Fraction replay using an ODE coefficient recurrence.

Paintbox rows are enumerated from actual colour tuples, without Stirling numbers.
The ordinary rows solve the finite pure-death forward equations as polynomials
in q=exp(-t), without the author's partial-fraction formula.
This is a non-source partition countercontrol, not a biological realization.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

N = 5
lam = lambda j: j*(j-1)//2
def eval_poly(poly, q):
    return sum((v*q**e for e,v in poly.items()), Q(0))

def ordinary_row(n, q):
    if n == 0:
        return [Q(1)] + [Q(0)]*N
    polys = {n: {lam(n): Q(1)}}
    for j in range(n-1, 0, -1):
        nxt = polys[j+1]
        cur = {e: Q(-lam(j+1))*a/Q(e-lam(j)) for e,a in nxt.items()}
        cur[lam(j)] = -sum(cur.values(), Q(0))
        # Coefficientwise q P'_j - lambda_j P_j = -lambda_(j+1) P_(j+1).
        for e in set(cur) | set(nxt):
            assert Q(e-lam(j))*cur.get(e,Q(0)) == -lam(j+1)*nxt.get(e,Q(0))
        assert sum(cur.values()) == 0
        polys[j] = cur
    return [Q(0)] + [eval_poly(polys[j],q) if j<=n else Q(0) for j in range(1,N+1)]

def colour_row(n):
    hist = [0]*(N+1)
    for colours in product(range(3), repeat=n):
        hist[len(set(colours))] += 1
    return [Q(x,3**n) for x in hist]

P = [colour_row(n) for n in range(N+1)]
E = [ordinary_row(n,Q(1,2)) for n in range(N+1)]
K = [[(x+y)/2 for x,y in zip(a,b)] for a,b in zip(P,E)]
def c(M,n):
    return M[n][n-2]+Q(n*(n-1),4)*M[n-1][n-1]-Q(n*(n-1)**2,4*(2*n-3))*M[n-2][n-2]-Q(n*(n-1)*(n-2),4*(2*n-3))*M[n][n]
def F(M,n):
    return c(M,n)+Q(n,16*(2*n-3))*(M[n-2][n-2]-M[n][n])

assert all(sum(row)==1 and min(row)>=0 for M in (P,E,K) for row in M)
assert all(K[n][j]>0 for n in range(1,N+1) for j in range(1,n+1))
assert all(c(E,n)==0 for n in (4,5))
assert all(sum(E[n][k]*E[k][j] for k in range(N+1))==ordinary_row(n,Q(1,4))[j] for n in range(N+1) for j in range(N+1))
assert F(K,5)==(F(P,5)+F(E,5))/2
assert F(K,5)==Q(-20245,18579456)
out={
    'status':'INDEPENDENT_EXACT_REPLAY_PASS', 'cap':N,
    'method':'ODE coefficient recursion plus direct colour-tuple enumeration',
    'c5':str(c(K,5)), 'd3':str(K[3][3]), 'd5':str(K[5][5]),
    'paintbox_filter':str(F(P,5)), 'ordinary_filter':str(F(E,5)),
    'mixture_filter':str(F(K,5)), 'rows':[[str(v) for v in row] for row in K],
    'scope':'Generic exchangeable projective partition mixture; no admitted source claimed.'
}
Path(__file__).with_name('RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
