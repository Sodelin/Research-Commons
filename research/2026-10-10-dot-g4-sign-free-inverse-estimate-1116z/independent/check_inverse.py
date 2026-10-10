#!/usr/bin/env python3
"""Independent exact count-law replay; cap nine only, no Lean or floating point."""
from fractions import Fraction as F
from math import comb, prod
from pathlib import Path
import hashlib, json

CAP = 9
Q, G = F(3,4), F(1,20)

def lam(n):
    return n*(n-1)//2

def ordinary(q):
    # Explicit distinct-eigenvalue formula for a pure-death chain with
    # k -> k-1 rate binom(k,2). Empty input is its own independent block.
    A = [[F(0) for _ in range(CAP+1)] for _ in range(CAP+1)]
    A[0][0] = F(1)
    for n in range(1,CAP+1):
        for j in range(1,n+1):
            multiplier = prod(lam(k) for k in range(j+1,n+1))
            terms = sum((q**lam(k) / prod(lam(ell)-lam(k)
                         for ell in range(j,n+1) if ell != k)
                         for k in range(j,n+1)), F(0))
            A[n][j] = multiplier * terms
    return A

def cell(q,g):
    O = ordinary(q)
    B = [[F(0) for _ in range(CAP+1)] for _ in range(CAP+1)]
    for n in range(CAP+1):
        for k in range(n+1):
            weight = comb(n,k)*g**k*(1-g)**(n-k)
            for a in range(k+1):
                for b in range(n-k+1):
                    B[n][a+b] += weight*O[k][a]*O[n-k][b]
    return B

def matmul(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(CAP+1)), F(0))
             for j in range(CAP+1)] for i in range(CAP+1)]

def inverse_lower(B):
    C = [[F(0) for _ in range(CAP+1)] for _ in range(CAP+1)]
    for n in range(CAP+1):
        C[n][n] = 1/B[n][n]
        for j in range(n):
            C[n][j] = -sum((B[n][k]*C[k][j] for k in range(j,n)),F(0))/B[n][n]
    return C

def encode(A):
    return [[str(x) for x in row] for row in A]

I = [[F(int(i==j)) for j in range(CAP+1)] for i in range(CAP+1)]
O = ordinary(Q)
B = cell(Q,G)
C = inverse_lower(B)
checks = {
    'ordinary_nonnegative_and_normalized': all(min(row)>=0 and sum(row)==1 for row in O),
    'cell_nonnegative_and_normalized': all(min(row)>=0 and sum(row)==1 for row in B),
    'ordinary_semigroup_at_3_4_and_2_3': matmul(O,ordinary(F(2,3))) == ordinary(F(1,2)),
    'ordinary_zero_time_identity': ordinary(F(1)) == I,
    'cell_zero_time_identity': cell(F(1),G) == I,
    'zero_coin_cell_is_ordinary': cell(Q,F(0)) == O,
    'cell_arm_exchange': cell(Q,1-G) == B,
    'pair_row_formula': B[2][2] == 2*G*(1-G)+(1-2*G*(1-G))*Q,
    'left_inverse_exact': matmul(C,B) == I,
    'right_inverse_exact': matmul(B,C) == I,
    'entry_9_1_is_strictly_negative': C[9][1] < 0,
    'checkerboard_sign_9_1_would_be_positive': (-1)**(9-1) == 1,
}
assert all(checks.values()), checks
kernel_data = {'cap':CAP,'pair_survival':str(Q),'coin':str(G),'ordinary':encode(O),'cell':encode(B),'inverse':encode(C)}
P=Path(__file__).resolve().parent
raw=(json.dumps(kernel_data,sort_keys=True,indent=2)+'\n').encode()
(P/'EXACT-MATRICES.json').write_bytes(raw)
expected = F(-140047749763889319747912838165364543929601100971867648166192210955550028142707842245781448089,
6618330063726707784181572672593018997835528051851418470338336437425485108474782459829025630183)
assert C[9][1] == expected
result = {'status':'PASS','scope':'Independent exact actual equal-arm INDEPENDENT cell count-kernel inverse; cap nine only.',
    'n':9,'j':1,'pair_survival':str(Q),'coin':str(G),'entry':str(C[9][1]),
    'matches_author_fraction':C[9][1]==expected,'checks':checks,
    'exact_matrices_sha256':hashlib.sha256(raw).hexdigest(),
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'limitation':'Refutes checkerboard positivity for the actual cell inverse. No physical inverse, rival construction, full-forest inverse norm bound, or G4 closure follows.'}
(P/'RESULT.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps(result,sort_keys=True,indent=2))
