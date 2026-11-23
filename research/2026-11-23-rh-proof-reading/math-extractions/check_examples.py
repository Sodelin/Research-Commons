from fractions import Fraction as F
from itertools import permutations, product
from math import prod

def det(A):
    return sum(
        (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1,len(p)))
        * prod(A[i][p[i]] for i in range(len(p)))
        for p in permutations(range(len(A)))
    )

# Discrete measures in the transformed coordinates, with strictly separated supports.
z = [(F(1,9),F(2,9)), (F(4,9),F(5,9)), (F(7,9),F(8,9))]
n = len(z)
A = [[sum(t**i for t in zj)/len(zj) for zj in z] for i in range(n)]
sep = prod(z[j][0]-z[i][-1] for i in range(n) for j in range(i+1,n))
vander = sum(prod(t[j]-t[i] for i in range(n) for j in range(i+1,n))
             for t in product(*z))/prod(map(len,z))
assert det(A)==vander and vander>=sep>0
# Non-deduplicated stream with adversarially repeated worse candidates.
weights = [F(3), F(2), F(1)]
ref = [{0,1},{0,2},{1,2}]
stream = [ref[0]]*10 + ref
score = lambda row: sum(weights[i] for i in row)
assert min(map(score,stream)) <= F(2,3)*sum(weights)
assert sum(map(score,stream))/len(stream) > F(2,3)*sum(weights)
# Finite grid for the 2η approximate-score bound, including the tight case.
err = [F(-1,2),F(0),F(1,2)]
for shifts in product(err,repeat=len(ref)):
    i = min(range(len(ref)),key=lambda i:score(ref[i])+shifts[i])
    assert score(ref[i])<=F(2,3)*sum(weights)+1
assert score(ref[1]) == F(2,3)*sum(weights)
print("PASS: exact normalized moment determinant, separated-support bound, repeated-stream control, and 27 noisy-score controls.")
