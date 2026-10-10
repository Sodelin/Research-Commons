"""Exact rational count-kernel diagnostic. No numerical approximation or Lean."""
from fractions import Fraction as Q
from math import prod
import json
from pathlib import Path
N=5
lam=lambda n:n*(n-1)//2

def stirling(n,j):
    if n==0:return int(j==0)
    if j==0:return 0
    return j*stirling(n-1,j)+stirling(n-1,j-1)

def ordinary(n,j,q):
    if n==0:return Q(j==0)
    if j<1 or j>n:return Q(0)
    return prod(lam(k) for k in range(j+1,n+1))*sum((q**lam(k)/prod(lam(l)-lam(k) for l in range(j,n+1) if l!=k) for k in range(j,n+1)), Q(0))

def colour(n,j):
    if n==0:return Q(j==0)
    if j<1 or j>min(n,3):return Q(0)
    return Q(prod(range(3-j+1,4))*stirling(n,j),3**n)

P=[[colour(n,j) for j in range(N+1)] for n in range(N+1)]
E=[[ordinary(n,j,Q(1,2)) for j in range(N+1)] for n in range(N+1)]
K=[[(P[n][j]+E[n][j])/2 for j in range(N+1)] for n in range(N+1)]
def primitive(M,n):
    return M[n][n-2]+Q(n*(n-1),4)*M[n-1][n-1]-Q(n*(n-1)**2,4*(2*n-3))*M[n-2][n-2]-Q(n*(n-1)*(n-2),4*(2*n-3))*M[n][n]
def filt(M,n):
    return primitive(M,n)+Q(n,16*(2*n-3))*(M[n-2][n-2]-M[n][n])
controls={
'rows_normalized_nonnegative':all(sum(row)==1 and all(x>=0 for x in row) for M in [P,E,K] for row in M),
'mixture_all_admissible_count_entries_positive':all(K[n][j]>0 for n in range(1,N+1) for j in range(1,n+1)),
'ordinary_semigroup':all(sum(E[n][k]*E[k][j] for k in range(N+1))==ordinary(n,j,Q(1,4)) for n in range(N+1) for j in range(N+1)),
'ordinary_primitive_zero':all(primitive(E,n)==0 for n in [4,5]),
'linearity':filt(K,5)==(filt(P,5)+filt(E,5))/2,
'exact_negative_value':filt(K,5)==Q(-20245,18579456),
'count_zero_isolated':all(K[n][0]==Q(n==0) for n in range(N+1))}
assert all(controls.values())
out={'status':'EXACT_RATIONAL_DIAGNOSTIC_PASS','cap':N,'ordinary_survival':'1/2','mixture_weight':'1/2','colour_count':3,'filter_definition':'c_n + n/(16(2n-3)) (d_(n-2)-d_n)','filter_at_5':str(filt(K,5)),'colour_filter_at_5':str(filt(P,5)),'ordinary_filter_at_5':str(filt(E,5)),'c_5':str(primitive(K,5)),'d_3':str(K[3][3]),'d_5':str(K[5][5]),'controls':controls,'count_rows':[[str(x) for x in row] for row in K],'scope':'Generic exchangeable projective coarsening mixture; no admitted original-source realization asserted.'}
Path(__file__).with_name('RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
