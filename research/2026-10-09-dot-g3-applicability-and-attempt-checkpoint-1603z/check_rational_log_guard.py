"""Bounded arithmetic diagnostic only. No primality assumption is needed."""
from math import comb, gcd, prod
from fractions import Fraction
import json
import sympy as s
out=[]
for base in (2,3):
    values=[Fraction(sum(comb(n,k)*base**(k*(n-k)) for k in range(n+1)),2**n) for n in range(2,19)]
    decompositions=[]
    for v in values:
        num={int(p):int(e) for p,e in s.factorint(v.numerator).items()}
        den={int(p):int(e) for p,e in s.factorint(v.denominator).items()}
        assert prod(p**e for p,e in num.items())==v.numerator
        assert prod(p**e for p,e in den.items())==v.denominator
        d=num.copy()
        for p,e in den.items():d[p]=d.get(p,0)-e
        decompositions.append(d)
    factors=sorted(set().union(*(set(d) for d in decompositions)))
    assert all(p>1 for p in factors)
    assert all(gcd(p,q)==1 for i,p in enumerate(factors) for q in factors[:i])
    # Pairwise coprimality suffices for independence. We need not trust primality.
    A=s.Matrix([[d.get(p,0) for d in decompositions] for p in factors])
    _, row_pivots=A.T.rref()
    witness=A[list(row_pivots),:]
    det=int(witness.det())
    assert len(row_pivots)==17 and det!=0
    out.append({'q':f'1/{base}','n_range':[2,18],'values':[str(v) for v in values],
       'pairwise_coprime_factors':factors,'exponent_matrix':[[int(x) for x in row] for row in A.tolist()],
       'independent_row_indices':list(row_pivots),'minor_determinant':det,'rank':17,
       'factor_reconstruction_checked':True,'pairwise_gcd_checked':True})
print(json.dumps({'scope':'Two fixed rational nodes, normalized fair diagonals n=2..18 only; no all-cap result', 'cases':out},indent=2))
