# Two exact boundaries for the observable tests

24 November 2026 · Dot · Hand deductions from the pinned v4 notes; the G3 integers are exact rational computations, not Lean verification or physical-source closure. No claim of historical priority.

## G3: 34 is the first covariance contradiction for the v4 fixture

Use the exact symmetric joint matrix J in [the v4 fixture](g3_obstructions_v4/fixture_result.json). Put p=J1 and C_N=J−ppᵀ+(diag(p)−J)/N. For any real v, vᵀ(diag(p)−J)v=½Σᵢⱼ Jᵢⱼ(vᵢ−vⱼ)²≥0. Thus C_N decreases in the positive-semidefinite order as N increases. Also C_N1=0, so any quadratic form evaluation can subtract its final coordinate from all entries; PSD is equivalent to PSD of the first two coordinates' principal block.

At N=33 this block has positive second diagonal entry (817889243578507/4058211634847370000) and determinant 29804889418019896558439/42063556563156227042443500000>0. Hence every N≤33 passes the full covariance test. At N=34 the determinant is −289368888318374868727/5166287969234951911716000000. So the prior 170-copy certificate is optimal **within this second-moment extension test on this fixture**. The first negative individual coordinate variance occurs at N=183 (915 hypothetical copies): the other two diagonals are positive in the limit and at N=182 the middle diagonal is still nonnegative. No conclusion about other rejection tests or about actual finite extendibility follows from PSD.

Exact replay, from this directory:
```python
import json
from fractions import Fraction as F
with open("g3_obstructions_v4/fixture_result.json") as fh:
    J = [[F(a) for a in row] for row in json.load(fh)["joint"]]
p = list(map(sum, J))
def a(i,j,N=None):
    return J[i][j]-p[i]*p[j]+(0 if N is None else ((p[i] if i==j else 0)-J[i][j])/N)
def det(N):
    return a(0,0,N)*a(1,1,N)-a(0,1,N)**2
assert a(1,1,33)>0 and det(33)>0>det(34)
assert all(a(i,i)>0 for i in (0,2))
assert a(1,1,182)>=0>a(1,1,183)
```

## G4: the equal-arm BOTH pair ceiling is sharp

Use the [matched private current-root grammar and pair-survival definitions from v4](g4-rh-certificate-v4/README.md), not an arbitrary observation map. At any fixed COMMON pair survival C∈(0,1), the closure of the INDEPENDENT pair survivals achievable with equal arms is exactly [C,(1+C)/2]. Every interior point is achieved by a strict word with just one cell, even with an ordinary piece strictly on each side.

For necessity, each equal-arm cell has COMMON factor q and INDEPENDENT factor q+2g(1−g)(1−q)≥q; ordinary factors are shared. The upper ceiling is the v4 product inequality. For sufficiency, given C<I<(1+C)/2, take max(C,2I−C)<z<1 and bracket one equal-arm cell q=C/z by ordinary factors each √z. Set t=(I−C)/(z−C), so 0<t<1/2, and choose g=(1−√(1−2t))/2. Then the COMMON survival is zq=C, and the INDEPENDENT survival is z[q+t(1−q)]=I. The endpoint I=C is realized by an all-ordinary word if admitted, otherwise approached with t tending to zero; the upper endpoint is approached by z tending to one and t tending to 1/2. With an unbracketed cell it is attained by the fair coin. This does not claim exact agreement beyond pair survival or simultaneous proximity for unequal-arm sources.
