"""Conservative exact-arithmetic CF confidence masks for the peer adapter.

COMPONENT ONLY: known correct order and known absolute CF gap in the
source-identified level-one NMSC model. Not an all-level biological oracle.
Counts are (ab|cd, ac|bd, ad|bc); candidate COMPLETE support masks are 1,4,5.
Return an empty set on inconsistency, not mask 0. The caller must abstain on
empty/ambiguous sets. IID loci; arbitrarily dependent quartets within a locus.
"""
from fractions import Fraction as F
from numbers import Integral
from pathlib import Path
from typing import Sequence
import hashlib
import json


def fraction_probability(x, name, allow_one=False):
    if isinstance(x, bool):
        raise ValueError(f'{name} must not be bool')
    p = x if isinstance(x, F) else F(str(x))
    if not 0 < p <= 1 or (p == 1 and not allow_one):
        raise ValueError(f'invalid {name}')
    return p


def risk_exponent(alpha):
    """Exact smallest integer k with 4*2**(-k) <= alpha."""
    a = fraction_probability(alpha, 'alpha')
    ratio = 4/a
    k = max(0, ratio.numerator.bit_length()-ratio.denominator.bit_length())
    if (1 << k)*ratio.denominator < ratio.numerator:
        k += 1
    assert 4*F(1, 1 << k) <= a
    return k


def cf_confidence_masks(counts: Sequence[int], min_gap, alpha) -> frozenset[int]:
    """Return candidate complete support masks with marginal coverage >=1-alpha.

    Hoeffding radius squared is 2*k/m, k=ceil(log2(4/alpha)). Since e>2,
    4*exp(-k) <= 4*2**(-k) <= alpha. All comparisons below are rational;
    neither transcendental rounding nor a computed square root is needed.
    """
    if len(counts) != 3 or any(isinstance(x,bool) or not isinstance(x,Integral) or x < 0 for x in counts):
        raise ValueError('counts must be three nonnegative integers')
    m = int(sum(counts))
    if m == 0:
        raise ValueError('at least one locus is required')
    gap = fraction_probability(min_gap, 'min_gap', allow_one=True)
    radius_squared = F(2*risk_exponent(alpha), m)
    options = {}
    for t in (0,2):
        center = abs(F(int(counts[t]-counts[1]), m))
        absent = center**2 <= radius_squared
        # Existence of a signed mean with absolute magnitude >=gap in the CI.
        present = center >= gap or (gap-center)**2 <= radius_squared
        options[t] = (absent, present)
    return frozenset(mask for mask in (1,4,5)
                     if all(options[t][bool(mask & (1 << t))] for t in (0,2)))


def shared_prefix_loci(min_gap, query_index: int, delta) -> int:
    """Sufficient prefix for singleton output on the contrast-coverage event."""
    if isinstance(query_index,bool) or not isinstance(query_index,Integral) or query_index < 1:
        raise ValueError('query_index must be a positive integer')
    gap = fraction_probability(min_gap, 'min_gap', allow_one=True)
    risk = fraction_probability(delta, 'delta') / (query_index*(query_index+1))
    bound = 8*risk_exponent(risk)/gap**2
    return bound.numerator//bound.denominator+1  # strict r < gap/2


def verify():
    cases=[((F(1,2),F(1,4),F(1,4)),F(1,4),1),
           ((F(1,4),F(1,4),F(1,2)),F(1,4),4),
           ((F(2,5),F(1,5),F(2,5)),F(1,5),5),
           ((F(1,4),F(3,8),F(3,8)),F(1,8),1)]
    total=covered=0
    alpha=F(1,20)
    for p,g,truth in cases:
        for m in range(1,21):
            r2=F(2*risk_exponent(alpha),m)
            for a in range(m+1):
                for b in range(m-a+1):
                    counts=(a,b,m-a-b)
                    candidates=cf_confidence_masks(counts,g,alpha)
                    assert candidates <= {1,4,5}
                    errors=[F(counts[t]-counts[1],m)-(p[t]-p[1]) for t in (0,2)]
                    if all(e*e <= r2 for e in errors):
                        assert truth in candidates
                        covered+=1
                    total+=1
    assert cf_confidence_masks((1,1,1),F(1,8),alpha)=={1,4,5}
    for counts,g,truth in [((20000,30000,30000),F(1,8),1),
                           ((32000,16000,32000),F(1,5),5)]:
        assert cf_confidence_masks(counts,g,alpha)=={truth}
    assert cf_confidence_masks((30000,30000,30000),F(1,4),alpha)==frozenset()
    for j in range(1,21):
        m=shared_prefix_loci(F(1,8),j,alpha)
        k=risk_exponent(alpha/(j*(j+1)))
        assert F(2*k,m) < F(1,8)**2/4
    report={'session':'ASTRA-STAT-20260930-0942Z',
            'scope':'exact-rational CF confidence-provider checks; level-one gap component only',
            'count_states_checked':total,'inside_coverage_event':covered,
            'empty_ambiguous_positive_and_negative_controls':'passed',
            'shared_prefix_checks':20,
            'sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('confidence-verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O')
    verify()
