"""Statistical wrappers for adaptive, discrete quartet-support queries.

Research code: ASTRA-STAT-20260930-0942Z. Standard library only.
The formulas require the assumptions in REPORT.md; they do not certify them.
Counts are for (ab|cd, ac|bd, ad|bc) with a,b,c,d in the supplied cyclic order.
The crossing topology is index 1. No raw gene-support interpretation under NMSC.
"""
from __future__ import annotations
from fractions import Fraction
from math import ceil, isfinite, log, log1p
from numbers import Integral
from typing import Sequence


def _positive_int(value: int, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, Integral) or value < 1:
        raise ValueError(f"{name} must be a positive integer")
    return int(value)


def _probability(value: float, name: str, *, allow_one: bool = False) -> float:
    x = float(value)
    if not isfinite(x) or x <= 0 or (x > 1 if allow_one else x >= 1):
        raise ValueError(f"{name} must be finite and in (0, {'1]' if allow_one else '1)'}")
    return x


def _counts(counts: Sequence[int]) -> tuple[int, int, int]:
    if len(counts) != 3 or any(isinstance(c, bool) or not isinstance(c, Integral) or c < 0 for c in counts):
        raise ValueError("counts must contain exactly three nonnegative integers")
    result = tuple(map(int, counts))
    if sum(result) == 0:
        raise ValueError("at least one locus is required")
    return result  # type: ignore[return-value]


def _crossing(crossing: int) -> int:
    if isinstance(crossing, bool) or not isinstance(crossing, Integral) or crossing not in (0, 1, 2):
        raise ValueError("crossing must be 0, 1 or 2")
    return int(crossing)


def cf_support(counts: Sequence[int], min_gap: float | Fraction, crossing: int = 1) -> frozenset[int]:
    """Signed CF rule. Requires |p_t-p_cross|=0 off support and >=min_gap on it.

    A negative contrast is allowed. An empty answer can occur on the failure
    event; this function does not silently replace it with a preferred topology.
    Fractions give exact threshold comparisons; floats are interpreted by str.
    """
    c = _counts(counts)
    x = _crossing(crossing)
    _probability(float(min_gap), "min_gap", allow_one=True)
    gap = min_gap if isinstance(min_gap, Fraction) else Fraction(str(min_gap))
    threshold = sum(c) * gap
    return frozenset(t for t in range(3) if t != x and 2 * abs(c[t] - c[x]) > threshold)


def no_ils_support(counts: Sequence[int], crossing: int = 1) -> frozenset[int]:
    """Empirical support ONLY for an exact no-ILS displayed-tree sampling model.

    Observing the forbidden crossing topology is an explicit model/order error.
    Absence in a finite sample is reliable only with the stated mass calibration.
    """
    c = _counts(counts)
    x = _crossing(crossing)
    if c[x] != 0:
        raise ValueError("crossing observations violate the no-ILS/common-order model")
    return frozenset(t for t in range(3) if c[t] > 0)


def fixed_cf_loci(min_gap: float, query_bound: int, delta: float) -> int:
    """A priori B: ceil(8/gap^2 * log(4 B/delta)). Not for an observed B."""
    g = _probability(min_gap, "min_gap", allow_one=True)
    b = _positive_int(query_bound, "query_bound")
    d = _probability(delta, "delta")
    return max(1, ceil(8 / g**2 * (log(4) + log(b) - log(d))))


def streaming_cf_loci(min_gap: float, query_index: int, delta: float) -> int:
    """Predetermined shared prefix for query j; risk delta/[j(j+1)]."""
    j = _positive_int(query_index, "query_index")
    return fixed_cf_loci(min_gap, j * (j + 1), delta)


def fixed_no_ils_loci(min_mass: float, query_bound: int, delta: float) -> int:
    """Common circular order implies at most two displayed quartet topologies."""
    rho = _probability(min_mass, "min_mass", allow_one=True)
    b = _positive_int(query_bound, "query_bound")
    d = _probability(delta, "delta")
    if rho == 1:
        return 1
    return max(1, ceil((log(2) + log(b) - log(d)) / -log1p(-rho)))


def streaming_no_ils_loci(min_mass: float, query_index: int, delta: float) -> int:
    j = _positive_int(query_index, "query_index")
    return fixed_no_ils_loci(min_mass, j * (j + 1), delta)


def cf32(x1: Fraction, x2: Fraction, x3: Fraction, x4: Fraction,
         hybrid: Fraction = Fraction(1, 2)) -> tuple[Fraction, Fraction, Fraction]:
    """Source equation before Proposition 10, Allman et al. (2019).

    x_i=exp(-t_i), using the SOURCE'S Figure 5 parameter labels. This function
    checks rational identities, not a new independently simulated NMSC process.
    """
    h = hybrid
    for x in (x1, x2, x3, x4, h):
        if not isinstance(x, Fraction) or not 0 < x < 1:
            raise ValueError("this positive-length check requires Fraction inputs in (0,1)")
    p0 = (1-h)**2 * (1-Fraction(2,3)*x1*x2) + 2*h*(1-h)*(1-x1+x1*x3/3) + h*h*(1-Fraction(2,3)*x1*x4)
    p1 = (1-h)**2*x1*x2/3 + h*(1-h)*x1*(1-x3/3) + h*h*x1*x4/3
    assert p0 + 2*p1 == 1
    return p0, p1, p1
