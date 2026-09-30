"""Exact-rational robust complete-support certificates (research prototype).

Scientific premises are inputs, not inferred by this module. Each row contains
counts from UNIQUE loci in that row's prefix stream. The anytime radius covers
all prefix lengths; it does not license selecting loci after seeing outcomes.
Bits 1,2,4 represent ab|cd, ac|bd, ad|bc on sorted quartet labels.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from numbers import Integral
from typing import Callable, Iterable


def rational(value, name):
    if isinstance(value, bool) or isinstance(value, float):
        raise ValueError(f'{name}: use an integer, Fraction, or rational string')
    try:
        return F(value)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValueError(f'{name}: invalid rational') from exc


def positive_int(value, name):
    if isinstance(value, bool) or not isinstance(value, Integral) or value < 1:
        raise ValueError(f'{name}: positive integer required')
    return int(value)


def ceil_log2(x: F) -> int:
    if x < 1:
        raise ValueError('ceil_log2 input must be >=1')
    c = max(0, x.numerator.bit_length() - x.denominator.bit_length())
    if (1 << c) * x.denominator < x.numerator:
        c += 1
    return c


@dataclass(frozen=True)
class Contract:
    gap: F
    error: tuple[F, ...]
    noise: str = 'tv'
    legal_masks: tuple[int, ...] = (1, 2, 3, 4, 5, 6)

    def __post_init__(self):
        gap = rational(self.gap, 'gap')
        error = tuple(rational(x, 'error') for x in self.error)
        if not 0 < gap <= 1 or not error or any(not 0 <= x <= 1 for x in error):
            raise ValueError('gap in (0,1], at least one error bound in [0,1]')
        if self.noise not in ('tv', 'huber'):
            raise ValueError('noise must be tv or huber')
        if self.noise == 'huber' and any(x == 1 for x in error):
            raise ValueError('Huber contamination must be <1')
        masks = tuple(self.legal_masks)
        if not masks or len(set(masks)) != len(masks) or any(type(x) is not int or not 1 <= x <= 7 for x in masks):
            raise ValueError('legal_masks must be distinct nonempty masks in 1..7')
        object.__setattr__(self, 'gap', gap)
        object.__setattr__(self, 'error', error)
        object.__setattr__(self, 'legal_masks', masks)

    @property
    def rows(self):
        return len(self.error)

    def thresholds(self, row):
        e = self.error[row]
        if self.noise == 'tv':
            return 2 * e, self.gap - 2 * e
        return e, (1 - e) * self.gap - e

    @property
    def margin(self):
        return min(b - a for a, b in (self.thresholds(e) for e in range(self.rows)))


def radius_squared(n, rows, queries, delta, *, anytime=True):
    n = positive_int(n, 'n')
    rows = positive_int(rows, 'rows')
    queries = positive_int(queries, 'queries')
    d = rational(delta, 'delta')
    if not 0 < d < 1:
        raise ValueError('delta must be in (0,1)')
    multiplier = n * (n + 1) if anytime else 1
    # ln(x) <= ceil(log2(x)); confidence arithmetic never uses float log/sqrt.
    c = ceil_log2(F(6 * rows * queries * multiplier, 1) / d)
    return F(c, 2 * n)


def exceeds_twice_radius(distance: F, r2: F) -> bool:
    return distance > 0 and distance * distance > 4 * r2


@dataclass(frozen=True)
class Certificate:
    status: str
    candidates: tuple[int, ...]
    present: tuple[bool, bool, bool]
    absent: tuple[bool, bool, bool]
    row_counts: tuple[int, ...]

    @property
    def mask(self):
        return self.candidates[0] if self.status == 'CERTIFIED' else None


def certify(counts: Iterable[Iterable[int]], contract: Contract, queries, delta, *, anytime=True) -> Certificate:
    blocks = tuple(tuple(row) for row in counts)
    if len(blocks) != contract.rows:
        raise ValueError('one count vector required for each declared row')
    if any(len(row) != 3 or any(isinstance(x, bool) or not isinstance(x, Integral) or x < 0 for x in row) for row in blocks):
        raise ValueError('each count vector must have three nonnegative integers')
    # Validate risk even when every row is empty.
    radius_squared(1, contract.rows, queries, delta, anytime=anytime)
    totals = tuple(int(sum(row)) for row in blocks)
    present, absent = [], []
    for t in range(3):
        supports, excludes = [], []
        for e, row in enumerate(blocks):
            n = totals[e]
            if n == 0:
                supports.append(False)
                excludes.append(False)
                continue
            center = F(int(row[t] - min(row)), n)
            r2 = radius_squared(n, contract.rows, queries, delta, anytime=anytime)
            a, b = contract.thresholds(e)
            supports.append(exceeds_twice_radius(center - a, r2))
            excludes.append(exceeds_twice_radius(b - center, r2))
        present.append(any(supports))
        absent.append(all(excludes))
    p, a = tuple(present), tuple(absent)
    if any(p[t] and a[t] for t in range(3)):
        return Certificate('MODEL_INCOMPATIBLE', (), p, a, totals)
    candidates = tuple(mask for mask in contract.legal_masks
                       if all((not p[t] or mask & (1 << t)) and
                              (not a[t] or not mask & (1 << t)) for t in range(3)))
    status = 'MODEL_INCOMPATIBLE' if not candidates else 'CERTIFIED' if len(candidates) == 1 else 'INCONCLUSIVE'
    return Certificate(status, candidates, p, a, totals)


def sufficient_prefix(contract, queries, delta, *, anytime=True):
    """A checked sufficient length; no claim of optimality or minimality."""
    radius_squared(1, contract.rows, queries, delta, anytime=anytime)
    if contract.margin <= 0:
        return None
    n = 1
    while 16 * radius_squared(n, contract.rows, queries, delta, anytime=anytime) >= contract.margin ** 2:
        n *= 2
    return n


class RecoveryAbstention(RuntimeError):
    pass


class GuardedOracle:
    """Memoized complete-mask adapter; unresolved queries abort the decoder.

    The supplied counts callback chooses a declared prefix, possibly after
    examining earlier prefixes if anytime=True. It must not fabricate samples.
    External decoder computation still needs a sufficient termination guard.
    """
    def __init__(self, counts: Callable, contract: Contract, queries, delta, *, anytime=True, provider=certify):
        self.counts = counts
        self.contract = contract
        self.queries = positive_int(queries, 'queries')
        radius_squared(1, contract.rows, self.queries, delta, anytime=anytime)
        self.delta = rational(delta, 'delta')
        self.anytime = anytime
        if not callable(counts) or not callable(provider):
            raise ValueError('counts and provider must be callable')
        self.provider = provider
        self.cache = {}
        self.certificates = {}
        self.attempted = set()
        self.aborted = None

    def __call__(self, quartet):
        if self.aborted is not None:
            raise RecoveryAbstention(self.aborted)
        q = tuple(quartet)
        if len(q) != 4 or any(type(x) is not int or x < 0 for x in q) or tuple(sorted(set(q))) != q:
            raise ValueError('quartet must be four distinct sorted nonnegative integers')
        if q in self.cache:
            return self.cache[q]
        if len(self.attempted) >= self.queries:
            self.aborted = 'QUERY_LIMIT'
            raise RecoveryAbstention('QUERY_LIMIT')
        self.attempted.add(q)
        try:
            cert = self.provider(self.counts(q), self.contract, self.queries, self.delta, anytime=self.anytime)
        except Exception as exc:
            self.aborted = 'INPUT_ERROR'
            raise RecoveryAbstention('INPUT_ERROR') from exc
        self.certificates[q] = cert
        if cert.status != 'CERTIFIED':
            self.aborted = cert.status
            raise RecoveryAbstention(cert.status)
        if cert.mask not in self.contract.legal_masks or cert.candidates != (cert.mask,):
            self.aborted = 'INVALID_CERTIFICATE'
            raise RecoveryAbstention(self.aborted)
        self.cache[q] = cert.mask
        return cert.mask
