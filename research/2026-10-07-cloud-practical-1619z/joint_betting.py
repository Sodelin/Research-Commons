"""Exact same-map joint betting research receiver; never issues admission.

The nine-vector is the literal old Bernoulli character vector. Complete loci
are the independent units. Mean-box exclusions are conditional statistical
constraints, not a source witness, an inverse journal or an accuracy result.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import importlib.util
import json
import re

FEATURES = ('AC1', 'AC2', 'CC1', 'BC1', 'BC2', 'AB1', 'AB2', 'AA1', 'BB1')
MODEL = 'fixed-six-copy-clock-jc-nine-v1'
MAP = 'complete-six-copy-two-site-character-vector-v1'
CORE_SHA = 'f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e'
MAX_LOCI = 100000
MAX_STRATEGIES = 32


class Invalid(ValueError):
    pass


def rational(value):
    if not isinstance(value, str) or len(value) > 160 or not re.fullmatch(r'-?[0-9]+(?:/[0-9]+)?', value):
        raise Invalid('bounded rational string required')
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise Invalid('rational syntax') from error
    if max(abs(result.numerator).bit_length(), result.denominator.bit_length()) > 256:
        raise Invalid('256-bit input cap')
    return result


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def literal_rows(data_path, data_sha, expected_loci, selection_sha, core_path):
    """Authenticate the old extractor and reuse its complete input validation."""
    path = Path(core_path)
    if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != CORE_SHA:
        raise Invalid('literal extractor identity changed')
    spec = importlib.util.spec_from_file_location('_cloud_joint_literal_core', path)
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    if tuple(core.FEATURES) != FEATURES or core.MODEL != MODEL:
        raise Invalid('literal feature interface changed')
    data = core.read(data_path, data_sha)
    extraction = core.extract(data, expected_loci, selection_sha)
    rows = []
    for locus in data['loci']:
        row = []
        for feature in FEATURES:
            a, b = core.PAIRS[feature[:2]]
            parity = 1
            for site in range(int(feature[-1])):
                parity *= core.CHI[locus['calls'][a][site]] * core.CHI[locus['calls'][b][site]]
            row.append((1 + parity) // 2)
        rows.append(tuple(row))
    if any(sum(row[j] for row in rows) != extraction['counts'][name]
           for j, name in enumerate(FEATURES)):
        raise Invalid('per-locus vector/count mismatch')
    if hashlib.sha256(path.read_bytes()).hexdigest() != CORE_SHA:
        raise Invalid('literal extractor identity changed during extraction')
    return tuple(rows), extraction


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        if self.lo > self.hi:
            raise Invalid('reversed interval')

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __mul__(self, other):
        values = (self.lo * other.lo, self.lo * other.hi,
                  self.hi * other.lo, self.hi * other.hi)
        return Interval(min(values), max(values))

    @staticmethod
    def point(value):
        return Interval(Q(value), Q(value))


def mean_box(record):
    if not isinstance(record, dict) or set(record) != set(FEATURES):
        raise Invalid('exact nine shifted-mean keys required')
    result = []
    for name in FEATURES:
        pair = record[name]
        if not isinstance(pair, list) or len(pair) != 2:
            raise Invalid('two rational endpoints required')
        lo, hi = map(rational, pair)
        if not 0 <= lo <= hi <= 1:
            raise Invalid('shifted-mean box outside [0,1]')
        result.append(Interval(lo, hi))
    return tuple(result)


def strategies(record):
    """Directions and weights are frozen before observation, never optimized here."""
    if not isinstance(record, list) or not 1 <= len(record) <= MAX_STRATEGIES:
        raise Invalid('1..32 predeclared strategies required')
    result = []
    for row in record:
        if not isinstance(row, dict) or set(row) != {'weight', 'direction'}:
            raise Invalid('strategy schema')
        if not isinstance(row['direction'], list) or len(row['direction']) != len(FEATURES):
            raise Invalid('nine direction coefficients required')
        direction = tuple(map(rational, row['direction']))
        weight = rational(row['weight'])
        if not weight > 0 or not 0 < sum(map(abs, direction)) <= 1:
            raise Invalid('positive weight and direction l1 in (0,1] required')
        result.append((weight, direction))
    if sum((w for w, _ in result), Q(0)) != 1:
        raise Invalid('mixture weights must sum exactly to one')
    return tuple(result)


def project_box(direction, box):
    result = Interval.point(0)
    for coefficient, entry in zip(direction, box):
        result = result + Interval.point(coefficient) * entry
    return result


def clip(value):
    return max(Q(-1, 2), min(Q(1, 2), value))


def factor(projected_value, projected_box, total, squares, n):
    """Candidate-dependent plug-in stake uses only the n preceding loci.

    The variance estimate only chooses a predictable bet. Coverage makes no
    claim that this estimate is an upper bound on the actual variance.
    """
    if not n:
        return Interval.point(1)
    average = total / n
    variance = squares / n - average * average
    if variance < 0:
        raise Invalid('negative exact empirical variance')
    denominator = variance + Q(1, 16)
    stake = Interval(clip((average - projected_box.hi) / denominator),
                     clip((average - projected_box.lo) / denominator))
    residual = Interval(projected_value - projected_box.hi,
                        projected_value - projected_box.lo)
    # Dependency loss is harmless for an outer enclosure. Intersect with the
    # independently proved [1/2,3/2] universal factor range before products.
    inclusion = Interval.point(1) + stake * residual
    return Interval(max(Q(1, 2), inclusion.lo), min(Q(3, 2), inclusion.hi))


def replay(rows, shifted_mean_box, plan, delta='1/20', max_bits=16384):
    """Check all-prefix lower evidence; no candidate/source existence claim.

    A bit-budget stop preserves earlier evidence, and an unsupported box stays
    UNKNOWN. Every row is validated, even if arithmetic stops on an early row.
    """
    if not isinstance(rows, tuple) or not 1 <= len(rows) <= MAX_LOCI:
        raise Invalid('complete validated 1..100000 literal row tuple required')
    if any(not isinstance(row, tuple) or len(row) != 9 or
           any(type(value) is not int or value not in (0, 1) for value in row)
           for row in rows):
        raise Invalid('literal Bernoulli nine-vector required')
    allowance = rational(delta)
    if not 0 < allowance < 1:
        raise Invalid('delta outside (0,1)')
    if type(max_bits) is not int or not 16 <= max_bits <= 65536:
        raise Invalid('16..65536 arithmetic bit cap required')
    box, bets = mean_box(shifted_mean_box), strategies(plan)
    projections = [project_box(d, box) for _, d in bets]
    wealth = [Interval.point(1) for _ in bets]
    totals, squares = [Q(0) for _ in bets], [Q(0) for _ in bets]
    threshold, best = 1 / allowance, Q(1)
    processed, crossing, refusal = 0, None, None
    for i, row in enumerate(rows):
        values = [sum((coefficient * value for coefficient, value in zip(d, row)), Q(0))
                  for _, d in bets]
        proposed = [old * factor(v, p, total, sq, i)
                    for old, v, p, total, sq in zip(wealth, values, projections, totals, squares)]
        mixture = sum((w * value.lo for (w, _), value in zip(bets, proposed)), Q(0))
        numbers = [mixture] + [endpoint for v in proposed for endpoint in (v.lo, v.hi)]
        if any(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_bits for q in numbers):
            refusal = 'ARITHMETIC_BITS'; break
        wealth = proposed
        totals = [s + v for s, v in zip(totals, values)]
        squares = [s + v * v for s, v in zip(squares, values)]
        processed = i + 1
        best = max(best, mixture)
        if mixture >= threshold:
            crossing = processed; break
    return {'schema': 'same-map-joint-betting-mean-box-receiver-v1',
            'model': MODEL, 'observation_map': MAP,
            'quantity': 'shifted_bernoulli_character_mean',
            'status': 'CONDITIONAL_MEAN_BOX_EXCLUDED' if crossing else 'UNKNOWN',
            'loci_supplied': len(rows), 'prefix_processed': processed,
            'exclusion_prefix': crossing, 'arithmetic_refusal': refusal,
            'delta': str(allowance), 'threshold': str(threshold),
            'best_prefix_mixture_lower': str(best),
            'mean_box_sha256': hashlib.sha256(canonical(shifted_mean_box)).hexdigest(),
            'predeclared_strategy_plan_sha256': hashlib.sha256(canonical(plan)).hexdigest(),
            'literal_rows_sha256': hashlib.sha256(canonical(rows)).hexdigest(),
            'arithmetic_max_bits': max_bits,
            'conditional_coverage_scope': 'one all-prefix event at the true nine-mean vector; original complete-locus conditional mean law required',
            'within_locus_independence_assumed': False,
            'variance_estimate_is_coverage_bound': False,
            'scientific_admission_verified': False,
            'data_confidence_certificate_issued': False,
            'physical_source_box_excluded': False,
            'parameter_accuracy_or_witness_certified': False,
            'lean_kernel_checked': False}
