"""New predictable joint-vector process, using only preceding locus moments.

Its separate future confidence budget cannot be silently intersected with the
older process. Source/extraction/admission contracts are otherwise unchanged.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import joint_betting as jb

ORIGINAL_BETTING_SHA = '2552515f21e9ef6c963897fb3022cd75aa5043f2e58c8daa1b3929c60f0995ea'
RIDGE = Q(1, 16)
BURN_IN = 32
REFRESH = 32


class ResourceStop(ArithmeticError):
    pass


def guard(numbers, max_bits):
    if any(max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > max_bits
           for value in numbers):
        raise ResourceStop('ARITHMETIC_BITS')


def inverse(matrix, max_bits=16384):
    n = len(matrix)
    if n != 9 or any(len(row) != 9 for row in matrix):
        raise jb.Invalid('nine-coordinate covariance required')
    rows = [list(row) + [Q(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for k in range(n):
        pivot = rows[k][k]
        if pivot <= 0:
            raise jb.Invalid('positive covariance-ridge pivot required')
        rows[k] = [value / pivot for value in rows[k]]
        guard(rows[k], max_bits)
        for i in range(n):
            if i != k:
                coefficient = rows[i][k]
                rows[i] = [a - coefficient * b for a, b in zip(rows[i], rows[k])]
                guard(rows[i], max_bits)
    answer = tuple(tuple(row[n:]) for row in rows)
    for i in range(n):
        for j in range(n):
            if sum((matrix[i][k] * answer[k][j] for k in range(n)), Q(0)) != Q(i == j):
                raise jb.Invalid('exact covariance inverse identity failed')
    return answer


def predictor(sums, joints, n, max_bits=16384):
    if n < 1:
        raise jb.Invalid('past nonempty prefix required')
    average = tuple(Q(value, n) for value in sums)
    covariance = tuple(tuple(Q(joints[i][j], n) - average[i] * average[j]
                             + (RIDGE if i == j else 0) for j in range(9)) for i in range(9))
    return average, inverse(covariance, max_bits)


def absolute_range(interval):
    lower = 0 if interval.lo <= 0 <= interval.hi else min(abs(interval.lo), abs(interval.hi))
    return jb.Interval(Q(lower), max(abs(interval.lo), abs(interval.hi)))


def divide_positive(numerator, denominator):
    if denominator.lo <= 0:
        raise jb.Invalid('positive stake normalization required')
    values = [a / b for a in (numerator.lo, numerator.hi) for b in (denominator.lo, denominator.hi)]
    return jb.Interval(min(values), max(values))


def factor(row, box, average, inverse_covariance, max_bits=16384):
    residuals = [jb.Interval(a - interval.hi, a - interval.lo) for a, interval in zip(average, box)]
    raw = []
    for coefficients in inverse_covariance:
        value = jb.Interval.point(0)
        for coefficient, residual in zip(coefficients, residuals):
            value = value + jb.Interval.point(coefficient) * residual
        raw.append(value)
    norm = jb.Interval.point(0)
    for value in raw:
        norm = norm + absolute_range(value)
    denominator = jb.Interval(max(Q(1), 2 * norm.lo), max(Q(1), 2 * norm.hi))
    stakes = [divide_positive(value, denominator) for value in raw]
    bound = jb.Interval.point(1)
    for stake, observed, interval in zip(stakes, row, box):
        bound = bound + stake * jb.Interval(Q(observed) - interval.hi, Q(observed) - interval.lo)
    result = jb.Interval(max(Q(1, 2), bound.lo), min(Q(3, 2), bound.hi))
    guard([endpoint for value in raw + stakes + [denominator, result]
           for endpoint in (value.lo, value.hi)], max_bits)
    return result


def down(value, bits):
    scale = 1 << bits
    return Q((value.numerator * scale) // value.denominator, scale)


def up(value, bits):
    scale = 1 << bits
    return Q(-((-value.numerator * scale) // value.denominator), scale)


def replay(rows, shifted_mean_box, delta='1/20', precision_bits=96, max_bits=16384):
    if hashlib.sha256(Path(jb.__file__).read_bytes()).hexdigest() != ORIGINAL_BETTING_SHA:
        raise jb.Invalid('original literal/betting interface identity changed')
    if not isinstance(rows, tuple) or not 1 <= len(rows) <= jb.MAX_LOCI or any(
            not isinstance(row, tuple) or len(row) != 9 or any(type(x) is not int or x not in (0, 1) for x in row)
            for row in rows):
        raise jb.Invalid('complete literal nine-vector tuple required')
    if type(precision_bits) is not int or not 16 <= precision_bits <= 256:
        raise jb.Invalid('16..256 fractional precision bits required')
    if type(max_bits) is not int or not 16 <= max_bits <= 65536:
        raise jb.Invalid('16..65536 arithmetic bit cap required')
    allowance = jb.rational(delta)
    if not 0 < allowance < 1:
        raise jb.Invalid('delta outside (0,1)')
    box = jb.mean_box(shifted_mean_box)
    sums, joints = [0] * 9, [[0] * 9 for _ in range(9)]
    average, inv = None, None
    lower, upper, best_lower, best_upper = Q(1), Q(1), Q(1), Q(1)
    processed, refusal, exclusion, refreshes = 0, None, None, []
    try:
        for i, row in enumerate(rows):
            if i >= BURN_IN and i % REFRESH == 0:
                average, inv = predictor(sums, joints, i, max_bits)
                refreshes.append(i)
            enclosure = jb.Interval.point(1) if average is None else factor(row, box, average, inv, max_bits)
            proposed_lower = lower * enclosure.lo
            proposed_upper = upper * enclosure.hi
            guard([proposed_lower, proposed_upper], max_bits)
            proposed_lower = down(proposed_lower, precision_bits)
            proposed_upper = up(proposed_upper, precision_bits)
            guard([proposed_lower, proposed_upper], max_bits)
            lower, upper = proposed_lower, proposed_upper
            best_lower, best_upper = max(best_lower, lower), max(best_upper, upper)
            processed = i + 1
            for j in range(9):
                sums[j] += row[j]
                for k in range(9):
                    joints[j][k] += row[j] * row[k]
            if lower >= 1 / allowance:
                exclusion = processed; break
            if upper >= 1 / allowance:
                break  # Not an exclusion; full-stream membership is unproved.
    except ResourceStop:
        refusal = 'ARITHMETIC_BITS'
    membership = processed == len(rows) and not refusal and best_upper < 1 / allowance
    status = ('CONDITIONAL_MEAN_BOX_EXCLUDED' if exclusion else
              'ALL_PREFIX_MEAN_BOX_MEMBERSHIP_CERTIFIED' if membership else 'UNKNOWN')
    return {'schema': 'ridge-covariance-predictable-nine-vector-receiver-v1',
            'model': jb.MODEL, 'observation_map': jb.MAP,
            'quantity': 'shifted_bernoulli_character_mean', 'status': status,
            'loci_supplied': len(rows), 'prefix_processed': processed, 'exclusion_prefix': exclusion,
            'best_prefix_capital_lower': str(best_lower), 'maximum_prefix_capital_upper': str(best_upper),
            'delta': str(allowance), 'threshold': str(1 / allowance),
            'ridge': str(RIDGE), 'burn_in_complete_loci': BURN_IN, 'refresh_complete_loci': REFRESH,
            'matrix_refresh_past_prefixes': refreshes,
            'precision_fractional_bits': precision_bits, 'arithmetic_max_bits': max_bits,
            'arithmetic_refusal': refusal,
            'mean_box_sha256': hashlib.sha256(jb.canonical(shifted_mean_box)).hexdigest(),
            'literal_rows_sha256': hashlib.sha256(jb.canonical(rows)).hexdigest(),
            'new_process_separate_future_budget': True,
            'intersected_with_previous_process': False,
            'within_locus_independence_assumed': False,
            'empirical_covariance_is_claimed_population_bound': False,
            'historical_plan_predeclaration_established': False,
            'finite_rng_certified': False, 'data_confidence_certificate_issued': False,
            'scientific_admission_verified': False,
            'parameter_width_or_old_inverse_journal_certified': False,
            'lean_kernel_checked': False}
