"""Conservative all-prefix upper capital for exact source-point membership."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import joint_betting as jb
import tight_factor as tf

TIGHT_FACTOR_SHA = 'daf95ef0ab80f7271c4b4f99b0b6eac42ffa650baebf86b35b6b3d31bc309a5a'
ORIGINAL_BETTING_SHA = '2552515f21e9ef6c963897fb3022cd75aa5043f2e58c8daa1b3929c60f0995ea'


def upward(value, bits):
    scale = 1 << bits
    return Q(-((-value.numerator * scale) // value.denominator), scale)


def replay(rows, shifted_mean_box, plan, delta='1/10', precision_bits=96, max_bits=16384):
    for module, expected in ((jb, ORIGINAL_BETTING_SHA), (tf, TIGHT_FACTOR_SHA)):
        if hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest() != expected:
            raise jb.Invalid('accepted betting/factor source identity changed')
    if not isinstance(rows, tuple) or not 1 <= len(rows) <= jb.MAX_LOCI:
        raise jb.Invalid('complete 1..100000 literal row tuple required')
    if any(not isinstance(row, tuple) or len(row) != 9 or
           any(type(value) is not int or value not in (0, 1) for value in row) for row in rows):
        raise jb.Invalid('literal Bernoulli nine-vector required')
    if type(precision_bits) is not int or not 16 <= precision_bits <= 256:
        raise jb.Invalid('16..256 fractional precision bits required')
    if type(max_bits) is not int or not 16 <= max_bits <= 65536:
        raise jb.Invalid('16..65536 arithmetic bit cap required')
    allowance = jb.rational(delta)
    if not 0 < allowance < 1:
        raise jb.Invalid('delta outside (0,1)')
    box, bets = jb.mean_box(shifted_mean_box), jb.strategies(plan)
    projections = [jb.project_box(d, box) for _, d in bets]
    capital = [Q(1) for _ in bets]
    totals, squares = [Q(0) for _ in bets], [Q(0) for _ in bets]
    threshold, largest = 1 / allowance, Q(1)
    processed, refusal, inconclusive_prefix, max_stored = 0, None, None, 1
    for i, row in enumerate(rows):
        values = [sum((coefficient * value for coefficient, value in zip(d, row)), Q(0))
                  for _, d in bets]
        factors = [tf.factor(value, projection, total, sq, i).hi
                   for value, projection, total, sq in zip(values, projections, totals, squares)]
        unrounded = [upper * factor for upper, factor in zip(capital, factors)]
        next_totals = [s + v for s, v in zip(totals, values)]
        next_squares = [s + v * v for s, v in zip(squares, values)]
        numbers = factors + unrounded + next_totals + next_squares
        if any(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) > max_bits for v in numbers):
            refusal = 'ARITHMETIC_BITS'; break
        proposed = [upward(value, precision_bits) for value in unrounded]
        mixture = sum((w * upper for (w, _), upper in zip(bets, proposed)), Q(0))
        sizes = [max(abs(v.numerator).bit_length(), v.denominator.bit_length()) for v in proposed + [mixture]]
        if max(sizes) > max_bits:
            refusal = 'ARITHMETIC_BITS'; break
        capital, totals, squares = proposed, next_totals, next_squares
        processed = i + 1
        largest = max(largest, mixture)
        max_stored = max(max_stored, max(sizes))
        if mixture >= threshold:
            inconclusive_prefix = processed; break
    certified = processed == len(rows) and not refusal and not inconclusive_prefix and largest < threshold
    return {'schema': 'same-process-all-prefix-upper-mean-box-membership-v1',
            'model': jb.MODEL, 'observation_map': jb.MAP,
            'quantity': 'shifted_bernoulli_character_mean',
            'status': 'ALL_PREFIX_MEAN_BOX_MEMBERSHIP_CERTIFIED' if certified else 'UNKNOWN',
            'loci_supplied': len(rows), 'prefix_processed': processed,
            'maximum_prefix_mixture_upper': str(largest), 'threshold': str(threshold),
            'delta': str(allowance), 'precision_fractional_bits': precision_bits,
            'arithmetic_max_bits': max_bits, 'maximum_stored_capital_or_mixture_bits': max_stored,
            'arithmetic_refusal': refusal, 'inconclusive_prefix': inconclusive_prefix,
            'all_means_in_box_satisfy_same_process_all_prefix_constraints': certified,
            'mean_box_sha256': hashlib.sha256(jb.canonical(shifted_mean_box)).hexdigest(),
            'predeclared_strategy_plan_sha256': hashlib.sha256(jb.canonical(plan)).hexdigest(),
            'literal_rows_sha256': hashlib.sha256(jb.canonical(rows)).hexdigest(),
            'accepted_dependency_sha256': {'joint_betting.py': ORIGINAL_BETTING_SHA, 'tight_factor.py': TIGHT_FACTOR_SHA},
            'historical_plan_predeclaration_established': False,
            'finite_rng_certified': False, 'scientific_admission_verified': False,
            'data_confidence_certificate_issued': False,
            'old_numerical_inverse_witness_certified': False,
            'lean_kernel_checked': False}
