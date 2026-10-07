"""Fixed-precision lower capital for the published original joint process."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import joint_betting as jb

ORIGINAL_BETTING_SHA = '2552515f21e9ef6c963897fb3022cd75aa5043f2e58c8daa1b3929c60f0995ea'


def downward(value, bits):
    scale = 1 << bits
    return Q((value.numerator * scale) // value.denominator, scale)


def replay(rows, shifted_mean_box, plan, delta='1/20', precision_bits=96, max_bits=16384):
    if hashlib.sha256(Path(jb.__file__).read_bytes()).hexdigest() != ORIGINAL_BETTING_SHA:
        raise jb.Invalid('original betting source identity changed')
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
    lower_capital = [Q(1) for _ in bets]
    totals, squares = [Q(0) for _ in bets], [Q(0) for _ in bets]
    best, final, threshold = Q(1), Q(1), 1 / allowance
    processed, crossing, refusal, max_stored_bits = 0, None, None, 1
    for i, row in enumerate(rows):
        values = [sum((coefficient * value for coefficient, value in zip(d, row)), Q(0))
                  for _, d in bets]
        factors = [jb.factor(value, projection, total, sq, i).lo
                   for value, projection, total, sq in zip(values, projections, totals, squares)]
        next_totals = [s + v for s, v in zip(totals, values)]
        next_squares = [s + v * v for s, v in zip(squares, values)]
        unrounded = [capital * factor for capital, factor in zip(lower_capital, factors)]
        intermediate = factors + next_totals + next_squares + unrounded
        if any(max(abs(v.numerator).bit_length(), v.denominator.bit_length()) > max_bits for v in intermediate):
            refusal = 'ARITHMETIC_BITS'; break
        proposed = [downward(value, precision_bits) for value in unrounded]
        mixture = sum((w * capital for (w, _), capital in zip(bets, proposed)), Q(0))
        sizes = [max(abs(v.numerator).bit_length(), v.denominator.bit_length())
                 for v in proposed + [mixture]]
        if max(sizes) > max_bits:
            refusal = 'ARITHMETIC_BITS'; break
        lower_capital, totals, squares = proposed, next_totals, next_squares
        processed = i + 1
        final, best = mixture, max(best, mixture)
        max_stored_bits = max(max_stored_bits, max(sizes))
        if mixture >= threshold:
            crossing = processed; break
    return {'schema': 'same-map-downward-capital-mean-box-receiver-v1',
            'model': jb.MODEL, 'observation_map': jb.MAP,
            'quantity': 'shifted_bernoulli_character_mean',
            'status': 'CONDITIONAL_MEAN_BOX_EXCLUDED' if crossing else 'UNKNOWN',
            'loci_supplied': len(rows), 'prefix_processed': processed,
            'exclusion_prefix': crossing, 'arithmetic_refusal': refusal,
            'delta': str(allowance), 'threshold': str(threshold),
            'precision_fractional_bits': precision_bits, 'arithmetic_max_bits': max_bits,
            'maximum_stored_capital_or_mixture_bits': max_stored_bits,
            'best_prefix_mixture_lower': str(best), 'final_mixture_lower': str(final),
            'mean_box_sha256': hashlib.sha256(jb.canonical(shifted_mean_box)).hexdigest(),
            'predeclared_strategy_plan_sha256': hashlib.sha256(jb.canonical(plan)).hexdigest(),
            'literal_rows_sha256': hashlib.sha256(jb.canonical(rows)).hexdigest(),
            'original_betting_source_sha256': ORIGINAL_BETTING_SHA,
            'conditional_coverage_scope': 'same original joint all-prefix process; capital rounded only downward',
            'within_locus_independence_assumed': False,
            'scientific_admission_verified': False,
            'data_confidence_certificate_issued': False,
            'physical_source_box_excluded': False,
            'parameter_accuracy_or_witness_certified': False,
            'lean_kernel_checked': False}
