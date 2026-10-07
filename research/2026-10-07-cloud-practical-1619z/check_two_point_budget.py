"""Bounded exact arithmetic on saved authenticated mean enclosures only.

No observation extraction, source-provider call, replay, sample or inverse run.
The output is a prospective two-point sufficient budget, not a data certificate.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import json
import resource
import time

BASE = Path(__file__).resolve().parent
OUT = BASE / 'two-point-budget-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
STARTED = time.time()
INPUT_SHA = '8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931'
FEATURES = ('AC1', 'AC2', 'CC1', 'BC1', 'BC2', 'AB1', 'AB2', 'AA1', 'BB1')
SOURCE_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def exp_partial(q, degree):
    return sum((q**k / factorial(k) for k in range(degree + 1)), Q(0))


try:
    raw = (BASE / 'covariance-points-attempt1/RESULT.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA
    receipt = json.loads(raw)
    assert receipt['status'] == 'PASS'
    assert tuple(receipt['complete_original_extraction']['feature_order']) == FEATURES
    assert receipt['actual_source_enclosure_calls'] == 2
    assert receipt['source_sha256']['source_bridge.py'] == (
        '1b45de0aa059bbcda435e4656b7f8869b889a882900071021652ff0c16db8d2f')
    assert receipt['new_process_receivers'][0]['model'] == 'fixed-six-copy-clock-jc-nine-v1'
    sources = receipt['source_parameter_points']
    assert sources[0]['rA'] == ['1', '1'] and sources[1]['rA'] == ['13/10', '13/10']
    assert {key: value for key, value in sources[0].items() if key != 'rA'} == {
        key: value for key, value in sources[1].items() if key != 'rA'}
    boxes = receipt['source_forward_mean_boxes']
    assert len(boxes) == 2 and all(set(box) == set(FEATURES) for box in boxes)
    parsed = [{key: tuple(map(Q, box[key])) for key in FEATURES} for box in boxes]
    assert all(0 <= lo <= hi <= 1 for box in parsed for lo, hi in box.values())
    gaps = {}
    for key in FEATURES:
        a, b = parsed[0][key]
        c, d = parsed[1][key]
        gaps[key] = {'absolute_gap_lower': str(max(Q(0), c - b, a - d)),
                     'absolute_gap_upper': str(max(abs(c - b), abs(d - a)))}
    selected = 'AA1'
    a, b = parsed[0][selected]
    c, d = parsed[1][selected]
    gap = c - b
    assert gap > 0
    assert all(gap > Q(gaps[key]['absolute_gap_upper']) for key in FEATURES if key != selected)
    threshold = (b + c) / 2
    assert threshold - b == c - threshold == gap / 2
    risk = Q(1, 20)
    # Lower exp(q_upper) bound is its positive finite series.
    q_upper = Q(149787, 50000)
    degree = 20
    exp_q_upper_lower = exp_partial(q_upper, degree)
    assert exp_q_upper_lower > 1 / risk
    # For k >= degree+1, subsequent term ratios are at most q/(degree+2).
    q_lower = Q(748933, 250000)
    assert 0 < q_lower < degree + 2
    exp_q_lower_upper = (exp_partial(q_lower, degree)
                         + (q_lower**(degree + 1) / factorial(degree + 1))
                         / (1 - q_lower / Q(degree + 2)))
    assert exp_q_lower_upper < 1 / risk
    required = 2 * q_upper / gap**2
    sufficient_n = -(-required.numerator // required.denominator)
    exponent = Q(sufficient_n) * gap**2 / 2
    archived_comparison_n = receipt['complete_original_extraction']['m']
    archived_comparison_exponent = Q(archived_comparison_n) * gap**2 / 2
    assert sufficient_n == 69134 and archived_comparison_n == 1024
    assert exponent >= q_upper
    assert Q(sufficient_n - 1) < required <= sufficient_n
    assert archived_comparison_exponent < q_lower
    result = {
        'schema': 'original-source-two-point-prospective-hoeffding-budget-v1',
        'status': 'PASS', 'check_source_sha256': SOURCE_SHA,
        'authenticated_saved_source_enclosure_receipt_sha256': INPUT_SHA,
        'source_parameter_points': sources, 'source_forward_mean_boxes': boxes,
        'feature_gap_enclosures': gaps, 'fixed_selected_feature': selected,
        'largest_actual_scalar_feature_gap_certified': True,
        'certified_selected_gap_lower': str(gap),
        'selected_gap_upper': gaps[selected]['absolute_gap_upper'],
        'fixed_decision_threshold': str(threshold),
        'decision_rule': 'choose source 1 iff fixed-N AA1 average >= threshold; otherwise source 0',
        'future_worst_source_error_allowance': str(risk),
        'future_risk_definition': 'maximum of the two conditional source misclassification probabilities',
        'hoeffding_error_bound': 'exp(-N * certified_selected_gap_lower^2 / 2)',
        'log_inverse_risk_lower': str(q_lower), 'log_inverse_risk_upper': str(q_upper),
        'exp_series_degree': degree,
        'exp_log_upper_partial_sum': str(exp_q_upper_lower),
        'exp_log_lower_geometric_tail_upper': str(exp_q_lower_upper),
        'rational_required_n_upper': str(required), 'certified_sufficient_n': sufficient_n,
        'certified_exponent_at_sufficient_n': str(exponent),
        'archived_locus_count_for_comparison_only': archived_comparison_n,
        'exponent_at_archived_count_for_comparison_only': str(archived_comparison_exponent),
        'sufficient_n_over_archived_count': str(Q(sufficient_n, archived_comparison_n)),
        'archived_count_certified_by_this_sufficient_hoeffding_bound': False,
        'sample_size_necessity_or_information_lower_bound_claimed': False,
        'admitted_fresh_iid_complete_loci_required': True,
        'fixed_feature_threshold_and_n_before_future_observations_required': True,
        'within_locus_feature_independence_required': False,
        'new_future_risk_separate_from_previous_processes': True,
        'retrospective_confidence_or_scientific_admission_issued': False,
        'future_sampling_performed': False, 'new_observations_generated': False,
        'source_provider_calls_in_this_check': 0, 'data_extraction_or_replay_performed': False,
        'full_domain_localization_claimed': False, 'lean_kernel_checked': False,
        'started_unix': STARTED, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(canonical(result))
    print(json.dumps({'status': 'PASS', 'fixed_feature': selected,
                      'certified_sufficient_n': sufficient_n, 'future_risk': str(risk),
                      'source_provider_calls': 0, 'data_replay': False}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(canonical({'status': 'FAIL', 'error': repr(error),
                                                 'check_source_sha256': SOURCE_SHA,
                                                 'input_sha256': INPUT_SHA,
                                                 'started_unix': STARTED, 'ended_unix': time.time()}))
    raise
