"""One bounded new-process assessment; no whole-domain inverse or new data."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import resource
import time

import joint_betting as jb
import covariance_betting as cb
from source_bridge import OriginalSourceBridge

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'covariance-points-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
          for name in ('joint_betting.py', 'source_bridge.py', 'covariance_betting.py', 'check_covariance_points.py')}
request_raw = (BASE / 'COVARIANCE-REQUEST.json').read_bytes()
request = json.loads(request_raw)
try:
    assert request['ridge'] == str(cb.RIDGE)
    assert request['burn_in_complete_loci'] == cb.BURN_IN
    assert request['refresh_complete_loci'] == cb.REFRESH
    assert request['new_separate_future_delta'] == '1/20'
    # NEW covariance code: exact inverse/predictability controls on a perfectly
    # dependent two-vector law, not a new original-source observation sample.
    covariance_controls = []
    point_box = tuple(jb.Interval.point(Q(2, 3)) for _ in range(9))
    for ones in (16, 32):
        average, inverse = cb.predictor([ones] * 9, [[ones] * 9 for _ in range(9)], 32)
        zero = cb.factor((0,) * 9, point_box, average, inverse)
        one = cb.factor((1,) * 9, point_box, average, inverse)
        assert zero.lo == zero.hi and one.lo == one.hi
        assert Q(1, 3) * zero.lo + Q(2, 3) * one.lo == 1
        assert Q(1, 2) <= zero.lo <= Q(3, 2) and Q(1, 2) <= one.lo <= Q(3, 2)
        if ones == 32:
            assert inverse == tuple(tuple(Q(16 if i == j else 0) for j in range(9)) for i in range(9))
        covariance_controls.append({'past_ones_out_of32': ones,
                                    'future_zero_factor': str(zero.lo), 'future_one_factor': str(one.lo),
                                    'dependent_law_expected_factor': '1'})
    old_request = json.loads((BASE / 'TIGHT-REPLAY-REQUEST.json').read_text())
    assert old_request['dataset_sha256'] == request['dataset_sha256']
    assert old_request['selection_sha256'] == request['selection_sha256']
    archive = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    rows, extraction = jb.literal_rows(archive / 'declared-model/DATASET.json', request['dataset_sha256'],
                                      request['expected_complete_loci'], request['selection_sha256'], archive / 'integration_core.py')
    source0 = {key: list(pair) for key, pair in old_request['original_known_synthetic_source_point'].items()}
    source1 = {key: list(pair) for key, pair in source0.items()}; source1['rA'] = ['13/10', '13/10']
    bridge = OriginalSourceBridge(ROOT)
    means = [bridge.enclose(source) for source in (source0, source1)]
    outputs = [cb.replay(rows, box, request['new_separate_future_delta'], request['precision_fractional_bits'],
                         request['maximum_arithmetic_bits']) for box in means]
    bridge.close()
    limited = cb.replay(rows, means[0], request['new_separate_future_delta'],
                        request['precision_fractional_bits'], max_bits=16)
    assert limited['status'] == 'UNKNOWN' and limited['arithmetic_refusal'] == 'ARITHMETIC_BITS'
    both_retained = all(row['status'] == 'ALL_PREFIX_MEAN_BOX_MEMBERSHIP_CERTIFIED' for row in outputs)
    result = {'schema': 'separate-covariance-original-source-point-assessment-v1', 'status': 'PASS',
              'source_sha256': hashes, 'request_sha256': hashlib.sha256(request_raw).hexdigest(),
              'covariance_inverse_and_dependent_factor_controls': covariance_controls,
              'complete_original_extraction': extraction, 'source_parameter_points': [source0, source1],
              'source_forward_mean_boxes': means, 'new_process_receivers': outputs,
              'changed_budget_refusal': limited, 'normalized_source_rA_separation': '3/55',
              'both_sources_certified_retained_in_new_region': both_retained,
              'new_region_width_target_obstructed_by_this_pair': both_retained,
              'new_process_separate_future_delta': request['new_separate_future_delta'],
              'intersected_with_old_process': False, 'actual_source_enclosure_calls': 2,
              'new_source_observations_generated': False, 'whole_domain_inverse_run': False,
              'historical_predeclaration_established': False, 'finite_rng_certified': False,
              'data_confidence_certificate_issued': False, 'lean_kernel_checked': False,
              'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'source_point_outcomes': [row['status'] for row in outputs],
                      'new_region_retains_separated_pair': both_retained,
                      'new_separate_future_delta': request['new_separate_future_delta'],
                      'actual_source_enclosure_calls': 2}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': hashes,
                                                   'request_sha256': hashlib.sha256(request_raw).hexdigest(),
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
