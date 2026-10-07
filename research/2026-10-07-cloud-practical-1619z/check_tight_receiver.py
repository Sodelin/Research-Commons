"""Bounded saved-observation source-box replay; never samples or fits data."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import resource
import time

import joint_betting as jb
import rounded_betting as old
import tight_factor as tf
import tight_rounded_betting as new
from source_bridge import OriginalSourceBridge

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'tight-receiver-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
source_hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                 for name in ('joint_betting.py', 'rounded_betting.py', 'tight_factor.py',
                              'tight_rounded_betting.py', 'source_bridge.py', 'check_tight_receiver.py')}
request_raw = (BASE / 'TIGHT-REPLAY-REQUEST.json').read_bytes()
request = json.loads(request_raw)
try:
    # New mathematical change only: exact extrema must dominate the old
    # dependency-losing interval and contain every tested candidate factor.
    extrema_checks, candidate_checks, strict_improvements = 0, 0, 0
    for z, average, variance in product((Q(-1, 2), Q(0), Q(1, 2)),
                                        (Q(-1, 2), Q(0), Q(1, 2)), (Q(0), Q(1, 8))):
        for left, right in ((Q(-1, 2), Q(1, 2)), (Q(-1, 4), Q(1, 4)),
                            (Q(0), Q(1, 2)), (Q(-1, 2), Q(0))):
            bound = jb.Interval(left, right)
            total, squares = 2 * average, 2 * (variance + average * average)
            exact = tf.factor(z, bound, total, squares, 2)
            previous = jb.factor(z, bound, total, squares, 2)
            assert previous.lo <= exact.lo <= exact.hi <= previous.hi
            strict_improvements += exact.lo > previous.lo
            for numerator in range(13):
                p = left + (right - left) * Q(numerator, 12)
                direct = 1 + jb.clip((average - p) / (variance + Q(1, 16))) * (z - p)
                assert exact.lo <= direct <= exact.hi
                candidate_checks += 1
            extrema_checks += 1
    # The frozen plan is canonical from the old fixed feature order, no search.
    jb.strategies(request['plan'])
    archive = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    old_request = archive / 'composition-attempt1/ANALYSIS-REQUEST.json'
    assert hashlib.sha256(old_request.read_bytes()).hexdigest() == request['old_analysis_request_sha256']
    rows, extraction = jb.literal_rows(archive / 'declared-model/DATASET.json', request['dataset_sha256'],
                                      request['expected_loci'], request['selection_sha256'], archive / 'integration_core.py')
    expected_counts = (623, 550, 794, 661, 578, 660, 594, 704, 730)
    assert tuple(extraction['counts'][key] for key in jb.FEATURES) == expected_counts
    bridge = OriginalSourceBridge(ROOT)
    mean_boxes = {name: bridge.enclose(request[name]) for name in
                  ('candidate_nontrivial_box', 'original_full_domain', 'original_known_synthetic_source_point')}
    outputs = {}
    for name, mean_box in mean_boxes.items():
        result = new.replay(rows, mean_box, request['plan'], request['delta'], request['precision_bits'])
        result.update(physical_box_sha256=hashlib.sha256(jb.canonical(request[name])).hexdigest(),
                      physical_source_box_conditionally_excluded=result['status'] == 'CONDITIONAL_MEAN_BOX_EXCLUDED')
        outputs[name] = result
    baseline = old.replay(rows, mean_boxes['candidate_nontrivial_box'], request['plan'],
                          request['delta'], request['precision_bits'])
    improved = outputs['candidate_nontrivial_box']
    if baseline['exclusion_prefix']:
        assert improved['exclusion_prefix'] and improved['exclusion_prefix'] <= baseline['exclusion_prefix']
    elif not improved['exclusion_prefix']:
        assert Q(improved['best_prefix_mixture_lower']) >= Q(baseline['best_prefix_mixture_lower'])
    bridge.close()
    volume_ratio = Q(1)
    for key, pair in request['candidate_nontrivial_box'].items():
        a, b = map(Q, pair); c, d = map(Q, request['original_full_domain'][key])
        assert c <= a < b <= d
        volume_ratio *= (b - a) / (d - c)
    result = {'schema': 'tight-factor-original-saved-observation-replay-v1', 'status': 'PASS',
              'request_sha256': hashlib.sha256(request_raw).hexdigest(), 'source_sha256': source_hashes,
              'extrema_controls': extrema_checks, 'candidate_grid_controls': candidate_checks,
              'strict_factor_lower_improvements_in_controls': strict_improvements,
              'complete_extraction': extraction, 'forward_shifted_mean_enclosures': mean_boxes,
              'new_receiver_outputs': outputs, 'original_receiver_candidate_baseline': baseline,
              'nontrivial_candidate_relative_box_volume': str(volume_ratio),
              'actual_source_enclosure_calls': 3,
              'classification': request['classification'],
              'historical_plan_predeclaration_established': False,
              'finite_rng_certified': False, 'new_source_observations_generated': False,
              'sampler_or_inverse_search_run': False, 'data_confidence_certificate_issued': False,
              'whole_domain_normalized_width_goal_met': False, 'lean_kernel_checked': False,
              'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'extrema_controls': extrema_checks,
        'candidate_grid_controls': candidate_checks, 'strict_lower_improvements': strict_improvements,
        'physical_box_outcomes': {name: row['status'] for name, row in outputs.items()},
        'baseline_candidate_outcome': baseline['status'], 'candidate_relative_volume': str(volume_ratio)}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': source_hashes,
                                                   'request_sha256': hashlib.sha256(request_raw).hexdigest(),
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
