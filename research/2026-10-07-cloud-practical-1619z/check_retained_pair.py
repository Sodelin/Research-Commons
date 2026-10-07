"""One same-data admitted-source pair check, with upper evidence and guards."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import resource
import time

import joint_betting as jb
import upper_membership as upper
from source_bridge import OriginalSourceBridge, DOMAIN

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'retained-pair-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
          for name in ('joint_betting.py', 'tight_factor.py', 'source_bridge.py',
                       'upper_membership.py', 'check_retained_pair.py')}
try:
    # Changed upper receiver: independent closed-form arithmetic test with
    # strictly positive rounding surplus, not a repeated old lower control.
    control_box = {name: ['1/2', '1/2'] for name in jb.FEATURES}
    control_plan = [{'weight': '1', 'direction': ['1'] + ['0'] * 8}]
    control = upper.replay(((1,) * 9,) * 24, control_box, control_plan,
                           delta=str(Q(1, 1 << 200)), precision_bits=16)
    exact = Q(5, 4) ** 23
    surplus = Q(control['maximum_prefix_mixture_upper']) - exact
    assert 0 < surplus < 4 * exact * Q(1, 1 << 16)
    request_raw = (BASE / 'TIGHT-REPLAY-REQUEST.json').read_bytes()
    request = json.loads(request_raw)
    archive = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    rows, extraction = jb.literal_rows(archive / 'declared-model/DATASET.json', request['dataset_sha256'],
                                      request['expected_loci'], request['selection_sha256'], archive / 'integration_core.py')
    source0 = {key: list(pair) for key, pair in request['original_known_synthetic_source_point'].items()}
    source1 = {key: list(pair) for key, pair in source0.items()}
    source1['rA'] = ['13/10', '13/10']
    bridge = OriginalSourceBridge(ROOT)
    boxes = [bridge.enclose(source) for source in (source0, source1)]
    memberships = [upper.replay(rows, box, request['plan'], request['delta'], request['precision_bits'])
                   for box in boxes]
    bridge.close()
    separation = (Q(13, 10) - 1) / (Q(DOMAIN['rA'][1]) - Q(DOMAIN['rA'][0]))
    assert separation == Q(3, 55) and separation > Q(1, 20)
    for name in jb.FEATURES:
        if name != 'AA1':
            assert boxes[0][name] == boxes[1][name]
    limited = upper.replay(rows, boxes[0], request['plan'], request['delta'],
                           request['precision_bits'], max_bits=16)
    assert limited['status'] == 'UNKNOWN' and limited['arithmetic_refusal'] == 'ARITHMETIC_BITS'
    retained = all(result['status'] == 'ALL_PREFIX_MEAN_BOX_MEMBERSHIP_CERTIFIED' for result in memberships)
    result = {'schema': 'same-process-original-source-retained-pair-check-v1', 'status': 'PASS',
              'source_sha256': hashes, 'request_sha256': hashlib.sha256(request_raw).hexdigest(),
              'dataset_sha256': request['dataset_sha256'], 'complete_extraction': extraction,
              'source_parameter_points': [source0, source1], 'source_mean_enclosures': boxes,
              'all_prefix_membership_receivers': memberships,
              'normalized_rA_separation': str(separation),
              'specified_region_width_goal_obstructed_by_retained_pair': retained,
              'upper_closed_form_control': control, 'upper_rounding_surplus': str(surplus),
              'changed_budget_guard': limited,
              'actual_source_enclosure_calls': 2, 'new_observations_generated': False,
              'arbitrary_estimator_impossibility_claimed': False,
              'historical_plan_predeclaration_established': False, 'finite_rng_certified': False,
              'data_confidence_certificate_issued': False, 'sampler_or_inverse_journal_run': False,
              'lean_kernel_checked': False, 'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'source_memberships': [r['status'] for r in memberships],
                      'rA_separation': str(separation),
                      'specified_region_width_goal_obstructed': retained}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': hashes,
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
