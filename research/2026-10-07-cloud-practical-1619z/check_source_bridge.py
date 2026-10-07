"""One bounded fresh source/fixture integration, with failed outputs preserved."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import resource
import time

import joint_betting as jb
from source_bridge import OriginalSourceBridge, DOMAIN

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OLD = ROOT / 'research/2026-10-05-dot-msci-phased-confidence-protocol-controls-1709z/controls/literal_two'
CORE = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/integration_core.py'
OUT = BASE / 'source-bridge-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
source_hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                 for name in ('joint_betting.py', 'source_bridge.py', 'check_source_bridge.py')}
try:
    request = json.loads((OLD / 'ANALYSIS-REQUEST.json').read_text())
    rows, extraction = jb.literal_rows(OLD / 'DATASET.json', request['dataset_sha256'],
                                      2, request['selection_sha256'], CORE)
    plan = [{'weight': '1/2', 'direction': ['1'] + ['0'] * 8},
            {'weight': '1/2', 'direction': ['1/2', '-1/2'] + ['0'] * 7}]
    bridge = OriginalSourceBridge(ROOT)
    full_domain = bridge.replay(rows, DOMAIN, plan)
    assert full_domain['conditional_status'] == 'UNKNOWN'
    pair_results = []
    for a in ('57/10', '6'):
        physical = {key: [value, value] for key, value in
                    dict(h='1/32', u='1/32', v='1/32', g='1/4',
                         rA=a, rB='6', rC='6', rAB='6', rR='6').items()}
        result = bridge.replay(rows, physical, plan)
        assert result['conditional_status'] == 'UNKNOWN'
        pair_results.append(result)
    # Check agreement with the separately accepted old source-mean enclosures.
    prior_path = ROOT / 'research/2026-10-07-dot-certified-near-collision-receiver-0952z/evidence/PAIR-FORWARD.json'
    prior = json.loads(prior_path.read_text())
    for result, old_source in zip(pair_results, prior['sources']):
        for name in jb.FEATURES:
            left, right = map(Q, result['forward_enclosed_shifted_means'][name])
            old_left, old_right = map(Q, old_source['shifted_mean_enclosures'][name])
            assert max(left, old_left) <= min(right, old_right)
    # Pure algebraic control only: not a newly generated source dataset.
    control = bridge.replay(((1,) * 9,) * 60,
                            {key: ['1/32', '1/32'] if key in ('h', 'u', 'v') else
                             ['1/4', '1/4'] if key == 'g' else ['6', '6'] for key in DOMAIN},
                            [{'weight': '1', 'direction': ['1'] + ['0'] * 8}])
    assert control['conditional_status'] == 'CONDITIONAL_ORIGINAL_SOURCE_BOX_EXCLUDED'
    outside = dict(DOMAIN); outside['rA'] = ['1/4', '6']
    try:
        bridge.enclose(outside)
    except jb.Invalid:
        rejected = True
    else:
        raise AssertionError('outside-domain box was accepted')
    bridge.close()
    result = {'schema': 'original-source-bridge-deterministic-check-v1', 'status': 'PASS',
              'full_domain_old_fixture': full_domain,
              'near_collision_sources_old_fixture': pair_results,
              'algebraic_exclusion_control': control,
              'outside_domain_guard_rejected': rejected,
              'prior_pair_mean_artifact_sha256': hashlib.sha256(prior_path.read_bytes()).hexdigest(),
              'dataset_sha256': request['dataset_sha256'],
              'source_sha256': source_hashes,
              'actual_source_enclosure_calls': 4,
              'new_source_observations_generated': False,
              'fixture_repetition_is_empirical_sample': False,
              'inverse_search_or_journal_run': False,
              'scientific_admission_verified': False,
              'data_confidence_certificate_issued': False,
              'lean_kernel_checked': False,
              'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'source_enclosure_calls': 4,
                      'old_fixture_results': ['UNKNOWN'] * 3,
                      'algebraic_control': control['conditional_status']}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': source_hashes,
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
