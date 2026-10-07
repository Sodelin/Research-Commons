"""Fresh consumer verification; no caller-PASS, new samples or full-D replay."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import resource
import time

import joint_betting as jb
from source_bridge import OriginalSourceBridge, DOMAIN
import complete_cover as cc

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'complete-cover-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
          for name in ('joint_betting.py', 'tight_factor.py', 'tight_rounded_betting.py',
                       'source_bridge.py', 'complete_cover.py', 'check_complete_cover.py')}
try:
    request_raw = (BASE / 'TIGHT-REPLAY-REQUEST.json').read_bytes()
    request = json.loads(request_raw)
    archive = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    rows, extraction = jb.literal_rows(archive / 'declared-model/DATASET.json', request['dataset_sha256'],
                                      request['expected_loci'], request['selection_sha256'], archive / 'integration_core.py')
    excluded = {key: ['1/32', '1/16'] if key in ('h', 'u', 'v') else pair
                for key, pair in request['candidate_nontrivial_box'].items()}
    bridge = OriginalSourceBridge(ROOT)
    actual = cc.build(rows, excluded, request['plan'], bridge, request['delta'], request['precision_bits'])
    assert actual['candidate_cell_removed'] and actual['retained_cell_count'] == 15
    assert actual['recomputed_exclusion_evidence']['exclusion_prefix'] == 190
    assert actual['status'] == 'UNKNOWN' and set(actual['whole_union_normalized_widths'].values()) == {'1'}
    expected_signatures = set(__import__('itertools').product((0, 1), repeat=4)) - {cc.REMOVED_SIGNATURE}
    assert {tuple(cell['signature']) for cell in actual['retained_cover']} == expected_signatures
    def contains(point, box):
        return all(Q(box[key][0]) <= value <= Q(box[key][1]) for key, value in point.items())
    truth = {key: Q(pair[0]) for key, pair in request['original_known_synthetic_source_point'].items()}
    assert any(contains(truth, cell['physical_box']) for cell in actual['retained_cover'])
    interior = {key: (Q(pair[0]) + Q(pair[1])) / 2 for key, pair in excluded.items()}
    assert not any(contains(interior, cell['physical_box']) for cell in actual['retained_cover'])
    volume = Q(0)
    for cell in actual['retained_cover']:
        relative = Q(1)
        for key, pair in cell['physical_box'].items():
            a, b = map(Q, pair); c, d = map(Q, DOMAIN[key])
            assert c <= a < b <= d
            relative *= (b - a) / (d - c)
        volume += relative
    assert volume == Q(295, 297)
    # Changed budget verifies NEW consumer's refusal/fallback route. It does
    # not rerun the unchanged full-D confidence test or any old factor controls.
    limited = cc.build(rows, excluded, request['plan'], bridge, request['delta'],
                       request['precision_bits'], max_bits=16)
    assert not limited['candidate_cell_removed'] and limited['retained_cell_count'] == 1
    assert limited['retained_cover'][0]['physical_box'] == DOMAIN and limited['status'] == 'UNKNOWN'
    assert limited['recomputed_exclusion_evidence']['arithmetic_refusal'] == 'ARITHMETIC_BITS'
    bridge.close()
    result = {'schema': 'original-complete-cover-consumer-check-v1', 'status': 'PASS',
              'source_sha256': hashes, 'request_sha256': hashlib.sha256(request_raw).hexdigest(),
              'dataset_sha256': request['dataset_sha256'],
              'actual_cover': actual, 'changed_budget_fallback': limited,
              'retained_relative_cartesian_volume': str(volume),
              'archived_source_contained': True, 'excluded_interior_point_not_retained': True,
              'actual_source_enclosure_calls': 2, 'unchanged_full_domain_confidence_test_rerun': False,
              'new_observations_generated': False, 'sampler_or_inverse_journal_run': False,
              'data_confidence_certificate_issued': False,
              'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'retained_cells': 15,
                      'source_exclusion_prefix': 190, 'all_union_widths': '1',
                      'original_width_goal': 'UNKNOWN', 'changed_budget_fallback_cells': 1}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': hashes,
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
