"""One larger nested parameter-box check under the SAME fixed process."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import resource
import time

import joint_betting as jb
import rounded_betting as old
import tight_rounded_betting as new
from source_bridge import OriginalSourceBridge

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'expanded-box-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
          for name in ('joint_betting.py', 'rounded_betting.py', 'tight_factor.py',
                       'tight_rounded_betting.py', 'source_bridge.py', 'check_expanded_box.py')}
request_raw = (BASE / 'TIGHT-REPLAY-REQUEST.json').read_bytes()
request = json.loads(request_raw)
try:
    archive = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration'
    rows, extraction = jb.literal_rows(archive / 'declared-model/DATASET.json', request['dataset_sha256'],
                                      request['expected_loci'], request['selection_sha256'], archive / 'integration_core.py')
    candidate = {key: ['1/32', '1/16'] if key in ('h', 'u', 'v') else pair
                 for key, pair in request['candidate_nontrivial_box'].items()}
    bridge = OriginalSourceBridge(ROOT)
    mean_box = bridge.enclose(candidate)
    improved = new.replay(rows, mean_box, request['plan'], request['delta'], request['precision_bits'])
    baseline = old.replay(rows, mean_box, request['plan'], request['delta'], request['precision_bits'])
    if baseline['exclusion_prefix']:
        assert improved['exclusion_prefix'] and improved['exclusion_prefix'] <= baseline['exclusion_prefix']
    elif not improved['exclusion_prefix']:
        assert Q(improved['best_prefix_mixture_lower']) >= Q(baseline['best_prefix_mixture_lower'])
    volume_ratio = Q(1)
    for key, pair in candidate.items():
        a, b = map(Q, pair); c, d = map(Q, request['original_full_domain'][key])
        assert c <= a < b <= d
        volume_ratio *= (b - a) / (d - c)
    bridge.close()
    result = {'schema': 'same-process-expanded-original-source-box-check-v1', 'status': 'PASS',
              'source_sha256': hashes, 'original_request_sha256': hashlib.sha256(request_raw).hexdigest(),
              'candidate_physical_box': candidate, 'candidate_relative_box_volume': str(volume_ratio),
              'forward_shifted_mean_box': mean_box, 'tight_receiver': improved, 'old_receiver': baseline,
              'actual_source_enclosure_calls': 1, 'dataset_sha256': request['dataset_sha256'],
              'classification': 'conditional_saved_synthetic_model_replay',
              'same_plan_and_underlying_process_as_first_box': True,
              'historical_plan_predeclaration_established': False, 'finite_rng_certified': False,
              'new_source_observations_generated': False, 'data_confidence_certificate_issued': False,
              'sampler_or_inverse_search_run': False, 'whole_domain_width_goal_met': False,
              'lean_kernel_checked': False, 'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'candidate_relative_volume': str(volume_ratio),
        'tight_outcome': improved['status'], 'tight_prefix': improved['prefix_processed'],
        'old_outcome': baseline['status'], 'old_prefix': baseline['prefix_processed']}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': hashes,
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
