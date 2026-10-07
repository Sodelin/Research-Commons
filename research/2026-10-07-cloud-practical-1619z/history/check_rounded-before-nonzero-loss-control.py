"""Bounded exact arithmetic controls for downward capital; no observations."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import resource
import time

import joint_betting as jb
import rounded_betting as rb
from source_bridge import OriginalSourceBridge, DOMAIN

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
OUT = BASE / 'rounded-attempt1'
OUT.mkdir(exist_ok=False)
resource.setrlimit(resource.RLIMIT_CPU, (5, 5))
resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
started = time.time()
source_hashes = {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest()
                 for name in ('joint_betting.py', 'rounded_betting.py', 'source_bridge.py', 'check_rounded.py')}
plan = [{'weight': '1', 'direction': ['1'] + ['0'] * 8}]
box = lambda q: {name: [str(q), str(q)] for name in jb.FEATURES}
try:
    checks = {}
    # Independent closed form: first factor1; thereafter fixed5/4 because all
    # prior scalar values1, candidate1/2, variance0, and stake clipped at1/2.
    lower = rb.replay(((1,) * 9,) * 24, box(Q(1, 2)), plan,
                      delta=str(Q(1, 1 << 200)), precision_bits=64)
    exact = Q(5, 4) ** 23
    observed = Q(lower['final_mixture_lower'])
    assert 0 <= exact - observed < 4 * exact * Q(1, 1 << 64)
    checks['known_closed_form_and_rounding_loss'] = {'exact': str(exact),
        'lower': str(observed), 'relative_loss_upper': str(Q(4, 1 << 64))}
    joint_plan = [{'weight': '1', 'direction': ['1/2', '-1/2'] + ['0'] * 7}]
    joint = rb.replay(((1, 0) + (0,) * 7,) * 40, box(Q(1, 2)), joint_plan)
    assert joint['status'] == 'CONDITIONAL_MEAN_BOX_EXCLUDED'
    checks['joint_contrast_exclusion'] = joint
    wide = {name: ['0', '1'] for name in jb.FEATURES}
    uncertain = rb.replay(((1,) * 9,) * 200, wide, plan)
    assert uncertain['status'] == 'UNKNOWN'
    checks['wide_box_remains_unknown'] = uncertain
    # 5000 algebraic vectors; true candidate equals every vector, giving the
    # independently known capital1. This checks stable storage, not runtime
    # at an actual original-source observation count or confidence frequency.
    stable = rb.replay(((1,) * 9,) * 5000, box(Q(1)), plan, precision_bits=64)
    assert stable['status'] == 'UNKNOWN' and stable['prefix_processed'] == 5000
    assert stable['final_mixture_lower'] == '1'
    assert stable['maximum_stored_capital_or_mixture_bits'] == 1
    checks['long_algebraic_storage_control'] = stable
    stopped = rb.replay(((1,) * 9,) * 40, box(Q(7, 13)), plan,
                        precision_bits=96, max_bits=16)
    assert stopped['status'] == 'UNKNOWN' and stopped['arithmetic_refusal'] == 'ARITHMETIC_BITS'
    checks['arithmetic_stop_remains_unknown'] = stopped
    old = ROOT / 'research/2026-10-05-dot-msci-phased-confidence-protocol-controls-1709z/controls/literal_two'
    req = json.loads((old / 'ANALYSIS-REQUEST.json').read_text())
    core = ROOT / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/integration_core.py'
    rows, _ = jb.literal_rows(old / 'DATASET.json', req['dataset_sha256'], 2, req['selection_sha256'], core)
    bridge = OriginalSourceBridge(ROOT)
    enclosed = bridge.enclose(DOMAIN)
    integrated = rb.replay(rows, enclosed, plan)
    assert integrated['status'] == 'UNKNOWN'
    checks['old_literal_fixture_original_full_domain_unknown'] = integrated
    bridge.close()
    result = {'schema': 'downward-capital-deterministic-controls-v1', 'status': 'PASS',
              'checks': checks, 'source_sha256': source_hashes,
              'source_enclosure_calls': 1,
              'new_source_observations_generated': False,
              'algebraic_controls_are_empirical_samples': False,
              'inverse_search_or_journal_run': False,
              'whole_domain_width_success_claimed': False,
              'lean_kernel_checked': False,
              'started_unix': started, 'ended_unix': time.time()}
    (OUT / 'RESULT.json').write_bytes(jb.canonical(result))
    print(json.dumps({'status': 'PASS', 'deterministic_controls': len(checks),
                      'old_fixture_outcome': integrated['status'],
                      'long_algebraic_prefix': stable['prefix_processed']}, sort_keys=True))
except BaseException as error:
    (OUT / 'FAILURE.json').write_bytes(jb.canonical({'status': 'FAIL', 'error': repr(error),
                                                   'source_sha256': source_hashes,
                                                   'started_unix': started, 'ended_unix': time.time()}))
    raise
