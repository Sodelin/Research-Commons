"""Finite exact audit controls, not sampled biological or coverage evidence."""
import datetime
from fractions import Fraction as Q
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys

source = Path('/workspace/cloud-practical/research/2026-10-07-cloud-practical-1619z/joint_betting.py')
spec = importlib.util.spec_from_file_location('_independent_betting_review', source)
jb = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = jb
spec.loader.exec_module(jb)

directions = [(Q(1),) + (Q(0),) * 8,
              (Q(1, 2), Q(-1, 2)) + (Q(0),) * 7,
              (Q(-1, 3), Q(1, 3), Q(1, 3)) + (Q(0),) * 6]
weights = (Q(1, 2), Q(1, 3), Q(1, 6))
plan = [{'weight': str(w), 'direction': list(map(str, d))}
        for w, d in zip(weights, directions)]
r0 = (0, 1, 0, 1, 0, 1, 0, 1, 0)
r1 = tuple(1 - x for x in r0)
probability = Q(3, 8)
true_mean = tuple((1 - probability) * x + probability * y for x, y in zip(r0, r1))


def direct_capitals(rows, mean):
    """Evaluate the equations directly, without receiver interval factors."""
    wealth = [Q(1)] * len(directions)
    past = [[] for _ in directions]
    path = [Q(1)]
    for row in rows:
        for j, direction in enumerate(directions):
            p = sum((a * m for a, m in zip(direction, mean)), Q(0))
            z = sum((a * x for a, x in zip(direction, row)), Q(0))
            if not past[j]:
                stake = Q(0)
            else:
                average = sum(past[j], Q(0)) / len(past[j])
                variance = sum((x * x for x in past[j]), Q(0)) / len(past[j]) - average ** 2
                stake = min(Q(1, 2), max(Q(-1, 2), (average - p) / (variance + Q(1, 16))))
            factor = 1 + stake * (z - p)
            assert Q(1, 2) <= factor <= Q(3, 2)
            wealth[j] *= factor
            past[j].append(z)
        path.append(sum((w * k for w, k in zip(weights, wealth)), Q(0)))
    return path


started = datetime.datetime.now(datetime.timezone.utc).isoformat()
expectations = []
point_checks = 0
for horizon in range(1, 7):
    expectation = Q(0)
    for bits in itertools.product((0, 1), repeat=horizon):
        rows = tuple(r1 if b else r0 for b in bits)
        path = direct_capitals(rows, true_mean)
        probability_of_path = probability ** sum(bits) * (1 - probability) ** (horizon - sum(bits))
        expectation += probability_of_path * path[-1]
        point_box = {name: [str(value)] * 2 for name, value in zip(jb.FEATURES, true_mean)}
        result = jb.replay(rows, point_box, plan)
        assert result['status'] == 'UNKNOWN'
        assert Q(result['best_prefix_mixture_lower']) == max(path)
        point_checks += 1
    assert expectation == 1
    expectations.append({'horizon': horizon, 'exact_expected_mixture': str(expectation)})

rows = (r0, r1, r1, r0)
broad_box = {name: ['1/4', '3/4'] if j < 2 else ['1/2', '1/2']
             for j, name in enumerate(jb.FEATURES)}
enclosure = jb.replay(rows, broad_box, plan)
interval_checks = 0
for first, second in itertools.product((Q(1, 4), Q(1, 2), Q(3, 4)), repeat=2):
    mean = (first, second) + (Q(1, 2),) * 7
    path = direct_capitals(rows, mean)
    assert Q(enclosure['best_prefix_mixture_lower']) <= max(path)
    interval_checks += 1

receipt = {'evidence': 'finite exact-rational synthetic-joint-law controls; no generated source data',
           'started_at': started,
           'ended_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'receiver_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'martingale_expectations': expectations,
           'point_receiver_checks': point_checks, 'interval_candidate_checks': interval_checks,
           'status': 'PASS', 'new_biological_observations': False,
           'scientific_admission_verified': False, 'lean_kernel_verified': False}
Path(__file__).with_name('independent-betting-controls.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
