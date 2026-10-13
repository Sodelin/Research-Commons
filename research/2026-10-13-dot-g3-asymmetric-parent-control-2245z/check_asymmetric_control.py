"""Own exact data regression. No native source, compiler or third-party import.
Usage: python3 -I -B check_asymmetric_control.py BASE_FIXTURE_JSON [NEW_FIXTURE_JSON]
"""
import copy
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

base_bytes = Path(sys.argv[1]).read_bytes()
assert hashlib.sha256(base_bytes).hexdigest() == '7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba'
base = json.loads(base_bytes)
path = Path(sys.argv[2]) if len(sys.argv) > 2 else Path(__file__).with_name('ASYMMETRIC-PHYSICAL-FIXTURE.json')
new = json.loads(path.read_text())
for key in ['vertices', 'root', 'leaves', 'hybrids', 'ancestral_pair_rate', 'configurations', 'same_tuple_all_rows', 'parameter_constraints', 'source_count']:
    assert base[key] == new[key]
for i, edge in enumerate(new['edges']):
    expected = copy.deepcopy(base['edges'][i])
    if i == 4:
        expected['survival'] = '4/9'
        expected['pair_rate_expression'] = '-log(4/9)/1'
    assert edge == expected
    assert 0 < F(edge['survival']) < 1 and F(edge['calendar_duration']) > 0
expected = copy.deepcopy(base['native_survival_bank'])
expected['values'][4] = '4/9'
assert new['native_survival_bank'] == expected
assert new['hybrids'][0]['incoming_occurrences'] == [3, 4]
gamma = F(new['hybrids'][0]['original_parent_1_probability'])
g0 = F(new['hybrids'][0]['native_parent_0_probability'])
assert (gamma, g0) == (F(1, 3), F(2, 3))
survival = lambda i: F(new['edges'][i]['survival'])
x0 = survival(5) * survival(3) * survival(2)
x1 = survival(5) * survival(4) * survival(2)
assert (x0, x1) == (F(1, 2), F(1, 4))
for old_row, row in zip(base['rows_A_to_B'], new['rows_A_to_B']):
    for key in old_row:
        if key not in ['moment', 'event_probability']:
            assert row[key] == old_row[key]
    k = row['level']
    lam = k * (k-1) // 2
    correct = g0*x0**lam + gamma*x1**lam
    wrong = gamma*x0**lam + g0*x1**lam
    renamed = (1-g0)*x1**lam + g0*x0**lam
    c = F(row['comb_coefficient'])
    control = new['wrong_binding_control']
    assert correct == F(row['moment']) == renamed
    assert c*correct == F(row['event_probability'])
    assert wrong == F(control['normalized_moments'][k-1])
    assert c*wrong == F(control['event_probabilities'][k-1])
    assert correct-wrong == F(control['correct_minus_wrong_normalized'][k-1])
    assert c*(correct-wrong) == F(control['correct_minus_wrong_event'][k-1])
    assert correct-wrong == (1-2*gamma)*(x0**lam-x1**lam)
    print(f'PASS k={k}: correct moment={correct}, raw={c*correct}; wrong moment={wrong}, raw={c*wrong}')
poly = lambda x: (x-F(1, 2))**2 * (x+1)
assert g0*poly(x0)+gamma*poly(x1) == F(5, 192)
assert gamma*poly(x0)+g0*poly(x1) == F(5, 96)
assert F(17, 192)-F(5, 12)**3 == F(7, 432)
print('PASS: sole changed physical parameter e4, original occurrences/coin/calendar/copies/event preserved')
print('PASS: one-sided reversal detected, fully transported mixture reindexing preserves moments')
print('PASS: old singleton certificate is not annihilated; no source NO inferred')
print('LIMIT: exact finite-data checks only; no native forward table or Lean execution')
