#!/usr/bin/env python3
"""Recheck finite artifacts; does not grade language or call a model/provider."""
import hashlib
import json
import shlex
import subprocess
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def read(path):
    return json.loads((ROOT / path).read_text())

manifest = read('fixtures/manifest.json')
for name, metrics in manifest['metrics'].items():
    data = (ROOT / 'fixtures' / name).read_bytes()
    assert len(data) == metrics['utf8_bytes']
    assert hashlib.sha256(data).hexdigest() == metrics['sha256']
inventory = read('fixtures/inventory.json')
for arm in 'PQRS':
    body = (ROOT / 'fixtures' / f'{arm}-memory.txt').read_text()
    contents = ([r['content'] for r in json.loads(body)['records']]
                if arm == 'S' else body)
    assert all(r['content'] in contents for r in inventory['records'])

gold = read('discovery/gold.json')
inputs = [F(str(x)) for x in gold['withheld_inputs']]
a, b = [F(2)], [F(6)]
for u in inputs:
    a.append(F(7, 10)*a[-1] + 2*u)
    b.append(F(7, 10)*b[-1] + 6*u)
assert all(y == 3*x for x, y in zip(a, b))
for arm in ('none', 'flat', 'linked'):
    answer = read(f'discovery/{arm}-answer.json')
    assert [F(str(x)) for x in answer['A_path']] == a
    assert [F(str(x)) for x in answer['B_path']] == b
    for model, keys in [('A', ['alpha', 'beta']),
                        ('B', ['gamma', 'delta']),
                        ('C', ['eta', 'theta', 'kappa'])]:
        assert [answer['models'][model][k] for k in keys] == gold['coefficients'][model]
    witness = answer['C_counterexample']
    initial = witness['initial']
    current = witness.get('unseen_current_input', witness.get('unseen_input'))
    p, s, h = (F(str(initial[k])) for k in ('p', 's', 'h'))
    u, r = (F(str(current[k])) for k in ('a', 'r'))
    assert s == 3*p and u == r
    a_next, c_next = F(7, 10)*p + 2*u, F(7, 10)*s + 6*h
    assert 3*a_next != c_next
    assert F(str(witness['A_next'])) == a_next
    assert F(str(witness.get('C_next', witness.get('actual_C_next')))) == c_next

search = read('heldout/search-answer.json')
returned = []
for query in search['searches']:
    result = subprocess.run(shlex.split(query['query']), cwd=ROOT / 'heldout',
                            capture_output=True, text=True, check=True)
    count = len(result.stdout[:query['output_cap_characters']])
    assert count == query['returned_source_characters']
    returned.append(count)
source_chars = sum(len((ROOT / 'heldout' / name).read_text()) for name in
                   ('decision-certificate-correction.md', 'AGENTS.md'))
assert source_chars == 3880 and sum(returned) == 3043

output = {
    'manifest_hashes_and_body_preservation': 'passed',
    'discovery_exact_arithmetic_and_three_answer_witnesses': 'passed',
    'full_document_source_characters': source_chars,
    'search_output_characters': returned,
    'not_provider_token_counts': True,
    'limits': 'Finite artifacts only. Language judgments, execution telemetry, human utility, general scientific transfer and long-term learning are not mechanically validated.'
}
(ROOT / 'results' / 'validation.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
