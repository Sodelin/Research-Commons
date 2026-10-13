"""Own bounded exact graph/data check. No imported project or external code.
Does not emit or check the complete stochastic genealogy tables or Lean proofs.
Run: python3 -I -B check_fixture.py [fixture_directory]
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial, prod
import hashlib
import json
import sys

root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent
fixture = json.loads((root / 'PHYSICAL-FIXTURE.json').read_text())
menu = json.loads((root / 'COMMON-MENU.json').read_text())['input']
vs, es = fixture['vertices'], fixture['edges']
age = {v['index']: F(v['age']) for v in vs}
leaves = fixture['leaves']
incoming = {v['index']: [] for v in vs}
outgoing = {v['index']: [] for v in vs}
for e in es:
    incoming[e['target']].append(e['index'])
    outgoing[e['source']].append(e['index'])
    assert age[e['source']] - age[e['target']] == F(e['calendar_duration']) > 0
    assert 0 < F(e['survival']) < 1
assert [e['index'] for e in es] == list(range(9))
assert es[3]['source'] == es[4]['source'] and es[3]['target'] == es[4]['target']
assert es[3]['id'] != es[4]['id']
for v in vs:
    i = v['index']
    deg = (len(incoming[i]), len(outgoing[i]))
    assert deg == {'root': (0, 2), 'tree': (1, 2), 'hybrid': (2, 1), 'leaf': (1, 0)}[v['kind']]
    assert age[i] == (1 + max(age[es[e]['target']] for e in outgoing[i]) if outgoing[i] else 0)

def reach(start, excluded_vertex=None, excluded_edge=None, undirected=False):
    seen, todo = set(), [start]
    while todo:
        a = todo.pop()
        if a == excluded_vertex or a in seen:
            continue
        seen.add(a)
        for e in es:
            if e['index'] == excluded_edge:
                continue
            if e['source'] == a:
                todo.append(e['target'])
            if undirected and e['target'] == a:
                todo.append(e['source'])
    return seen

assert len(reach(0)) == len(vs)
assert all(any(t in reach(0, excluded_vertex=v) for t in leaves.values()) for v in range(1, 9))
assert 5 not in reach(4, excluded_edge=5, undirected=True)
h = fixture['hybrids'][0]
assert h['incoming_occurrences'] == [3, 4]
assert F(h['original_parent_1_probability']) + F(h['native_parent_0_probability']) == 1
assert 0 < F(h['original_parent_1_probability']) < 1
assert sum(F(z['weight']) for z in fixture['bank_support']) == 1

def path(taxon, bit):
    v, result = leaves[taxon], []
    while v != 0:
        ei = h['incoming_occurrences'][bit] if v == h['vertex'] else incoming[v][0]
        result.append((v, ei))
        v = es[ei]['source']
    return result + [(0, None)]

def survival(i, j, bit):
    right = {v for v, _ in path(j, bit)}
    x = F(1)
    for v, ei in path(i, bit):
        if v in right:
            return x
        x *= F(es[ei]['survival'])
    raise AssertionError('No common root')

for pair in menu['pairs']:
    c = pair['certificate']
    moments = list(map(F, c['moments']))
    a = survival(pair['i'], pair['j'], 0)
    assert a == survival(pair['i'], pair['j'], 1)
    assert moments == [1, a, a**3]
    coeff = list(map(F, c['coefficients']))
    assert coeff == [2*a**3, -3*a*a, 1]
    assert sum(x*y for x, y in zip(coeff, moments)) == 0
    assert c['nonnegative_terms'] == [
        {'weight': str(2*a), 'left': 0, 'right': 0, 'square': [str(-a), '1']},
        {'weight': '1', 'left': 1, 'right': 0, 'square': [str(-a), '1']}]

for row in fixture['rows_A_to_B']:
    k = row['level']
    assert row['copy_count'] == len(row['copies']) == k+5
    assert len({c['id'] for c in row['copies']}) == k+5
    assert len({json.dumps(c['type_tag']) for c in row['copies']}) == k+5
    assert {c['taxon'] for c in row['copies']} == set('ABCD')
    selected = row['copies'][:k+1]
    assert [c['taxon'] for c in selected] == ['A']*k + ['B']
    assert row['keep_copy_indices'] == list(range(k+1))
    tree = {'leaf': 'selected:B'}
    for i in range(k):
        tree = {'graft': [tree, {'leaf': f'selected:A:{i}'}]}
    assert row['event']['forest'] == [tree]
    coefficient = F(2**k, factorial(k+1)*factorial(k))
    moment = F(1, 2)**(k*(k-1)//2)
    assert F(row['comb_coefficient']) == coefficient
    assert F(row['moment']) == moment
    assert F(row['event_probability']) == coefficient*moment

print('PASS: degree, age, height, reachability, root-LSA and hybrid-child bridge checks')
print('PASS: original parallel occurrences, interior coin and two positive bank weights')
print('PASS: both actual selected routes give all 16 directed survivals and 48 sparse moments')
print('PASS: 6/7/8 distinct padded copies, literal ordered combs and exact normalization')
print('PASS: existing polynomial/square certificates pair exactly to zero')
print('LIMIT: no native full-table execution, no Lean compilation, no machine outer-face certificate')
for name in ['PHYSICAL-FIXTURE.json', 'COMMON-MENU.json', 'PHYSICAL-FIXTURE-AND-DERIVATION.md', 'check_fixture.py']:
    print(hashlib.sha256((root/name).read_bytes()).hexdigest(), name)
