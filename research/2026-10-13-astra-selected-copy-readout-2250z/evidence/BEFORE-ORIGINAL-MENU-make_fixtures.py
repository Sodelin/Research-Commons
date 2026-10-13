#!/usr/bin/env python3
"""Prepare source fixtures from the exact hand-reviewed dot2200 tuple; no tests."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import selected_readout as subject

HERE = Path(__file__).resolve().parent
FIXTURE = HERE.parent/'2026-10-13-dot-g3-physical-singleton-fixture-2200z/PHYSICAL-FIXTURE.json'
FIXTURE_SHA = '7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba'


def primary():
    raw = FIXTURE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != FIXTURE_SHA:
        raise ValueError('accepted dot fixture identity changed')
    f = json.loads(raw)
    c, _, _ = subject.providers()
    source = dict(vertices=[dict(index=v['index'], id=v['id']) for v in f['vertices']], root=f['root'],
        edges=[{key: edge[key] for key in ['index', 'id', 'source', 'target', 'survival']} for edge in f['edges']],
        taxa=[dict(index=i, id=taxon, vertex=f['leaves'][taxon]) for i, taxon in enumerate(f['taxa'])],
        hybrids=[dict(index=h['index'], id=h['original_id'], vertex=h['vertex'],
                       incoming=h['incoming_occurrences'],
                       original_parent_1_probability=h['original_parent_1_probability'],
                       native_parent_0_probability=h['native_parent_0_probability']) for h in f['hybrids']],
        protected_edges={e['id']: e['id'] for e in f['edges']},
        protected_hybrids={h['original_id']: h['original_id'] for h in f['hybrids']},
        physical_context=dict(calendar={v['id']: v['age'] for v in f['vertices']},
            pair_rates={e['id']: e['pair_rate_expression'] for e in f['edges']},
            ancestral_pair_rate=f['ancestral_pair_rate'],
            provenance=dict(fixture_path=str(FIXTURE.relative_to(HERE.parent.parent)),
                fixture_sha256=FIXTURE_SHA, public_cutoff='4f39c2fe57ed1d528a193c653c0aac55efa3a106',
                status='hand-reviewed source tuple; native-to-typed binding and Lean instance unproved')))
    menu = dict(schema='supplied_common_menu_v1', taxa=f['taxa'],
        protected_edges=list(source['protected_edges']), protected_hybrids=list(source['protected_hybrids']),
        parameter_constraints=f['parameter_constraints'], configurations=f['configurations'], pairs=[])
    for i in f['taxa']:
        for j in f['taxa']:
            a = Fraction(1) if i == j else Fraction(1, 2) if {i,j} in [{'A','B'}, {'C','D'}] else Fraction(1, 4)
            generated = c.generate_singleton(list(map(str, [Fraction(1), a, a**3])))
            menu['pairs'].append(dict(i=i, j=j, certificate=generated['certificate']))
    return dict(schema='selected_native_common_readout_v1', menu=menu, source=source,
                budgets=dict(states=256, terms=4096, histories=256))


def asymmetric():
    request = primary()
    request['source']['edges'][4]['survival'] = '2/3'
    request['source']['physical_context']['pair_rates']['e4'] = '-log(2/3)/1'
    request['source']['physical_context']['provenance'].update(
        status='new unequal-arm formal test mutation; not the accepted dot physical fixture',
        mutation='e4 survival8/9→2/3, same occurrence order and Gamma1/3')
    return request


def correlated():
    request = asymmetric()
    s, m = request['source'], request['menu']
    s['vertices'] += [dict(index=9, id='S_second'), dict(index=10, id='H_second')]
    s['edges'][3]['survival'] = '1/2'; s['edges'][4]['survival'] = '3/4'
    s['edges'][5]['target'] = 9
    s['edges'] += [dict(index=9, id='e9', source=9, target=10, survival='2/3'),
                   dict(index=10, id='e10', source=9, target=10, survival='4/5'),
                   dict(index=11, id='e11', source=10, target=5, survival='1')]
    s['hybrids'].append(dict(index=1, id='H:second', vertex=10, incoming=[9,10],
        original_parent_1_probability='2/5', native_parent_0_probability='3/5'))
    s['protected_edges'].update({f'e{i}':f'e{i}' for i in range(9,12)})
    s['protected_hybrids']['H:second'] = 'H:second'
    s['physical_context'] = dict(calendar={}, pair_rates={}, ancestral_pair_rate='1',
        provenance=dict(status='formal two-site correlated-mask test only; no physical admission claim'))
    m['protected_edges'] = list(s['protected_edges']); m['protected_hybrids'] = list(s['protected_hybrids'])
    m['configurations'] = [dict(id='both0', weight='1/2', mask={'H:pendant-A':0,'H:second':0}),
                           dict(id='both1', weight='1/2', mask={'H:pendant-A':1,'H:second':1}),
                           dict(id='zero-natural', weight='0', mask={'H:pendant-A':None,'H:second':None})]
    return request


def main():
    examples=HERE/'examples';examples.mkdir(exist_ok=True)
    for name, request in [('dot2200-selected.json',primary()),('unequal-arm-selected.json',asymmetric()),
                          ('correlated-two-site-selected.json',correlated())]:
        with (examples/name).open('x') as f:json.dump(request,f,indent=2);f.write('\n')
    with (examples/'DOT-PHYSICAL-FIXTURE.json').open('xb') as f:f.write(FIXTURE.read_bytes())
    print(json.dumps(dict(status='SOURCE_FIXTURES_PREPARED',tests_run=False,compiler_run=False,
                         original_fixture_sha256=FIXTURE_SHA)))


if __name__ == '__main__':main()
