"""Exact tests of four-tip metric-marginal target recovery.

Supplied source fixtures only. The second pass uses serialized observable
local derivatives and calendar covers, with no source or inheritance fields.
Finite tests support the written proof; they are not an all-source census.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from copy import deepcopy
import os
import gzip, hashlib, json, platform, sys, time
import networkx as nx
import sympy as sp
from metric_partition_inverse import (
    supplied_fixtures, splits_from_clusters, quartets_from_splits, canonical, Unknown,
)
from new_fixtures import stress_sources
from quartet_target import decode_quartet_marginals, find_common_circle, boundary_splits

HERE = Path(__file__).resolve().parent
OUT = Path(os.environ.get('G5_OUTPUT_DIR', str(HERE)))
OUT.mkdir(parents=True, exist_ok=True)


def require(test, description):
    if not test:
        raise AssertionError(description)


def serialize_Q(Q):
    return [{'subset': A, 'support': sorted(q)} for A, q in sorted(Q.items())]


def archive_oracle(case):
    # Only these four observation fields are accepted. No biological source,
    # inheritance-mode flag or source parameter is part of this input object.
    if set(case) != {'case_id', 'labels', 'calendar_cells', 'germs'}:
        raise ValueError('Unexpected observation archive fields')
    values = {}
    for row in case['germs']:
        key = (tuple(row['selected']), row['time'])
        values[key] = [dict((canonical(p), F(w)) for p, w in derivative)
                       for derivative in row['derivatives']]
    def get(selected, t, k):
        try:
            return values[(tuple(selected), t)][k]
        except (KeyError, IndexError):
            raise Unknown('Requested exact derivative is not in the supplied archive') from None
    return get


def main():
    started = time.time()
    fixtures = supplied_fixtures() + stress_sources()
    selected_case = os.environ.get('G5_CASE_FILTER')
    report = {'status': 'RUNNING', 'session': 'G5-QUARTET-MARGINALS-20260930',
              'python': platform.python_version(), 'sympy': sp.__version__, 'networkx': nx.__version__,
              'case_filter': selected_case,
              'scope': 'Explicit admitted fixtures and order decoding of their supplied target tables; no source census or query-minimum computation.',
              'input_domain': 'Exact local right-germ derivatives with a valid finite calendar cover; not an arbitrary-law membership validator.',
              'cases': [], 'total_quartet_runs': 0, 'total_source_generated_germ_certificates': 0,
              'total_source_free_replay_germ_certificates': 0, 'total_boundary_checks': 0,
              'max_selected_tips_per_germ': 0, 'max_spectral_atoms': 0, 'max_derivative_order': 0,
              'quartet_cluster_comparisons': 0, 'source_free_replays': 0}
    all_certificates = []
    records = []
    observations = []
    def save():
        (OUT/'quartet-checks.json').write_text(json.dumps(report, indent=2)+'\n')

    for source in fixtures:
        if selected_case and not selected_case.startswith(source.name+'/'):
            continue
        admission = source.validate()
        reference_C, displayed_trees = source.switching_clusters()
        reference_S = splits_from_clusters(source.labels, reference_C)
        reference_Q = quartets_from_splits(source.labels, reference_S)
        record = {'name': source.name, 'ages_in_units_of_log_2': source.ages, 'labels': source.labels,
                  'edges': [e.__dict__ for e in source.edges],
                  'inheritance': {h: str(g) for h, g in source.inheritance.items()},
                  'ancestral_rate': source.ancestral_rate, 'admission': admission}
        records.append(record)
        distinct_trees = len({tuple(sorted(tuple(sorted(b)) for b in cc)) for cc in displayed_trees})
        for mode in ('common', 'independent'):
            if selected_case and selected_case not in (source.name+'/'+mode):
                continue
            case_started = time.time()
            cache = {}
            requested = defaultdict(set)
            def germ(selected, t, k):
                key = (tuple(selected), t)
                require(len(selected) <= 4, 'The decoder requested more than four sampled tips')
                if key not in cache:
                    cache[key] = source.local_mixture(selected, t, mode)
                requested[key].add(k)
                return cache[key].derivative(k)
            Q, S, order, receipt = decode_quartet_marginals(source.labels, source.cells(), germ)
            print('DECODED',source.name,mode,round(time.time()-case_started,3),flush=True)
            require(Q == reference_Q, 'Complete Q mismatch: '+source.name+'/'+mode)
            require(S == reference_S, 'Complete S mismatch: '+source.name+'/'+mode)
            for run in receipt['quartet_runs']:
                A = frozenset(run['subset'])
                wanted = {frozenset(c) & A for c in reference_C if frozenset(c) & A}
                require({frozenset(c) for c in run['clusters']} == wanted,
                        'Marginal displayed-cluster mismatch: '+source.name+'/'+mode)
                report['quartet_cluster_comparisons'] += 1
            for row in receipt['local_certificates']:
                key = (tuple(row['selected']), row['time'])
                atoms = row['algebra']['spectral_atom_count']
                degree = row['algebra']['highest_derivative_used']
                report['max_selected_tips_per_germ'] = max(report['max_selected_tips_per_germ'], len(key[0]))
                report['max_spectral_atoms'] = max(report['max_spectral_atoms'], atoms)
                report['max_derivative_order'] = max(report['max_derivative_order'], degree)
                # The receipt contains exact weights in a JSON-friendly form.
                # Independent truth here was the original source-derived mixture.
                weights = {canonical(item['partition']): F(item['weight']) for item in row['algebra']['occupancy_weights']}
                require(weights == cache[key].truth(), 'Exact local tomography failed')
            case_id = f'case-{len(observations):03d}'
            observation = {'case_id': case_id, 'labels': source.labels,
                           'calendar_cells': source.cells(), 'germs': []}
            for key in sorted(requested):
                selected, t = key
                observation['germs'].append({
                    'selected': selected, 'time': t,
                    'derivatives': [[(p, str(w)) for p, w in sorted(cache[key].derivative(k).items())]
                                    for k in range(max(requested[key])+1)]})
            print('ARCHIVE_READY',source.name,mode,round(time.time()-case_started,3),flush=True)
            # Round trip through JSON, so replay does not retain source object references.
            observation = json.loads(json.dumps(observation))
            replay_Q, replay_S, replay_order, replay_receipt = decode_quartet_marginals(
                observation['labels'], observation['calendar_cells'], archive_oracle(observation))
            require((replay_Q, replay_S, replay_order) == (Q, S, order), 'Source-free replay mismatch')
            require(replay_receipt == receipt, 'Replay certificate/stage discrepancy')
            observations.append(observation)
            checkpoint_dir=OUT/'case-checkpoints';checkpoint_dir.mkdir(exist_ok=True)
            (checkpoint_dir/(source.name+'-'+mode+'.json')).write_text(json.dumps({'case_id':case_id,'quartets':len(Q),'germs':len(receipt['local_certificates']), 'source_free_replay_match':True})+'\n')
            all_certificates.append({'case_id': case_id, **receipt})
            nruns = len(receipt['quartet_runs']); ngerms = len(receipt['local_certificates'])
            report['source_free_replays'] += 1
            report['total_quartet_runs'] += nruns
            report['total_source_generated_germ_certificates'] += ngerms
            report['total_source_free_replay_germ_certificates'] += len(replay_receipt['local_certificates'])
            report['total_boundary_checks'] += receipt['boundary_membership_checks']
            report['cases'].append({'case_id': case_id, 'fixture': source.name, 'mode': mode,
                'admission': admission, 'distinct_displayed_rooted_trees': distinct_trees,
                'switchings_evaluated': len(displayed_trees), 'quartets': nruns, 'germ_certificates': ngerms,
                'reference_split_count': len(S), 'Q': serialize_Q(Q), 'S': sorted(S),
                'compatible_circle': order, 'order_search_nodes': receipt['order_search_nodes'],
                'exact_Q_S_match': True, 'source_free_replay_match': True,
                'seconds': round(time.time()-case_started,4)})
            print(source.name, mode, 'PASS',nruns,'quartets',ngerms,'germs',flush=True)
            save()

    # Structural negative and resource controls are distinct from biology.
    guard_count = 0
    four = tuple('abcd')
    all_three = {four: {canonical((('a','b'),('c','d'))), canonical((('a','c'),('b','d'))),
                        canonical((('a','d'),('b','c')))}}
    def expect(exc, fn):
        try:
            fn()
        except exc:
            return
        raise AssertionError('Expected '+exc.__name__)
    expect(ValueError, lambda: find_common_circle(four, all_three)); guard_count += 1
    expect(ValueError, lambda: find_common_circle(four, {})); guard_count += 1
    expect(ValueError, lambda: find_common_circle(four, {four: set()})); guard_count += 1
    valid = {four: {canonical((('a','b'),('c','d')))}}
    expect(Unknown, lambda: find_common_circle(four, valid, max_search_nodes=1)); guard_count += 1
    broken = deepcopy(observations[0]); broken['germs'] = []
    expect(Unknown, lambda: decode_quartet_marginals(broken['labels'], broken['calendar_cells'], archive_oracle(broken))); guard_count += 1
    badfields = deepcopy(observations[0]); badfields['source_graph'] = {}
    expect(ValueError, lambda: archive_oracle(badfields)); guard_count += 1
    report['input_and_resource_guards'] = guard_count
    report['status'] = 'PASS'
    report['seconds_this_run'] = round(time.time()-started,4)
    report['not_claimed'] = ['independent proof acceptance', 'Lean verification', 'numerical inference from sampled loci',
                             'arbitrary-law membership validation', 'minimality of four tips',
                             'recovery of full n-tip joint laws from these marginals', 'source-class or exact-query enumeration']
    (OUT/'quartet-fixtures.json').write_text(json.dumps(records, indent=2)+'\n')
    (OUT/'quartet-observations.json.gz').write_bytes(gzip.compress(json.dumps(observations,separators=(',',':')).encode('utf-8'),mtime=0))
    (OUT/'quartet-certificates.json.gz').write_bytes(gzip.compress(json.dumps(all_certificates,separators=(',',':')).encode('utf-8'),mtime=0))
    report['payload_sha256'] = {name: hashlib.sha256(((HERE if name.endswith('.py') else OUT)/name).read_bytes()).hexdigest()
        for name in ['metric_partition_inverse.py','quartet_target.py','new_fixtures.py','verify_quartet_target.py',
                     'quartet-fixtures.json','quartet-observations.json.gz','quartet-certificates.json.gz']}
    save()
    print('DONE',json.dumps({k:v for k,v in report.items() if k.startswith('total_') or k.startswith('max_') or k=='seconds_this_run'}),flush=True)

if __name__ == '__main__':
    main()
