#!/usr/bin/env python3
"""Freeze one saved survival-root certificate without changing acceptance pointers.

The actual target audit and source/import receipts establish kernel completion;
the root's separate review establishes independent acceptance. Counts for the
122, 123 and 1504 closures overlap and must never be added.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('result', type=Path)
    parser.add_argument('--certificate', required=True)
    args = parser.parse_args()
    result_path = args.result.resolve(strict=True)
    result = json.loads(result_path.read_bytes())
    work = Path(result['workspace'])
    evidence = ROOT / result['evidence']
    final = result['final_receipt']
    assert final['status'] == 'PASS_ALL_REQUESTED_TARGETS'
    assert final['kernel_checking'] and final['trust_level'] == 0
    assert final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
    prep = json.loads((work / 'PREPARATION.json').read_bytes())
    graph = json.loads((work / 'DEPENDENCY-GRAPH.json').read_bytes())
    assert sha(work / 'DEPENDENCY-GRAPH.json') == prep['graph_sha256'] == final['graph_sha256']
    files = {r.get('restored_path', r['path']): r for r in result['preserved_files']}

    def raw(relative):
        row = files[relative]
        archived = (evidence / row['path']).read_bytes()
        assert len(archived) == row['bytes'] and hashlib.sha256(archived).hexdigest() == row['sha256']
        body = gzip.decompress(archived) if row.get('encoding') == 'gzip' else archived
        assert len(body) == row.get('restored_bytes', row['bytes'])
        assert hashlib.sha256(body).hexdigest() == row.get('restored_sha256', row['sha256'])
        return body

    summaries = {}
    for label in final['targets_passed']:
        target = graph['targets'][label]
        prefix = 'targets/' + ''.join(c if c.isascii() and (c.isalnum() or c in '_-') else '_' for c in label)
        checked = json.loads(raw(prefix + '/RESULT.json'))
        assert checked['status'] == 'PASS'
        assert checked['aggregate_receipt']['status'] == checked['audit_receipt']['status'] == 'PASS_FRESH_KERNEL_CHECK'
        assert len(checked['component_receipts']) == len(target['order'])
        components = {r['module']: r for r in checked['component_receipts']}
        assert set(components) == set(target['order'])
        audit_relative = str(Path(checked['audit_receipt']['audit_output']).relative_to(Path(result['actual_run'])))
        audit = json.loads(raw(audit_relative))
        assert audit['selected_modules'] == target['order']
        assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
        declarations = audit['declarations']
        assert len({r['name'] for r in declarations}) == len(declarations) == audit['declaration_count']
        assert sum(r['kind'] == 'theorem' for r in declarations) == audit['theorem_declaration_count']
        assert all(r['module'] in target['modules'] for r in declarations)
        for module in target['order']:
            rec = components[module]
            pin = target['modules'][module]['sha256']
            assert rec['source_sha256'] == pin == prep['source_pins'][module]
            assert sha(work / 'source-store' / (pin + '.lean')) == pin
            assert rec['source_and_imports_stable'] and rec['native_initialized_libraries_bound']
            assert rec['exit_code'] == 0
        summaries[label] = {'status': 'PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT',
            'roots': target['roots'], 'closure_modules': len(target['order']),
            'owned_declarations': audit['declaration_count'], 'owned_theorems': audit['theorem_declaration_count'],
            'owned_declaration_kind_counts': dict(Counter(r['kind'] for r in declarations)),
            'owned_axioms': [], 'nonstandard_axiom_rows': [], 'missing_modules': [],
            'audit_raw_sha256': files[audit_relative].get('restored_sha256', files[audit_relative]['sha256']),
            'audit_distribution': files[audit_relative]['path'],
            'aggregate_source_sha256': checked['aggregate_receipt']['source_sha256'],
            'audit_source_sha256': checked['audit_receipt']['source_sha256'],
            'source_and_import_bindings_stable': True}
    post = result['post_run_transport_verification']
    assert sha(Path(post['original_path'])) == post['original_sha256']
    post_result = json.loads(Path(post['original_path']).read_bytes())
    assert post_result['run'] == result['actual_run']
    assert post_result['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
    certificate = {'status': 'PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS',
        'workspace': str(work), 'actual_run': result['actual_run'], 'evidence': result['evidence'],
        'preservation_manifest_sha256': sha(evidence / 'PRESERVATION-MANIFEST.json'),
        'result_path': str(result_path), 'result_sha256': sha(result_path),
        'preparation_sha256': sha(work / 'PREPARATION.json'), 'graph_sha256': final['graph_sha256'],
        'source_pins': prep['source_pins'], 'derivatives': prep['derivatives'],
        'contexts': prep['contexts'], 'contexts_qualification': 'Accepted predecessor provenance; current graph/source versions and fresh root audits are separately bound here.',
        'targets': summaries, 'counts': final['counts'],
        'kernel_checking': True, 'trust_level': 0, 'compiler_sha256': final['compiler_sha256'],
        'native_runtime_digest': final['native_runtime_digest'], 'compiler_and_native_final_stable': True,
        'post_run_transport_verification': post, 'summarizer_sha256': sha(Path(__file__)),
        'root_independent_review_pending': True, 'current_acceptance_pointers_modified': False,
        'scope': 'Fixed supplied strict-calendar whole-edge exposure/survival image with positive real edge rates, natural and all original controlled completed laws; the G6 consumer reuses that construction. Closure counts overlap. This is no timed retiming or native source-representation refinement, effective source reconstruction, or G1-G7 master-completion claim.',
        'freshness_qualification': 'Exact kernel component receipts may come from preserved successful prefixes or this dated context. The listed target counts disclose reuse; its aggregate and full owned audit are freshly compiled.',
        'historical_evidence_or_scientific_gates_promoted': False}
    if 'current/connected' in summaries:
        old_path = ROOT / 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json'
        assert sha(old_path) == '87fc610c7d4ef52c064990f040e90791f6b34c37fff97ffa3e93b9b25a481750'
        old = json.loads(old_path.read_bytes())
        old_graph = json.loads((Path(old['workspace']) / 'DEPENDENCY-GRAPH.json').read_bytes())['targets']['current/connected']
        current = graph['targets']['current/connected']
        assert all(current['modules'][m] == r for m, r in old_graph['modules'].items())
        fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
        assert set(current['modules']) - set(old_graph['modules']) == set(fresh)
        assert len(current['modules']) == 1504 and len(fresh) == 7
        certificate['prior1497'] = {'certificate': str(old_path), 'sha256': sha(old_path),
            'all_source_versions_and_literal_import_graph_records_retained': True,
            'inherited_owned_declaration_metadata_comparison': 'Root independent review pending; no result invented.'}
        certificate['additional_exact_sources'] = fresh
    destination = ROOT / args.certificate
    assert destination.parent == ROOT and not destination.exists()
    save(destination, certificate)
    print(json.dumps({'certificate': str(destination), 'sha256': sha(destination),
        'targets': {k: {f: v[f] for f in ['closure_modules', 'owned_declarations', 'owned_theorems']} for k,v in summaries.items()},
        'counts': final['counts'], 'root_independent_review_pending': True}))


if __name__ == '__main__':
    main()
