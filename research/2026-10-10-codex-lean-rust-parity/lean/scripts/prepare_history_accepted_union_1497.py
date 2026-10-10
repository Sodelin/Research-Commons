#!/usr/bin/env python3
"""Prepare one dated history-library union from authenticated accepted bytes.

Contributor: Codex / lean_integration_successor, 2026-10-10.
Only scratch location, graph composition and provenance change. The previously
frozen four-provider namespace wrapper (before install aliases), strict core,
audit template, compiler flags and resource caps are copied byte for byte.
This creates no compiler process, changes no accepted path, and copies no cache.
"""
from __future__ import annotations

import argparse
import datetime
import json
from pathlib import Path
import shutil

from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
PREVIOUS = Path('/tmp/rc-lean-integrated-library-union-1487-20261010T174456.536017Z')
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
AUDIT = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
OVERLAY = '09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0'
AUTHENTICATED = 'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'
PARENTS = [
    'INTEGRATED-MODULAR-UNION-CERTIFICATE.json',
    'SEMANTIC-RANK-RECOVERY-CERTIFICATE.json',
    'ACTUAL-CALENDAR-GATHERING-CERTIFICATE.json',
    'ORIGINAL-COMPLETION-FIXTURE-CERTIFICATE.json',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--feasibility', type=Path, required=True)
    args = parser.parse_args()
    report_path = args.feasibility.resolve(strict=True)
    report = json.loads(report_path.read_bytes())
    assert report['status'] == 'PASS_READONLY_EXACT_COHERENT_UNION_FEASIBILITY'
    assert report['modules'] == report['selected_completed_cache_keys'] == 1497
    assert report['added_modules'] == 10
    assert not report['source_or_literal_import_conflicts']
    feasible = ROOT / report['evidence']
    graph_path = feasible / 'PROPOSED-DEPENDENCY-GRAPH.json'
    selection_path = feasible / 'SELECTED-CACHE-IDENTITIES.json'
    assert sha(graph_path) == report['proposed_graph_sha256']
    assert sha(selection_path) == report['selected_cache_manifest_sha256']
    graph = json.loads(graph_path.read_bytes())
    target = graph['targets']['current/connected']
    assert len(target['modules']) == len(target['order']) == 1497
    assert len(set(target['order'])) == 1497
    assert not any(m.endswith('FixtureMain') for m in target['modules'])
    selected = json.loads(selection_path.read_bytes())
    assert {r['module'] for r in selected} == set(target['modules'])
    prior_prep = json.loads((PREVIOUS / 'PREPARATION.json').read_bytes())
    original_wrappers = ROOT / prior_prep['cache_install_transport_derivation']['evidence']
    old_overlay = original_wrappers / 'ORIGINAL-NAMESPACE-OVERLAY.py'
    old_authenticated = original_wrappers / 'ORIGINAL-AUTHENTICATED-OVERLAY.py'
    for p, expected in [
        (PREVIOUS / 'scripts/build_connected.py', CORE),
        (PREVIOUS / 'scripts/AuditTemplate.lean', AUDIT),
        (old_overlay, OVERLAY), (old_authenticated, AUTHENTICATED),
    ]:
        assert sha(p) == expected, p
    parent_pins = []
    for name in PARENTS:
        p = ROOT / name
        c = json.loads(p.read_bytes())
        assert c['status'] == 'PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS'
        assert c['kernel_checking'] and c['trust_level'] == 0
        parent_pins.append({'path': str(p), 'sha256': sha(p),
                            'workspace': c['workspace'], 'graph_sha256': c['graph_sha256'],
                            'targets': c['targets']})
    cache_alloc = sum(((p.stat().st_size + 4095) // 4096) * 4096
                      for row in selected for p in Path(row['cache_entry']).rglob('*') if p.is_file())
    source_paths = {row['source_path'] for row in selected}
    source_alloc = sum(((Path(p).stat().st_size + 4095) // 4096) * 4096 for p in source_paths)
    budget = {'cross_filesystem_cache_rounded_bytes': cache_alloc,
              'source_rounded_bytes': source_alloc,
              'fresh_run_reserve_bytes': 256 * 2**20,
              'packet_evidence_metadata_transient_reserve_bytes': 96 * 2**20,
              'previous1487_measured_run_residual_excluding_cache_links': 234393600,
              'limit_bytes': 2**30}
    budget['total_new_allocation_bound_bytes'] = sum(budget[k] for k in [
        'cross_filesystem_cache_rounded_bytes', 'source_rounded_bytes',
        'fresh_run_reserve_bytes', 'packet_evidence_metadata_transient_reserve_bytes'])
    assert budget['total_new_allocation_bound_bytes'] <= budget['limit_bytes']
    assert shutil.disk_usage('/dev/shm').free > budget['total_new_allocation_bound_bytes']
    assert shutil.disk_usage(ROOT).free > budget['packet_evidence_metadata_transient_reserve_bytes']
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-lean-history-accepted-union-1497-' + stamp)
    evidence = ROOT / 'evidence/proof-extensions/history-accepted-union-1497' / stamp
    assert not work.exists() and not evidence.exists()
    (work / 'scripts').mkdir(parents=True)
    (work / 'source-store').mkdir()
    evidence.mkdir(parents=True)
    for row in selected:
        module = row['module']
        h = target['modules'][module]['sha256']
        source = Path(row['source_path'])
        assert sha(source) == h == row['source_sha256']
        out = work / 'source-store' / (h + '.lean')
        if out.exists():
            assert sha(out) == h
        else:
            shutil.copyfile(source, out)
        frozen = evidence / 'sources' / (module.replace('.', '/') + '.lean')
        frozen.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, frozen)
        assert sha(out) == sha(frozen) == h
    shutil.copytree(PREVIOUS / 'third-party', work / 'third-party')
    for name in ['build_connected.py', 'AuditTemplate.lean']:
        shutil.copyfile(PREVIOUS / 'scripts' / name, work / 'scripts' / name)
    shutil.copyfile(old_overlay, work / 'scripts/build_with_mathlib_overlay.py')
    shutil.copyfile(old_authenticated, work / 'scripts/build_with_authenticated_overlay.py')
    shutil.copyfile(Path(__file__), evidence / 'PREPARER.py')
    shutil.copyfile(graph_path, work / 'DEPENDENCY-GRAPH.json')
    shutil.copyfile(graph_path, evidence / 'DEPENDENCY-GRAPH.json')
    derivation = {'status': 'PRE_USE_DATED_RAM_SCRATCH_LOCATION_AND_EXACT_HISTORY_COMPOSITION',
        'contributor': 'Codex / lean_integration_successor', 'preparer_sha256': sha(Path(__file__)),
        'previous_workspace': str(PREVIOUS), 'previous_preparation_sha256': sha(PREVIOUS / 'PREPARATION.json'),
        'workspace': str(work), 'scratch_root': '/dev/shm',
        'filesystem_reason': 'Separate RW tmpfs; /tmp capacity insufficient. All original paths are preserved.',
        'root_derivation': 'Unchanged wrappers derive ROOT from their new scripts directory; external compiler, Mathlib and native paths are unchanged.',
        'feasibility_report': str(report_path), 'feasibility_report_sha256': sha(report_path),
        'selected_cache_manifest': str(selection_path), 'selected_cache_manifest_sha256': sha(selection_path),
        'parent_certificates': parent_pins, 'budget': budget,
        'kernel_flags_core_audit_and_resource_caps_changed': False,
        'proof_sources_or_original_receipts_modified': False, 'compiler_launched': False,
        'cache_transport': 'Existing verified EXDEV-copy2 seeder; existing frozen installer derivation will verify originals and install exact local staged aliases by same-filesystem hardlink.'}
    prep = {'status': 'PREPARED_EXACT_ACCEPTED_HISTORY_LIBRARY_UNION_UNCOMPILED',
        'workspace': str(work), 'evidence': str(evidence), 'targets': ['current/connected'],
        'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'), 'contexts': report['contexts'],
        'derivatives': [], 'source_versions_and_literal_imports_pinned': True,
        'builder_sha256': CORE, 'audit_template_sha256': AUDIT,
        'official_complete_mathlib_namespace_overlay': True,
        'namespace_overlay_wrapper_sha256': OVERLAY, 'optimized_overlay_sha256': AUTHENTICATED,
        'source_pins': {m: r['sha256'] for m, r in target['modules'].items()},
        'historical_passes_copied': False, 'native_execution_claimed': False,
        'namespace_adapter_derivation': prior_prep['namespace_adapter_derivation'],
        'scratch_location_derivation': derivation}
    for out in [work, evidence]:
        save(out / 'PREPARATION.json', prep)
        save(out / 'LOCATION-AND-COMPOSITION-DERIVATION.json', derivation)
    save(ROOT / 'HISTORY-ACCEPTED-UNION-1497-PREPARATION.json', prep)
    print(json.dumps({'status': prep['status'], 'workspace': str(work), 'evidence': str(evidence),
                      'modules': 1497, 'budget': budget}))


if __name__ == '__main__':
    main()
