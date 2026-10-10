#!/usr/bin/env python3
"""Freeze seven proposed consumers over immutable accepted1497 inputs; no Lean.

Contributor: Codex / lean_integration_successor, 2026-10-10.
Six historical bodies are checked first. The two-proof G6 consumer is separate.
The existing cache admission/installer code is retained except for the exact
manifest partition into authenticated old modules and explicitly fresh sources.
"""
from __future__ import annotations

import argparse
import datetime
import errno
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
COMMONS = ROOT.parents[2]
PREVIOUS = Path('/dev/shm/rc-lean-history-accepted-union-1497-20261010T204542.182773Z')
PROPOSAL = ROOT / 'proposals/reuse-integration-20261010T2138Z/PROPOSAL.json'
SECONDARY = ROOT / 'proposals/reuse-integration-20261010T2138Z/secondary-source/G6OriginalWholeEdgeChartConsumer.lean'
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
AUDIT = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
OVERLAY = '09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0'
AUTHENTICATED = 'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'


def allocation(roots):
    seen, total = set(), 0
    for root in roots:
        for directory, dirs, files in os.walk(root):
            for p in [Path(directory), *(Path(directory) / n for n in files)]:
                st = p.lstat()
                key = (st.st_dev, st.st_ino)
                if key not in seen:
                    seen.add(key)
                    total += st.st_blocks * 512
    return total


def link(source, output):
    output.parent.mkdir(parents=True, exist_ok=True)
    assert not output.exists() and not source.is_symlink()
    before = sha(source)
    try:
        os.link(source, output)
        mode = 'SAME_FILESYSTEM_HARD_LINK'
    except OSError as e:
        if e.errno != errno.EXDEV:
            raise
        shutil.copy2(source, output)
        mode = 'EXDEV_HASH_CHECKED_COPY2'
    assert sha(source) == sha(output) == before
    return {'source': str(source), 'destination': str(output), 'sha256': before, 'bytes': source.stat().st_size,
            'mode': mode, 'source_device_inode': [source.stat().st_dev, source.stat().st_ino],
            'destination_device_inode': [output.stat().st_dev, output.stat().st_ino]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repair-manifest', type=Path, required=True,
                        help='Exact attributed proposal derivatives; original six bodies stay unchanged.')
    args = parser.parse_args()
    repair_path = args.repair_manifest.resolve(strict=True)
    repairs = json.loads(repair_path.read_bytes())
    previous_attempts = sorted(Path('/dev/shm').glob('rc-lean-g7-survival-integration-*'))
    assert previous_attempts and all(not (p / 'ACTIVE-GUARDED-PROCESS.json').exists() for p in previous_attempts)
    assert sha(PROPOSAL) == '2add61f5af5d5ef900987f713fbe0ace1d3ff2b4b3ac15dc6153efc1accc2894'
    proposal = json.loads(PROPOSAL.read_bytes())
    prior_prep = json.loads((PREVIOUS / 'PREPARATION.json').read_bytes())
    old_graph = json.loads((PREVIOUS / 'DEPENDENCY-GRAPH.json').read_bytes())
    old = old_graph['targets']['current/connected']
    assert len(old['modules']) == 1497
    assert sha(PREVIOUS / 'DEPENDENCY-GRAPH.json') == 'b1cf28461bce4bfc2ba4adcf26e4eca4c76214783cf29e2557ce134db782838e'
    fresh = {}
    fresh_sources = {}
    for r in proposal['sources_in_dependency_order']:
        # Proposal current paths may receive explicitly versioned repairs. The
        # original proposal lineage always starts from its preserved old body.
        p = COMMONS / r['original_source']
        assert sha(p) == r['sha256']
        fresh[r['module']] = {'module': r['module'], 'sha256': r['sha256'], 'imports': r['imports']}
        fresh_sources[r['module']] = p
    secondary_original = next(p / 'source-store/20df02223f9c2c214056f50d4bfa43f7e68ee35a93aead431ef2a02bd81f1163.lean'
                              for p in previous_attempts
                              if (p / 'source-store/20df02223f9c2c214056f50d4bfa43f7e68ee35a93aead431ef2a02bd81f1163.lean').is_file())
    assert sha(secondary_original) == '20df02223f9c2c214056f50d4bfa43f7e68ee35a93aead431ef2a02bd81f1163'
    fresh['G6OriginalWholeEdgeChartConsumer'] = {'module': 'G6OriginalWholeEdgeChartConsumer',
        'sha256': sha(secondary_original), 'imports': ['G7OriginalSurvivalCoverage']}
    fresh_sources['G6OriginalWholeEdgeChartConsumer'] = secondary_original
    for module, repair in repairs['source_derivatives'].items():
        assert module in fresh
        source = Path(repair['path']).resolve(strict=True)
        assert source.is_relative_to(PROPOSAL.parent)
        assert sha(source) == repair['sha256']
        assert repair['imports'] == fresh[module]['imports']
        fresh[module] = {**fresh[module], 'sha256': repair['sha256']}
        fresh_sources[module] = source
    modules = {**old['modules'], **fresh}
    assert len(modules) == 1504
    order, visiting = [], set()
    def visit(m):
        if m in order or m not in modules:
            return
        assert m not in visiting, ('cycle', m)
        visiting.add(m)
        for dep in modules[m]['imports']:
            visit(dep)
        visiting.remove(m)
        order.append(m)
    def target(roots):
        nonlocal order
        order = []
        for m in roots:
            visit(m)
        return {'roots': roots, 'order': list(order), 'modules': {m: modules[m] for m in order},
                'required_for_accepted_release': False, 'status': 'PROPOSED_FRESH_KERNEL_AND_FULL_OWNED_AUDIT'}
    primary = target(['G7OriginalSurvivalCoverage'])
    secondary = target(['G6OriginalWholeEdgeChartConsumer'])
    union1503 = target(old['roots'] + ['G7OriginalSurvivalCoverage'])
    union1504 = target(old['roots'] + ['G6OriginalWholeEdgeChartConsumer'])
    assert [len(t['modules']) for t in [primary, secondary, union1503, union1504]] == [122, 123, 1503, 1504]
    graph = {'targets': {'recovery/g7-original-survival-six': primary,
                         'recovery/g6-whole-edge-chart-consumer': secondary,
                         'history/survival-library1503': union1503,
                         'current/connected': union1504},
             'scope': 'Exact accepted1497 library plus six unchanged historical G7 consumers and a separate two-proof G6 consumer. Each target requires its own fresh aggregate/full ownership audit.'}
    allocation_roots = [PREVIOUS, *previous_attempts]
    existing = allocation(allocation_roots)
    reserves = {'fresh_seven_attempt_and_cache_bundle_copies': 256 * 2**20,
                'two_minimal_root_runs_audits_and_metadata': 96 * 2**20,
                'one_full_coherent_run_and_raw_audit': 256 * 2**20,
                'source_transport_metadata_and_transient_writes': 64 * 2**20}
    total = existing + sum(reserves.values())
    assert total <= 2**31 and shutil.disk_usage('/dev/shm').free > sum(reserves.values())
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-lean-g7-survival-integration-' + stamp)
    evidence = work / 'evidence/preparation'
    evidence.mkdir(parents=True)
    (work / 'scripts').mkdir()
    save(work / 'DEPENDENCY-GRAPH.json', graph)
    source_transports = []
    closure = []
    for m, r in modules.items():
        source = fresh_sources[m] if m in fresh else PREVIOUS / 'source-store' / (r['sha256'] + '.lean')
        assert sha(source) == r['sha256']
        dest = work / 'source-store' / (r['sha256'] + '.lean')
        if not dest.exists():
            source_transports.append(link(source, dest))
        distributed = source if m in fresh else ROOT / 'evidence/proof-extensions/history-accepted-union-1497/20261010T204542.182773Z/sources' / (m.replace('.', '/') + '.lean')
        assert sha(distributed) == r['sha256']
        closure.append({'module': m, **r, 'scratch_source': str(dest), 'preserved_source': str(distributed)})
    save(work / 'SOURCE-CLOSURE.json', closure)
    save(work / 'SOURCE-TRANSPORT.json', source_transports)
    save(work / 'FRESH-SOURCES.json', fresh)
    selected = []
    for entry in sorted((PREVIOUS / '.build/cache').iterdir()):
        receipt = entry / 'receipt.json'
        r = json.loads(receipt.read_bytes())
        assert r['module'] in old['modules'] and r['source_sha256'] == old['modules'][r['module']]['sha256']
        selected.append({'module': r['module'], 'source_sha256': r['source_sha256'],
            'source_path': str(PREVIOUS / 'source-store' / (r['source_sha256'] + '.lean')),
            'cache_entry': str(entry), 'cache_key': entry.name, 'receipt_sha256': sha(receipt),
            'cached_object': r['cached_object'], 'object_artifacts': r['object_artifacts']})
    assert len(selected) == 1497 and {r['module'] for r in selected} == set(old['modules'])
    selected_by_module = {r['module']: r for r in selected}
    partial_admissions = []
    for module in union1504['order']:
        if module not in fresh:
            continue
        for prior in reversed(previous_attempts):
            chosen = None
            for entry in sorted((prior / '.build/cache').glob('*')):
                receipt = entry / 'receipt.json'
                if not receipt.exists():
                    continue
                rec = json.loads(receipt.read_bytes())
                if (rec.get('module'), rec.get('source_sha256'), rec.get('kind'), rec.get('status')) != \
                        (module, fresh[module]['sha256'], 'component', 'PASS_FRESH_KERNEL_CHECK'):
                    continue
                if set(rec['direct_import_bindings']) != set(fresh[module]['imports']):
                    continue
                owned_deps = [d for d in fresh[module]['imports'] if d in modules]
                if any(d not in selected_by_module or
                       rec['direct_import_artifacts'][d] != selected_by_module[d]['object_artifacts']
                       for d in owned_deps):
                    continue
                chosen = {'module': module, 'source_sha256': rec['source_sha256'],
                    'source_path': str(prior / 'source-store' / (rec['source_sha256'] + '.lean')),
                    'cache_entry': str(entry), 'cache_key': entry.name, 'receipt_sha256': sha(receipt),
                    'cached_object': rec['cached_object'], 'object_artifacts': rec['object_artifacts'],
                    'provenance': 'Exact kernel-checked component from a preserved partial prior run; no accepted proof-root assertion.'}
                break
            if chosen:
                selected.append(chosen)
                selected_by_module[module] = chosen
                partial_admissions.append(chosen)
                break
    save(work / 'SELECTED-CACHE-IDENTITIES.json', selected)
    save(work / 'PARTIAL-COMPONENT-ADMISSION-PROVENANCE.json', partial_admissions)
    wrappers = ROOT / prior_prep['cache_install_transport_derivation']['evidence']
    for source, name, expected in [(PREVIOUS / 'scripts/build_connected.py', 'build_connected.py', CORE),
            (PREVIOUS / 'scripts/AuditTemplate.lean', 'AuditTemplate.lean', AUDIT),
            (wrappers / 'ORIGINAL-NAMESPACE-OVERLAY.py', 'build_with_mathlib_overlay.py', OVERLAY),
            (wrappers / 'ORIGINAL-AUTHENTICATED-OVERLAY.py', 'build_with_authenticated_overlay.py', AUTHENTICATED)]:
        assert sha(source) == expected
        shutil.copyfile(source, work / 'scripts' / name)
    for name in ['check_core.py', 'seed_exact_cache.py', 'guard_g7_survival_run_20261010_v2.py']:
        shutil.copyfile(ROOT / 'scripts' / name, work / 'scripts' / name)
    shutil.copytree(PREVIOUS / 'third-party', work / 'third-party')
    # Only the coverage assertion changes: the seven absent keys must be exactly
    # the explicitly pinned fresh-source partition. All warm admission code stays.
    seeder_source = ROOT / 'scripts/seed_exact_cache_transport.py'
    seeder = seeder_source.read_text()
    old_assert = '    assert len(identities) == len(selected)\n    assert {row["module"] for row in identities} == set(selected)'
    new_assert = '''    fresh = json.loads((destination / 'FRESH-SOURCES.json').read_bytes())
    warm = {row['module'] for row in identities}
    assert 1497 <= len(identities) <= 1504 and len(warm) == len(identities) and len(fresh) == 7
    assert warm <= set(selected) and len(warm - set(fresh)) == 1497
    assert set(selected) - warm <= set(fresh)
    assert all(selected[m] == row for m, row in fresh.items())'''
    assert seeder.count(old_assert) == 1
    seeder = seeder.replace(old_assert, new_assert)
    installer_source = ROOT / 'scripts/prepare_cache_install_transport_history_1497.py'
    installer = installer_source.read_text()
    old_assert = '    assert len(selected) == len(owned) and {r["module"] for r in selected} == set(owned)'
    new_assert = '''    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    warm = {r['module'] for r in selected}
    assert 1497 <= len(selected) <= 1504 and len(warm) == len(selected) and len(fresh) == 7
    assert warm <= set(owned) and len(warm - set(fresh)) == 1497
    assert set(owned) - warm <= set(fresh)
    assert all(owned[m] == row for m, row in fresh.items())'''
    assert installer.count(old_assert) == 1
    installer = installer.replace(old_assert, new_assert).replace('CACHE-INSTALL-TRANSPORT-HISTORY-1497-DERIVATION.json', 'CACHE-INSTALL-TRANSPORT-G7-SURVIVAL-DERIVATION.json')
    for name, text in [('seed_g7_survival_cache.py', seeder), ('prepare_g7_survival_install.py', installer)]:
        compile(text, name, 'exec')
        (work / 'scripts' / name).write_text(text)
    budget = {'all_prior1497_and_G7_attempts_distinct_inode_allocated_bytes': existing, 'new_allocation_reserves': reserves,
              'planned_combined_allocation_bound_bytes': total, 'combined_scratch_limit_bytes': 2**31,
              'abort_at_bytes_with_transient_headroom': 2**31 - 128 * 2**20,
              'memory_nonreclaimable_abort_bytes': 15 * 2**30, 'monitor_poll_seconds': 0.5,
              'packet_lossless_export_reserved_bytes': 40 * 2**20,
              'packet_lossless_export_constraint': 'Measure gzip bytes before writing packet; raw audits stay at fixed scratch paths. Prior1497 full source closure is already distributed and linked by exact source hashes.'}
    derivation = {'status': 'PRE_USE_DATED_G7_SOURCE_COMPOSITION_AND_REVISED_STORAGE_POLICY',
        'contributor': 'Codex / lean_integration_successor', 'workspace': str(work),
        'preparer_sha256': sha(Path(__file__)), 'parent1497_workspace': str(PREVIOUS),
        'parent1497_preparation_sha256': sha(PREVIOUS / 'PREPARATION.json'),
        'parent1497_certificate': str(ROOT / 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json'),
        'parent1497_certificate_sha256': sha(ROOT / 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json'),
        'primary_proposal_sha256': sha(PROPOSAL), 'fresh_sources': fresh, 'budget': budget,
        'source_repair_manifest': str(repair_path), 'source_repair_manifest_sha256': sha(repair_path),
        'preserved_prior_G7_workspaces': [str(p) for p in previous_attempts],
        'partial_kernel_component_admissions': partial_admissions,
        'prior_1GiB_policy_origin': 'Self-imposed operational1497 scratch budget; retained unchanged. Root authorized a revised2GiB total policy for this dated continuation.',
        'graph_partition': {'primary': 122, 'secondary': 123, 'full_without_secondary': 1503, 'full_with_secondary': 1504,
                            'warm_authenticated_old': 1497, 'fresh_primary': 6, 'fresh_secondary': 1},
        'original_seeder_path': str(seeder_source), 'original_seeder_sha256': sha(seeder_source),
        'derived_seeder_sha256': sha(work / 'scripts/seed_g7_survival_cache.py'),
        'original_install_preparer_path': str(installer_source), 'original_install_preparer_sha256': sha(installer_source),
        'derived_install_preparer_sha256': sha(work / 'scripts/prepare_g7_survival_install.py'),
        'transport_helper_derivation': 'Only replace exact full-coverage assertions with an exact1497 warm/seven pinned fresh partition; installer output filename is uniquely dated. ROOT follows isolated scripts path, so transport evidence stays in scratch.',
        'core_kernel_flags_mathlib_guards_resource_caps_changed': False,
        'original_sources_receipts_native_or_accepted_evidence_written': False, 'compiler_launched': False}
    prep = {'status': 'PREPARED_UNCOMPILED_G7_SURVIVAL_CONTINUATION', 'workspace': str(work), 'evidence': str(evidence),
        'targets': list(graph['targets']), 'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'),
        'contexts': [{'workspace': str(PREVIOUS), 'target': 'current/connected', 'graph_sha256': sha(PREVIOUS / 'DEPENDENCY-GRAPH.json'),
                      'selected_modules': 1497, 'provenance': 'Accepted predecessor context; not a claim the new sources have compiled.'}],
        'derivatives': [{'module': m, **r, 'attributed_source_author': 'Codex / lean_reuse_successor'}
                        for m, r in repairs['source_derivatives'].items()],
        'source_versions_and_literal_imports_pinned': True, 'source_pins': {m:r['sha256'] for m,r in modules.items()},
        'builder_sha256': CORE, 'audit_template_sha256': AUDIT, 'official_complete_mathlib_namespace_overlay': True,
        'namespace_overlay_wrapper_sha256': OVERLAY, 'optimized_overlay_sha256': AUTHENTICATED,
        'namespace_adapter_derivation': prior_prep['namespace_adapter_derivation'],
        'scratch_location_derivation': derivation, 'historical_passes_copied': False, 'native_execution_claimed': False}
    save(work / 'PREPARATION.json', prep)
    save(evidence / 'PREPARATION.json', prep)
    save(work / 'LOCATION-AND-COMPOSITION-DERIVATION.json', derivation)
    selection = str(work / 'SELECTED-CACHE-IDENTITIES.json')
    for script in ['seed_g7_survival_cache.py', 'prepare_g7_survival_install.py']:
        subprocess.run([sys.executable, str(work / 'scripts' / script), str(work), '--selection-manifest', selection], check=True)
    phases = {'primary': {'target': 'recovery/g7-original-survival-six', 'requires': []},
              'secondary': {'target': 'recovery/g6-whole-edge-chart-consumer', 'requires': ['primary']},
              'union1503': {'target': 'history/survival-library1503', 'requires': ['primary'], 'status': 'PROSPECTIVE_ONLY_DO_NOT_EXECUTE'},
              'union1504': {'target': 'current/connected', 'requires': ['primary', 'secondary']}}
    plan = {'status': 'READY_FOR_ROOT_PLAN_REVIEW_NO_COMPILER_LAUNCHED', 'workspace': str(work),
        'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'), 'preparation_sha256': sha(work / 'PREPARATION.json'),
        'monitor_sha256': sha(work / 'scripts/guard_g7_survival_run_20261010_v2.py'),
        'monitor_path': str(work / 'scripts/guard_g7_survival_run_20261010_v2.py'),
        'python': sys.executable, 'launcher': str(ROOT / 'scripts/run_proof_extensions.py'),
        'launcher_sha256': sha(ROOT / 'scripts/run_proof_extensions.py'),
        'lean_bin': '/workspace/toolchains/lean-4.33.1-linux/bin', 'mathlib': '/workspace/dependencies/mathlib4',
        'phases': phases, 'allocation_roots': [str(p) for p in [*allocation_roots, work]],
        'scratch_abort_bytes': budget['abort_at_bytes_with_transient_headroom'],
        'scratch_hard_limit_bytes': 2**31, 'memory_abort_bytes': budget['memory_nonreclaimable_abort_bytes'],
        'budget': budget, 'compiler_launched': False,
        'normal_compiler_caps': 'Unchanged original4GiB/180s; -j1 -t0 -Ddebug.skipKernelTC=false',
        'full_coherent_caps': 'Unchanged current/connected6GiB/300s; no core changes',
        'preservation': 'No objects or duplicate1497 sources exported. Lossless gzip retains raw SHA bindings; full original scratch files stay at fixed paths.'}
    save(work / 'RESOURCE-AND-RUN-PLAN.json', plan)
    shutil.copyfile(Path(__file__), evidence / 'PREPARER.py')
    packet = ROOT / ('G7-SURVIVAL-INTEGRATION-PREPARATION-' + stamp + '.json')
    save(packet, {'status': plan['status'], 'workspace': str(work), 'evidence': str(evidence),
                  'plan_path': str(work / 'RESOURCE-AND-RUN-PLAN.json'), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
                  'preparer_sha256': sha(Path(__file__)), 'graph_sha256': plan['graph_sha256'],
                  'preparation_sha256': plan['preparation_sha256'], 'budget': budget})
    print(json.dumps({'workspace': str(work), 'packet_preparation': str(packet), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
                      'preparer_sha256': sha(Path(__file__)), 'monitor_sha256': plan['monitor_sha256'], 'budget': budget}))


if __name__ == '__main__':
    main()
