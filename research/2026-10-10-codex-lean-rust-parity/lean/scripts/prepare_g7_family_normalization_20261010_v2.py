#!/usr/bin/env python3
"""Freeze one new family consumer over the accepted 1504 exact local context.

Contributor: Codex / lean_integration_successor, 2026-10-10.
Only the minimal 168-module target is prepared. This script never runs Lean.
The original strict builder, namespace providers, flags and caps are retained.
"""
from __future__ import annotations

import datetime
import errno
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
PARENT = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
FREEZE = ROOT / 'proposals/reuse-integration-20261010T2138Z/family-normalization/PROPOSAL-FREEZE.json'
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
AUDIT = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
OVERLAY = '09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0'
AUTH = 'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'
GUARD = '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4'


def allocated(roots):
    seen, total = set(), 0
    for root in roots:
        for directory, _, files in os.walk(root):
            for path in [Path(directory), *(Path(directory) / n for n in files)]:
                stat = path.lstat()
                key = (stat.st_dev, stat.st_ino)
                if key not in seen:
                    seen.add(key)
                    total += stat.st_blocks * 512
    return total


def link(source, destination):
    source = Path(source)
    expected = sha(source)
    destination.parent.mkdir(parents=True, exist_ok=True)
    assert not destination.exists()
    try:
        os.link(source, destination)
        mode = 'SAME_FILESYSTEM_HARD_LINK'
        assert (source.stat().st_dev, source.stat().st_ino) == (destination.stat().st_dev, destination.stat().st_ino)
    except OSError as error:
        if error.errno != errno.EXDEV:
            raise
        shutil.copy2(source, destination)
        mode = 'EXDEV_HASH_CHECKED_COPY2'
    assert sha(source) == sha(destination) == expected
    return {'source': str(source), 'destination': str(destination), 'sha256': expected,
            'bytes': source.stat().st_size, 'transport': mode}


def main():
    proposal = json.loads(FREEZE.read_bytes())
    assert sha(FREEZE) == 'b36eb33a1a0a857928c04b6d5b5c95699d231d6913ca1fb532f8dfe6c56d87e5'
    for key in ['accepted_parent_certificate', 'independent_parent_QC']:
        assert sha(Path(proposal[key]['path'])) == proposal[key]['sha256']
    graph_path = PARENT / 'DEPENDENCY-GRAPH.json'
    parent_graph = json.loads(graph_path.read_bytes())
    parent = parent_graph['targets']['current/connected']
    parent_prep = json.loads((PARENT / 'PREPARATION.json').read_bytes())
    parent_plan = json.loads((PARENT / 'RESOURCE-AND-RUN-PLAN.json').read_bytes())
    assert len(parent['modules']) == 1504
    pins = proposal['literal_import_closure']['source_pins']
    assert len(pins) == 167 and len({r['module'] for r in pins}) == 167
    modules = {}
    for row in pins:
        module = row['module']
        original = parent['modules'][module]
        assert (original['sha256'], original['imports']) == (row['sha256'], row['imports'])
        assert sha(Path(row['source_path'])) == row['sha256']
        modules[module] = original
    source = Path(proposal['immutable_source_path'])
    assert sha(source) == proposal['sha256'] == '81dcd9983e73eecd5f59caac14ee6231825fdd9ae25dd9cf64bafbc06b6f2f08'
    module = proposal['module']
    imports = re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)', source.read_text(), re.M)
    assert imports == proposal['imports']
    fresh = {module: {'module': module, 'sha256': proposal['sha256'], 'imports': imports}}
    modules.update(fresh)
    order, seen, active = [], set(), set()

    def visit(name):
        if name in seen:
            return
        assert name not in active
        active.add(name)
        for dependency in modules[name]['imports']:
            if dependency in modules:
                visit(dependency)
            else:
                assert dependency in {'Init', 'Std', 'Lean', 'Mathlib'} or dependency.startswith(('Init.', 'Std.', 'Lean.', 'Mathlib.'))
        active.remove(name)
        seen.add(name)
        order.append(name)

    visit(module)
    assert len(order) == len(modules) == 168
    assert order[:-1] == proposal['literal_import_closure']['order']
    label = 'extraction/g7-original-family-calendar-normalization'
    target = {'roots': [module], 'order': order, 'modules': modules,
              'required_for_accepted_release': False, 'status': 'UNCOMPILED_EXACT_PROOF_EXTENSION'}
    graph = {'targets': {label: target}, 'scope': 'Minimal exact accepted1504 closure plus one new supplied-calendar family consumer; no full union or runtime acceptance is copied.'}
    roots = list(parent_plan['allocation_roots'])
    roots += [str(p) for p in sorted(Path('/dev/shm').glob('rc-lean-g7-family-normalization-*')) if p.is_dir()]
    roots = list(dict.fromkeys(roots))
    existing = allocated(roots)
    reserves = {'fresh_component_and_companion_cache': 64 * 2**20,
                'minimal_aggregate_and_complete_raw_owned_audit': 96 * 2**20,
                'source_cache_transport_metadata_and_transient_writes': 64 * 2**20,
                'lossless_export_staging': 32 * 2**20}
    bound = existing + sum(reserves.values())
    assert bound < 2**31 - 128 * 2**20
    assert shutil.disk_usage('/dev/shm').free > sum(reserves.values())
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work = Path('/dev/shm') / ('rc-lean-g7-family-normalization-' + stamp)
    evidence = work / 'evidence/preparation'
    evidence.mkdir(parents=True)
    (work / 'scripts').mkdir()
    save(work / 'DEPENDENCY-GRAPH.json', graph)
    save(work / 'FRESH-SOURCES.json', fresh)
    source_records, closure = [], []
    pin_by_module = {r['module']: r for r in pins}
    for name in order:
        row = modules[name]
        original = source if name == module else PARENT / 'source-store' / (row['sha256'] + '.lean')
        assert sha(original) == row['sha256']
        dest = work / 'source-store' / (row['sha256'] + '.lean')
        if not dest.exists():
            source_records.append(link(original, dest))
        preserved = source if name == module else Path(pin_by_module[name]['source_path'])
        closure.append({**row, 'scratch_source': str(dest), 'preserved_source': str(preserved)})
    save(work / 'SOURCE-CLOSURE.json', closure)
    save(work / 'SOURCE-TRANSPORT.json', source_records)
    cache_by_module = {}
    for entry in (PARENT / '.build/cache').iterdir():
        receipt = entry / 'receipt.json'
        rec = json.loads(receipt.read_bytes())
        if rec['module'] not in modules or rec['module'] == module:
            continue
        assert rec['module'] not in cache_by_module
        assert rec['source_sha256'] == modules[rec['module']]['sha256']
        cache_by_module[rec['module']] = {'module': rec['module'], 'source_sha256': rec['source_sha256'],
            'source_path': str(work / 'source-store' / (rec['source_sha256'] + '.lean')),
            'cache_entry': str(entry), 'cache_key': entry.name, 'receipt_sha256': sha(receipt),
            'cached_object': rec['cached_object'], 'object_artifacts': rec['object_artifacts']}
    assert len(cache_by_module) == 167 and set(cache_by_module) == set(modules) - {module}
    selected = [cache_by_module[n] for n in order[:-1]]
    save(work / 'SELECTED-CACHE-IDENTITIES.json', selected)
    wrappers = PARENT / parent_prep['cache_install_transport_derivation']['evidence']
    for original, name, expected in [
        (PARENT / 'scripts/build_connected.py', 'build_connected.py', CORE),
        (PARENT / 'scripts/AuditTemplate.lean', 'AuditTemplate.lean', AUDIT),
        (wrappers / 'ORIGINAL-NAMESPACE-OVERLAY.py', 'build_with_mathlib_overlay.py', OVERLAY),
        (wrappers / 'ORIGINAL-AUTHENTICATED-OVERLAY.py', 'build_with_authenticated_overlay.py', AUTH)]:
        assert sha(original) == expected
        shutil.copyfile(original, work / 'scripts' / name)
    for name in ['check_core.py', 'seed_exact_cache.py']:
        shutil.copyfile(ROOT / 'scripts' / name, work / 'scripts' / name)
    shutil.copytree(PARENT / 'third-party', work / 'third-party')
    seeder_original = ROOT / 'scripts/seed_exact_cache_transport.py'
    installer_original = ROOT / 'scripts/prepare_cache_install_transport_history_1497.py'
    seeder = seeder_original.read_text()
    before = '    assert len(identities) == len(selected)\n    assert {row["module"] for row in identities} == set(selected)'
    after = '''    fresh = json.loads((destination / 'FRESH-SOURCES.json').read_bytes())
    warm = {row['module'] for row in identities}
    assert len(selected) == 168 and len(identities) == len(warm) == 167 and len(fresh) == 1
    assert warm == set(selected) - set(fresh)
    assert all(selected[m] == row for m, row in fresh.items())'''
    assert seeder.count(before) == 1
    seeder = seeder.replace(before, after)
    installer = installer_original.read_text()
    before = '    assert len(selected) == len(owned) and {r["module"] for r in selected} == set(owned)'
    after = '''    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    warm = {r['module'] for r in selected}
    assert len(owned) == 168 and len(selected) == len(warm) == 167 and len(fresh) == 1
    assert warm == set(owned) - set(fresh)
    assert all(owned[m] == row for m, row in fresh.items())'''
    assert installer.count(before) == 1
    installer = installer.replace(before, after).replace('CACHE-INSTALL-TRANSPORT-HISTORY-1497-DERIVATION.json', 'CACHE-INSTALL-TRANSPORT-G7-FAMILY168-DERIVATION.json')
    guard_original = ROOT / 'scripts/guard_g7_survival_run_20261010_v2.py'
    assert sha(guard_original) == GUARD
    guard = guard_original.read_text()
    before = "choices=['primary', 'secondary', 'union1503', 'union1504']"
    assert guard.count(before) == 1
    guard = guard.replace(before, "choices=['family']")
    for name, text in [('seed_g7_family_cache.py', seeder), ('prepare_g7_family_install.py', installer), ('guard_g7_family_normalization_20261010.py', guard)]:
        compile(text, name, 'exec')
        (work / 'scripts' / name).write_text(text)
    budget = {'prior1497_and_all_G7_contexts_distinct_inode_allocated_bytes': existing,
        'new_allocation_reserves': reserves, 'planned_combined_allocation_bound_bytes': bound,
        'combined_scratch_limit_bytes': 2**31, 'abort_at_bytes_with_transient_headroom': 2**31 - 128 * 2**20,
        'memory_nonreclaimable_abort_bytes': 15 * 2**30, 'monitor_poll_seconds': 0.5,
        'packet_export_policy': 'Measure exact lossless gzip allocation before writing; existing parent sources remain referenced by immutable distributed path/hash, raw audit stays fixed in shmem; no ELF or duplicate object export.'}
    derivation = {'status': 'PRE_USE_MINIMAL_FAMILY168_LOCATION_AND_TRANSPORT_DERIVATION',
        'preparer_sha256': sha(Path(__file__)), 'parent_workspace': str(PARENT),
        'parent_graph_sha256': sha(graph_path), 'parent_preparation_sha256': sha(PARENT / 'PREPARATION.json'),
        'parent_certificate': proposal['accepted_parent_certificate'], 'parent_QC': proposal['independent_parent_QC'],
        'proposal_freeze_path': str(FREEZE), 'proposal_freeze_sha256': sha(FREEZE),
        'source_partition': {'accepted_exact_parent_modules': 167, 'fresh_modules': fresh, 'total': 168},
        'original_seeder_path': str(seeder_original), 'original_seeder_sha256': sha(seeder_original),
        'derived_seeder_sha256': sha(work / 'scripts/seed_g7_family_cache.py'),
        'original_install_preparer_path': str(installer_original), 'original_install_preparer_sha256': sha(installer_original),
        'derived_install_preparer_sha256': sha(work / 'scripts/prepare_g7_family_install.py'),
        'original_guard_path': str(guard_original), 'original_guard_sha256': GUARD,
        'derived_guard_sha256': sha(work / 'scripts/guard_g7_family_normalization_20261010.py'),
        'guard_derivation': 'Replace only four prior phase labels with family. All prelaunch pins, cleanup, final gates, memory/storage thresholds and child grouping are unchanged.',
        'transport_derivation': 'Only exact coverage assertions change to 167 authenticated warm + one pinned fresh; installer metadata filename changes. Existing cache admission, install, copy/hash policy and original receipts remain unchanged.',
        'budget': budget, 'original_sources_receipts_native_or_accepted_evidence_written': False,
        'compiler_flags_caps_core_mathlib_guards_audit_changed': False, 'compiler_launched': False}
    prep = {'status': 'PREPARED_UNCOMPILED_G7_FAMILY_NORMALIZATION168', 'workspace': str(work), 'evidence': str(evidence),
        'targets': [label], 'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'),
        'contexts': [{'workspace': str(PARENT), 'target': 'current/connected', 'graph_sha256': sha(graph_path),
                      'selected_modules': 167, 'provenance': 'Selected exact accepted parent components; no new target acceptance is copied.'}],
        'derivatives': [{'module': module, 'source': str(source), 'source_sha256': proposal['sha256'], 'replaces_original_sha256': None}],
        'source_versions_and_literal_imports_pinned': True, 'source_pins': {n: r['sha256'] for n,r in modules.items()},
        'builder_sha256': CORE, 'audit_template_sha256': AUDIT, 'official_complete_mathlib_namespace_overlay': True,
        'namespace_overlay_wrapper_sha256': OVERLAY, 'optimized_overlay_sha256': AUTH,
        'namespace_adapter_derivation': parent_prep['namespace_adapter_derivation'],
        'scratch_location_derivation': derivation, 'historical_passes_copied': False, 'native_execution_claimed': False}
    save(work / 'PREPARATION.json', prep)
    save(evidence / 'PREPARATION.json', prep)
    save(work / 'LOCATION-AND-COMPOSITION-DERIVATION.json', derivation)
    selection = str(work / 'SELECTED-CACHE-IDENTITIES.json')
    for script in ['seed_g7_family_cache.py', 'prepare_g7_family_install.py']:
        subprocess.run([sys.executable, str(work / 'scripts' / script), str(work), '--selection-manifest', selection], check=True)
    plan = {'status': 'READY_FOR_ROOT_PLAN_REVIEW_NO_COMPILER_LAUNCHED', 'workspace': str(work),
        'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'), 'preparation_sha256': sha(work / 'PREPARATION.json'),
        'monitor_sha256': sha(work / 'scripts/guard_g7_family_normalization_20261010.py'),
        'monitor_path': str(work / 'scripts/guard_g7_family_normalization_20261010.py'),
        'python': sys.executable, 'launcher': str(ROOT / 'scripts/run_proof_extensions.py'),
        'launcher_sha256': sha(ROOT / 'scripts/run_proof_extensions.py'),
        'lean_bin': '/workspace/toolchains/lean-4.33.1-linux/bin', 'mathlib': '/workspace/dependencies/mathlib4',
        'phases': {'family': {'target': label, 'requires': []}}, 'allocation_roots': [*roots, str(work)],
        'scratch_abort_bytes': 2**31 - 128 * 2**20, 'scratch_hard_limit_bytes': 2**31,
        'memory_abort_bytes': 15 * 2**30, 'budget': budget, 'compiler_launched': False,
        'normal_compiler_caps': 'Unchanged original4GiB/180s; -j1 -t0 -Ddebug.skipKernelTC=false',
        'preservation': budget['packet_export_policy']}
    save(work / 'RESOURCE-AND-RUN-PLAN.json', plan)
    shutil.copyfile(Path(__file__), evidence / 'PREPARER.py')
    packet = ROOT / ('G7-FAMILY-NORMALIZATION-PREPARATION-' + stamp + '.json')
    save(packet, {'status': plan['status'], 'workspace': str(work), 'evidence': str(evidence),
        'plan_path': str(work / 'RESOURCE-AND-RUN-PLAN.json'), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
        'preparer_sha256': sha(Path(__file__)), 'graph_sha256': plan['graph_sha256'],
        'preparation_sha256': plan['preparation_sha256'], 'budget': budget})
    print(json.dumps({'workspace': str(work), 'packet_preparation': str(packet), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
        'preparer_sha256': sha(Path(__file__)), 'monitor_sha256': plan['monitor_sha256'], 'budget': budget}))


if __name__ == '__main__':
    main()
