#!/usr/bin/env python3
"""Freeze one new parallel-arm transport consumer over the accepted 1504 exact local context.

Contributor: Codex / lean_integration_successor, 2026-10-10.
Only the minimal117 proof target is executable; four protected namespace provider records are additionally staged. This script never runs Lean.
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
REPOSITORY = ROOT.parents[2]
PARENT = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
FREEZE = ROOT / 'proposals/reuse-integration-20261010T2138Z/parallel-arm-transport/PROPOSAL-FREEZE.json'
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
    assert sha(FREEZE) == '73e28655aa7277e838c37bf84e56bfe275e5fc592ddc137baa6ce66c99cdb24b'
    accepted = proposal['accepted_provider_context']
    for key in ['certificate', 'root_qc']:
        assert sha(REPOSITORY / accepted[key]) == accepted[key + '_sha256']
    graph_path = PARENT / 'DEPENDENCY-GRAPH.json'
    parent_graph = json.loads(graph_path.read_bytes())
    parent = parent_graph['targets']['current/connected']
    parent_prep = json.loads((PARENT / 'PREPARATION.json').read_bytes())
    parent_plan = json.loads((PARENT / 'RESOURCE-AND-RUN-PLAN.json').read_bytes())
    assert len(parent['modules']) == 1504
    pins = [{**r, 'source_path': str(REPOSITORY / r['accepted_source'])}
            for r in accepted['providers']]
    assert len(pins) == 116 and len({r['module'] for r in pins}) == 116
    modules = {}
    for row in pins:
        module = row['module']
        original = parent['modules'][module]
        assert (original['sha256'], original['imports']) == (row['sha256'], row['imports'])
        assert sha(Path(row['source_path'])) == row['sha256']
        modules[module] = original
    source_pin = proposal['source']
    source = REPOSITORY / source_pin['immutable_version']
    assert sha(source) == sha(REPOSITORY / source_pin['path']) == source_pin['sha256'] == 'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc'
    module = source_pin['module']
    imports = re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)', source.read_text(), re.M)
    assert imports == source_pin['imports']
    fresh = {module: {'module': module, 'sha256': source_pin['sha256'], 'imports': imports}}
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
    assert len(order) == len(modules) == 117
    assert order[:-1] == [r['module'] for r in pins]
    label = proposal['intended_target']['suggested_target']
    target = {'roots': [module], 'order': order, 'modules': {n: modules[n] for n in order},
              'required_for_accepted_release': False, 'status': 'UNCOMPILED_EXACT_PROOF_EXTENSION'}
    protected = {n: r for n,r in parent['modules'].items() if n.startswith('Mathlib.')}
    assert len(protected) == 4 and not (set(protected) & set(modules))
    guard_order = [n for n in parent['order'] if n in protected]
    modules.update(protected)
    guards = {'roots': guard_order, 'order': guard_order, 'modules': protected,
        'required_for_accepted_release': False, 'status': 'PROTECTED_NAMESPACE_CONTEXT_ONLY_NOT_EXECUTED'}
    graph = {'targets': {label: target, 'context/protected-mathlib-providers': guards},
        'scope': '117-module executable parallel-arm transport root plus four exact accepted protected namespace providers. Overall staging graph121; provider context is not requested for execution or claimed as a new proof root.'}
    staging_order = order + guard_order
    roots = list(parent_plan['allocation_roots'])
    roots += [str(p) for pattern in ['rc-lean-g7-family-normalization-*', 'rc-lean-g6-parallel-arm-transport-*']
              for p in sorted(Path('/dev/shm').glob(pattern)) if p.is_dir()]
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
    work = Path('/dev/shm') / ('rc-lean-g6-parallel-arm-transport-' + stamp)
    evidence = work / 'evidence/preparation'
    evidence.mkdir(parents=True)
    (work / 'scripts').mkdir()
    save(work / 'DEPENDENCY-GRAPH.json', graph)
    save(work / 'FRESH-SOURCES.json', fresh)
    source_records, closure = [], []
    pin_by_module = {r['module']: r for r in pins}
    parent_closure = {r['module']: r for r in json.loads((PARENT / 'SOURCE-CLOSURE.json').read_bytes())}
    for name in staging_order:
        row = modules[name]
        original = source if name == module else PARENT / 'source-store' / (row['sha256'] + '.lean')
        assert sha(original) == row['sha256']
        dest = work / 'source-store' / (row['sha256'] + '.lean')
        if not dest.exists():
            source_records.append(link(original, dest))
        preserved = source if name == module else Path(pin_by_module[name]['source_path'] if name in pin_by_module else parent_closure[name]['preserved_source'])
        assert sha(preserved) == row['sha256']
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
    assert len(cache_by_module) == 120 and set(cache_by_module) == set(modules) - {module}
    selected = [cache_by_module[n] for n in staging_order if n != module]
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
    assert len(selected) == 121 and len(identities) == len(warm) == 120 and len(fresh) == 1
    assert warm == set(selected) - set(fresh)
    assert all(selected[m] == row for m, row in fresh.items())'''
    assert seeder.count(before) == 1
    seeder = seeder.replace(before, after)
    installer = installer_original.read_text()
    before = '    assert len(selected) == len(owned) and {r["module"] for r in selected} == set(owned)'
    after = '''    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    warm = {r['module'] for r in selected}
    assert len(owned) == 121 and len(selected) == len(warm) == 120 and len(fresh) == 1
    assert warm == set(owned) - set(fresh)
    assert all(owned[m] == row for m, row in fresh.items())'''
    assert installer.count(before) == 1
    installer = installer.replace(before, after).replace('CACHE-INSTALL-TRANSPORT-HISTORY-1497-DERIVATION.json', 'CACHE-INSTALL-TRANSPORT-G6-PARALLEL117-DERIVATION.json')
    guard_original = ROOT / 'scripts/guard_g7_survival_run_20261010_v2.py'
    assert sha(guard_original) == GUARD
    guard = guard_original.read_text()
    before = "choices=['primary', 'secondary', 'union1503', 'union1504']"
    assert guard.count(before) == 1
    guard = guard.replace(before, "choices=['parallel']")
    for name, text in [('seed_g6_parallel_cache.py', seeder), ('prepare_g6_parallel_install.py', installer), ('guard_g6_parallel_arm_transport_20261010.py', guard)]:
        compile(text, name, 'exec')
        (work / 'scripts' / name).write_text(text)
    budget = {'prior1497_and_all_G7_contexts_distinct_inode_allocated_bytes': existing,
        'new_allocation_reserves': reserves, 'planned_combined_allocation_bound_bytes': bound,
        'combined_scratch_limit_bytes': 2**31, 'abort_at_bytes_with_transient_headroom': 2**31 - 128 * 2**20,
        'memory_nonreclaimable_abort_bytes': 15 * 2**30, 'monitor_poll_seconds': 0.5,
        'packet_export_policy': 'Pre-stage exact lossless gzip/text evidence in the fixed new shmem context. Copy to the packet only when measured portable bytes plus8MiB reserve fit live overlay capacity; otherwise retain the complete fixed shmem export and save a small explicit distribution manifest, without silent omission. Parent sources are linked by existing immutable distributed paths/hashes; raw audits remain fixed shmem originals. No ELF, objects or duplicate parent source export.',
        'overlay_free_bytes_at_preparation': shutil.disk_usage(str(ROOT)).free,
        'packet_export_transient_reserve_bytes': 8 * 2**20,
        'prospective_overlay_portable_byte_ceiling': max(0, shutil.disk_usage(str(ROOT)).free - 8 * 2**20)}
    derivation = {'status': 'PRE_USE_MINIMAL_PARALLEL117_LOCATION_AND_TRANSPORT_DERIVATION',
        'preparer_sha256': sha(Path(__file__)), 'parent_workspace': str(PARENT),
        'parent_graph_sha256': sha(graph_path), 'parent_preparation_sha256': sha(PARENT / 'PREPARATION.json'),
        'parent_certificate': {'path': str(REPOSITORY / accepted['certificate']), 'sha256': accepted['certificate_sha256']},
        'parent_QC': {'path': str(REPOSITORY / accepted['root_qc']), 'sha256': accepted['root_qc_sha256']},
        'proposal_freeze_path': str(FREEZE), 'proposal_freeze_sha256': sha(FREEZE),
        'source_partition': {'executable_accepted_parent_modules': 116, 'protected_provider_records': protected, 'staged_warm': 120, 'fresh_modules': fresh, 'executed_total': 117, 'guard_complete_staging_graph': 121},
        'guard_complete_context_policy': 'Retain all four required accepted Mathlib provider records in a nonexecuted provider context from the beginning. Exact accepted Family-v3 namespace staging precedent; no guard omission or wrapper/core/assertion relaxation.',
        'preparer_derivation_base': {'path': str(ROOT / 'scripts/prepare_g7_family_normalization_20261010_v3.py'), 'sha256': '362fb7c8b0757328717ce55d4914b61304d96999997c04a570a82ad5dd6d9347'},
        'original_seeder_path': str(seeder_original), 'original_seeder_sha256': sha(seeder_original),
        'derived_seeder_sha256': sha(work / 'scripts/seed_g6_parallel_cache.py'),
        'original_install_preparer_path': str(installer_original), 'original_install_preparer_sha256': sha(installer_original),
        'derived_install_preparer_sha256': sha(work / 'scripts/prepare_g6_parallel_install.py'),
        'original_guard_path': str(guard_original), 'original_guard_sha256': GUARD,
        'derived_guard_sha256': sha(work / 'scripts/guard_g6_parallel_arm_transport_20261010.py'),
        'guard_derivation': 'Replace only four prior phase labels with parallel. All prelaunch pins, cleanup, final gates, memory/storage thresholds and child grouping are unchanged.',
        'transport_derivation': 'Only exact coverage assertions change to 120 authenticated warm (116 executable + four protected providers) + one pinned fresh; installer metadata filename changes. Existing cache admission, install, copy/hash policy and original receipts remain unchanged.',
        'budget': budget, 'original_sources_receipts_native_or_accepted_evidence_written': False,
        'compiler_flags_caps_core_mathlib_guards_audit_changed': False, 'compiler_launched': False}
    prep = {'status': 'PREPARED_UNCOMPILED_G6_PARALLEL_ARM_TRANSPORT117', 'workspace': str(work), 'evidence': str(evidence),
        'targets': [label, 'context/protected-mathlib-providers'], 'requested_targets': [label], 'executed_modules': 117, 'staging_modules': 121, 'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'),
        'contexts': [{'workspace': str(PARENT), 'target': 'current/connected', 'graph_sha256': sha(graph_path),
                      'selected_modules': 120, 'provenance': '116 exact executable parent components plus four protected namespace provider records from accepted1504; no new target acceptance is copied.'}],
        'derivatives': [{'module': module, 'source': str(source), 'source_sha256': source_pin['sha256'], 'replaces_original_sha256': None}],
        'source_versions_and_literal_imports_pinned': True, 'source_pins': {n: r['sha256'] for n,r in modules.items()},
        'builder_sha256': CORE, 'audit_template_sha256': AUDIT, 'official_complete_mathlib_namespace_overlay': True,
        'namespace_overlay_wrapper_sha256': OVERLAY, 'optimized_overlay_sha256': AUTH,
        'namespace_adapter_derivation': parent_prep['namespace_adapter_derivation'],
        'scratch_location_derivation': derivation, 'historical_passes_copied': False, 'native_execution_claimed': False}
    save(work / 'PREPARATION.json', prep)
    save(evidence / 'PREPARATION.json', prep)
    save(work / 'LOCATION-AND-COMPOSITION-DERIVATION.json', derivation)
    selection = str(work / 'SELECTED-CACHE-IDENTITIES.json')
    for script in ['seed_g6_parallel_cache.py', 'prepare_g6_parallel_install.py']:
        subprocess.run([sys.executable, str(work / 'scripts' / script), str(work), '--selection-manifest', selection], check=True)
    plan = {'status': 'READY_FOR_ROOT_PLAN_REVIEW_NO_COMPILER_LAUNCHED', 'workspace': str(work),
        'graph_sha256': sha(work / 'DEPENDENCY-GRAPH.json'), 'preparation_sha256': sha(work / 'PREPARATION.json'),
        'monitor_sha256': sha(work / 'scripts/guard_g6_parallel_arm_transport_20261010.py'),
        'monitor_path': str(work / 'scripts/guard_g6_parallel_arm_transport_20261010.py'),
        'python': sys.executable, 'launcher': str(ROOT / 'scripts/run_proof_extensions.py'),
        'launcher_sha256': sha(ROOT / 'scripts/run_proof_extensions.py'),
        'lean_bin': '/workspace/toolchains/lean-4.33.1-linux/bin', 'mathlib': '/workspace/dependencies/mathlib4',
        'phases': {'parallel': {'target': label, 'requires': []}}, 'allocation_roots': [*roots, str(work)],
        'scratch_abort_bytes': 2**31 - 128 * 2**20, 'scratch_hard_limit_bytes': 2**31,
        'memory_abort_bytes': 15 * 2**30, 'budget': budget, 'compiler_launched': False,
        'normal_compiler_caps': 'Unchanged original4GiB/180s; -j1 -t0 -Ddebug.skipKernelTC=false',
        'preservation': budget['packet_export_policy']}
    save(work / 'RESOURCE-AND-RUN-PLAN.json', plan)
    shutil.copyfile(Path(__file__), evidence / 'PREPARER.py')
    packet = ROOT / ('G6-PARALLEL-ARM-TRANSPORT-PREPARATION-' + stamp + '.json')
    save(packet, {'status': plan['status'], 'workspace': str(work), 'evidence': str(evidence),
        'plan_path': str(work / 'RESOURCE-AND-RUN-PLAN.json'), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
        'preparer_sha256': sha(Path(__file__)), 'graph_sha256': plan['graph_sha256'],
        'preparation_sha256': plan['preparation_sha256'], 'budget': budget})
    print(json.dumps({'workspace': str(work), 'packet_preparation': str(packet), 'plan_sha256': sha(work / 'RESOURCE-AND-RUN-PLAN.json'),
        'preparer_sha256': sha(Path(__file__)), 'monitor_sha256': plan['monitor_sha256'], 'budget': budget}))


if __name__ == '__main__':
    main()
