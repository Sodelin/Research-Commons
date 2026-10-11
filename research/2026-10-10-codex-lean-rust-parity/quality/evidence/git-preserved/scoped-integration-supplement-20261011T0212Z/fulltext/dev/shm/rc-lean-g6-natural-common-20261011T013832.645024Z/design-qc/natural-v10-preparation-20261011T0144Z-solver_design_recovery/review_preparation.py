#!/usr/bin/env python3
"""Saved-byte and source-AST preparation review only; no target imports/runs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
PREV = Path('/dev/shm/rc-lean-g6-natural-common-20261011T005738.287542Z')
OLD = Path('/dev/shm/rc-lean-g6-natural-common-20261011T003502.004915Z')

def require(ok, why):
    if not ok:
        raise AssertionError(why)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(65536), b''):
            h.update(block)
    return h.hexdigest()

def pin(path, expected=None):
    p = Path(path)
    digest = sha(p)
    require(expected is None or digest == expected, 'pin ' + str(p))
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': digest}

def load(path):
    return json.loads(Path(path).read_bytes())

def same_inode(a, b):
    x, y = Path(a).stat(), Path(b).stat()
    require((x.st_dev, x.st_ino) == (y.st_dev, y.st_ino), 'same inode ' + str(a))

def companion(base, suffix):
    return base.with_suffix(suffix) if suffix in ('.olean', '.ilean', '.ir') else Path(str(base) + suffix[len('.olean'):])

def check():
    plan_pin = pin(W/'RESOURCE-AND-RUN-PLAN.json', '2ce83724b428cf5873587300a5601b89ca07d0a8d0e8d6e6104c7e247bd2a45c')
    prep_pin = pin(W/'PREPARATION.json', 'cf51798f50180944db0bc26bee7e008f13f538a5c6825255e39bebe871914d16')
    graph_pin = pin(W/'DEPENDENCY-GRAPH.json', 'cc990a0238c1c1ae300b61fcd37303fa044439dc711041ba90de1412c3222b1b')
    closure_pin = pin(W/'SOURCE-CLOSURE.json', 'c39b15f32be30c93df85e0ed7fd6b80301a074ce7715737c170a0c1fb579a835')
    plan, prep, graph = (load(x['path']) for x in (plan_pin, prep_pin, graph_pin))
    require(plan['preparation_sha256'] == prep_pin['sha256'] and plan['graph_sha256'] == prep['graph_sha256'] == graph_pin['sha256'], 'actual prepared pins agree')
    deriv = prep['scratch_location_derivation']
    freeze_pin = pin(deriv['source_freeze']['path'], 'd54d69c760f24b6e6a2e6fb7310c6b6d5a489250663bfafb82b0adda62d9da9f')
    freeze = load(freeze_pin['path'])
    qcdir = OLD/'design-qc/natural-v7-preparer-20261011T0100Z-solver_design_recovery'
    static_gates = [
        pin(qcdir/'V7-PREPARER-STATIC-QC-ATTEMPT2.json', '91073f4fdd3256971ed3fd9249bafdc09612d5d171086b538fd634b403e0f5e5'),
        pin(qcdir/'V8-METADATA-LOCATION-STATIC-QC-ATTEMPT1.json', '61bf76ef5b0d958a5d1e76131139fa43c7675f85b729fc56890cf18db48f70d5'),
        pin(PREV/'design-qc/factor-5f-source-20261011T0113Z-solver_design_recovery/FACTOR-5F-PROOF-ONLY-STATIC-QC-ATTEMPT2.json', '9a100e62a31c06981db763719e94d91c0f3db05ef3397d2cb676aa49cb80b4bb'),
        pin(PREV/'design-qc/natural-v9-and-output-helpers-20261011T0114Z-solver_design_recovery/V9-AND-SHMEM-OUTPUT-STATIC-QC-ATTEMPT2.json', '557186c0e928aa3a08248371787ca42593117f0f1a02688b4b6a245c0be3a2ce'),
    ]
    static_gates.append(pin(Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')/'design-qc/factor-3fc-and-v10-source-20261011T0132Z-solver_design_recovery/FACTOR-3FC-AND-V10-STATIC-QC-ATTEMPT2.json','a7ecbf6ce59c8ed585589c9e8439de98340f06796b8a95d49cc077a186fb74ab'))
    preparer = pin(Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')/'scripts/prepare_g6_natural_common_factorization_20261011_v10_shmem_metadata.py', '7ea1b1f9d4b917bcf33d91246bfc4920e70a6783179e589b76875e9d7add181e')
    require(deriv['preparer_sha256'] == preparer['sha256'], 'reviewed v10 preparer identity')
    target_name = 'extraction/g6-natural-common-forest-factorization-3fc98f89'
    target, guards = graph['targets'][target_name], graph['targets']['context/protected-mathlib-providers']
    modules = {**target['modules'], **guards['modules']}
    require(len(target['modules']) == len(target['order']) == 141 and len(guards['modules']) == 4 and len(modules) == 145 and not set(target['modules']) & set(guards['modules']), '141 actual and four guard-only staging records')
    require(prep['requested_targets'] == [target_name] and plan['phases']['natural']['target'] == target_name, 'only exact natural target requested')
    providers = freeze['exact_composition']['accepted_providers']
    require(len(providers) == 139, '139 accepted parent-root sources')
    parent = load(P/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json')
    for row in providers:
        require((row['sha256'], row['imports']) == (target['modules'][row['module']]['sha256'], target['modules'][row['module']]['imports']), 'provider literal import/source metadata')
        if row['module'] != 'G6OriginalParallelArmTransport':
            require(parent['source_pins'][row['module']] == row['sha256'], 'accepted1504 parent source')
        else:
            require(row['sha256'] == 'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc', 'separately accepted original parallel-arm provider')
    fresh = load(W/'FRESH-SOURCES.json')
    require({n: r['sha256'] for n, r in fresh.items()} == {r['module']: r['sha256'] for r in freeze['sources']} == {
        'G6OriginalCommonPrefix': 'a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917',
        'G6NaturalCommonForestFactorization': '3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4'}, 'two immutable new source versions')
    closure = load(closure_pin['path'])
    require(len(closure) == 145 and {r['module'] for r in closure} == set(modules), '145 exact staged source records')
    for row in closure:
        require((row['sha256'], row['imports']) == (modules[row['module']]['sha256'], modules[row['module']]['imports']), 'source/graph metadata pair')
        pin(row['scratch_source'], row['sha256'])
        pin(row['preserved_source'], row['sha256'])
        require(re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)', Path(row['scratch_source']).read_text(), re.M) == row['imports'], 'literal normal/public import bytes')
    additional = [pin(r['path'], r['sha256']) for r in prep['additional_storage_input_pins'].values()]
    require(Path(prep['additional_storage_input_pins']['capture_gate']['path']).is_absolute(), 'absolute capture gate')
    eq_pin = pin(prep['runtime_parent_derivation']['path'], '1a6d3fd26e3fc51ffaa7699166196e548a9b7a6d6b5745a37a6d96b9f48d69eb')
    eq = load(eq_pin['path'])
    for role in ('namespace', 'authenticated'):
        old, new, rep = eq['accepted_'+role], eq['actual_'+role], eq[role+'_exact_replacement']
        pin(old['path'], old['sha256'])
        pin(new['path'], new['sha256'])
        a, b = Path(old['path']).read_text(), Path(new['path']).read_text()
        require(a.count(rep['old']) == rep['occurrences'] == 1 and a.replace(rep['old'], rep['new'], 1) == b, 'full parent source exact except one context hash literal')
    policy_pins = [pin(plan['monitor_path'], '8a190dfa60b0151c1ad622fab21eefac866b44145a1d0d3665b31f66a1979a9b'),
        pin(plan['launcher'], '1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c'),
        pin(W/'scripts/build_connected.py', '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'),
        pin(W/'scripts/storage_wrapper.py', 'd774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810')]
    require(plan['monitor_sha256'] == policy_pins[0]['sha256'] and plan['launcher_sha256'] == policy_pins[1]['sha256'], 'guard/facade plan binding')
    selection = load(W/'SELECTED-CACHE-IDENTITIES.json')
    require(len(selection) == 144 and {r['module'] for r in selection} == set(modules)-{'G6NaturalCommonForestFactorization'}, '144 warm incl one qualified prefix; only factorization pending fresh')
    prefix_rows = [r for r in selection if r['module'] == 'G6OriginalCommonPrefix']
    require(len(prefix_rows) == 1, 'exact one selected prefix component')
    prefix = prefix_rows[0]
    require(prefix['cache_key'] == '54ae5d6ce3d15200690415bbd1279d656cc4bfd4afa654a9d4a8f01f81bb95a9' and Path(prefix['cache_entry']).parent.parent.parent == OLD and prefix['receipt_sha256'] == '1210456fa737c8a7ad7c8caab999d60a01b391aad3e4ad10514b27877c204a05', 'only previously authenticated exact prefix key/receipt')
    artifact_count = 0
    direct_import_files = {}
    compiler_pin = pin('/workspace/toolchains/lean-4.33.1-linux/bin/lean', 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550')
    for row in selection:
        old, new = Path(row['cache_entry'])/'receipt.json', W/'.build/cache'/row['cache_key']/'receipt.json'
        pin(old, row['receipt_sha256'])
        pin(new, row['receipt_sha256'])
        require(old.read_bytes() == new.read_bytes(), 'selected receipt byte equality')
        same_inode(old, new)
        rec = load(old)
        require(rec['source_sha256'] == modules[row['module']]['sha256'] and rec['object_artifacts'] == row['object_artifacts'], 'selected source/artifact metadata')
        require(rec['status'] == 'PASS_FRESH_KERNEL_CHECK' and rec['exit_code'] == 0 and rec['source_and_imports_stable'] and rec['compiler_sha256'] == compiler_pin['sha256'], 'authenticated prior successful component/compiler')
        require(rec['cap_seconds'] == 180 and rec['cap_memory_mib'] == 4096 and '-Ddebug.skipKernelTC=false' in rec['command'] and '-j1' in rec['command'] and '-t0' in rec['command'], 'strict existing component caps/kernel flags')
        require(set(rec['direct_import_bindings']) == set(modules[row['module']]['imports']), 'receipt direct imports match literal staged source imports')
        for imported in rec['direct_import_bindings'].values():
            for suffix, digest in imported['artifacts'].items():
                path = str(companion(Path(imported['path']), suffix))
                require(path not in direct_import_files or direct_import_files[path] == digest, 'consistent direct compiled import identities')
                direct_import_files[path] = digest
        for suffix, digest in row['object_artifacts'].items():
            canonical = companion(Path(row['cached_object']), suffix)
            source = companion(old.parent/'artifact.olean', suffix)
            staged = companion(new.parent/'artifact.olean', suffix)
            for p in (canonical, source, staged):
                pin(p, digest)
            same_inode(source, staged)
            artifact_count += 1
    for path, digest in direct_import_files.items():
        pin(path, digest)
    require(len(direct_import_files) == 513, '513 distinct current compiled direct-import files bound by selected receipts')
    transport = load(W/'CACHE-TRANSPORT-PRE-USE-PLAN.json')
    require(len(transport['entries']) == 144 and not transport['compiler_launched'], '144 saved pre-use aliases')
    files, filebytes = 0, 0
    for row in transport['entries']:
        for item in row['files']:
            for side in ('source', 'destination'):
                record = pin(item[side], item['sha256'])
                require(record['bytes'] == item['bytes'], 'transport exact byte length')
            same_inode(item['source'], item['destination'])
            files += 1
            filebytes += item['bytes']
    require(artifact_count == 156 and files == artifact_count + len(selection) == 300 and filebytes == 50855764, '156 artifacts+144 receipts=300 exact hardlink files/50855764B')
    budget = plan['budget']
    require(budget['planned_conservative_combined_bound_bytes'] == budget['conservative_followed_target_prior_bytes'] + sum(budget['new_allocation_reserves'].values()) == 1917931520, 'dated bound arithmetic')
    require(plan['scratch_abort_bytes'] == 2013265920 and plan['scratch_hard_limit_bytes'] == 2147483648 and plan['memory_abort_bytes'] == 16106127360 and len(plan['allocation_roots']) == 26 and budget['packet_export_transient_reserve_bytes'] == 8388608, 'unchanged2GiB/15GiB/8MiB policy with all26 roots')
    roots = set(plan['allocation_roots'])
    require(roots == set(load(Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')/'RESOURCE-AND-RUN-PLAN.json')['allocation_roots']) | {str(W)}, 'all25 prior roots retained plus exact new natural context; relocated object pool counted inside forest root')
    require(plan['phases']['natural']['requires'] == [] and not plan['compiler_launched'], 'saved prelaunch plan has no hidden targets or claimed compiler launch')
    require({str(OLD), str(PREV), '/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z', str(W)} <= roots and set(load(prep['additional_storage_input_pins']['capture_gate']['path'])['byte_trial_allocation_roots']) <= roots, 'forest/full export, old failed contexts and seven support roots counted')
    import os
    forest = Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
    migration_path = forest/'metadata/git-evidence-publication/GIT-OBJECT-POOL-LOSSLESS-RELOCATION-20261011.json'
    migration_pin = pin(migration_path)
    migration = load(migration_path)
    prior_inventory = load(forest/'design-qc/git-object-pool-relocation-source-20261011T0130Z-solver_design_recovery/OBJECT-POOL-RELOCATION-V1-SOURCE-QC.json')['actual_input_inventory']['rows']
    require(migration['status']=='FULL_GIT_OBJECT_POOL_RELOCATED_WITH_IDENTICAL_LOGICAL_BYTES' and migration['rows']==prior_inventory and migration['objects_count']==2261 and migration['content_bytes']==55754823 and migration['object_cap_bytes_unchanged']==67108864,'complete original migration receipt and frozen2261 rows')
    logical, counted = Path(migration['old_logical_path']), Path(migration['counted_preserved_path'])
    require(logical.is_symlink() and logical.resolve()==counted and str(counted).startswith(str(forest)+'/') and not Path('/tmp/rc-cloud-git-objects-verified-redirect-backup-20261011').exists(),'original logical pool readthrough counted forest and temporary backup absent')
    for row in migration['rows']:
        require(pin(logical/row['path'],row['sha256'])['bytes']==pin(counted/row['path'],row['sha256'])['bytes']==row['bytes'],'all migrated object original logical/fullcounted bytes')
        same_inode(logical/row['path'],counted/row['path'])
    total_pool_bytes=sum(p.stat().st_size for p in counted.rglob('*') if p.is_file())
    require(total_pool_bytes<67108864,'actual current object pool below unchanged64MiB content cap')
    seen, allocation = set(), 0
    for root in roots:
        require(Path(root).is_dir() and not (Path(root)/'ACTIVE-GUARDED-PROCESS.json').exists(),'all26 current roots idle at inspection')
        for directory, dirs, files in os.walk(root,followlinks=False):
            for path in [Path(directory),*(Path(directory)/name for name in files)]:
                st=path.lstat();key=(st.st_dev,st.st_ino)
                if key not in seen:
                    seen.add(key);allocation+=st.st_blocks*512
    mem=dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
    nonreclaim=sum(int(mem[k]) for k in ('anon','shmem','kernel'))
    require(allocation+sum(budget['new_allocation_reserves'].values())<plan['scratch_abort_bytes'] and nonreclaim<plan['memory_abort_bytes'],'actual current26-root lstat+fullproofreserve fits unchanged limits')
    current_measurement={'distinct_inode_lstat_bytes':allocation,'full_next_phase_reserves':sum(budget['new_allocation_reserves'].values()),'with_reserves':allocation+sum(budget['new_allocation_reserves'].values()),'nonreclaim_bytes':nonreclaim,'current_object_pool_content_bytes':total_pool_bytes,'all26_markers_absent':True,'migration':migration_pin,'all2261logical_objects_rehashed':True}
    return {'current_resource_and_relocation_readback':current_measurement,'status': 'PASS_SAVED_V10_PREPARATION_IDENTITIES_AND_QUALIFIED_PREFIX_REUSE_ONLY', 'plan': plan_pin, 'preparation': prep_pin, 'graph': graph_pin, 'closure': closure_pin, 'freeze': freeze_pin, 'preparer': preparer, 'prior_static_gates': static_gates, 'actual_parent_equivalence': eq_pin, 'policy_pins': policy_pins, 'compiler_pin': compiler_pin, 'additional_prelaunch_pins': additional, 'checked_counts': {'executed_modules_planned': 141, 'staged_sources': 145, 'accepted_root_providers': 139, 'qualified_prefix_components': 1, 'pending_fresh_components': 1, 'new_source_versions_retained': 2, 'warm_receipt_pairs': 144, 'artifact_companion_pairs': 156, 'same_inode_cache_transport_files': 300, 'transport_bytes': 50855764, 'distinct_current_compiled_direct_import_files': 513, 'allocation_roots': 26}, 'dated_conservative_bound_bytes': 1917931520, 'qualification': ['Saved preparation identities only; no target/helper/guard/compiler imported or executed by this reviewer.', 'a080 is one authenticated kernel component in a failed141 run, distinct from139 accepted root providers. No previous full141 audit/aggregate acceptance inferred.', 'Source141, staging145 and warm144 labels are distinct. Exact current source/import/native/kernel admissions and current-resource launch remain Root/sole scheduler gates.', 'Original once-drawn private seed/erased Old/local support/no-read and physical exit/context/bin/decoder/global positive construction boundaries remain unchanged.']}

def main():
    out = Path(sys.argv[1])
    report = {'schema': 'natural_v10_saved_preparation_design_qc_v1', 'contributor': 'Codex / solver_design_recovery', 'observed_utc': datetime.now(timezone.utc).isoformat(), 'reviewer_sha256': sha(__file__), 'target_modules_imported_or_producer_processes_started': 0, 'mathematical_acceptance_modified': False}
    try:
        report.update(check())
    except Exception as e:
        report.update(status='FAIL_SAVED_V10_PREPARATION_QC', error_type=type(e).__name__, error=str(e))
    with out.open('x') as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write('\n')
    print(json.dumps({'path': str(out), 'status': report['status'], 'sha256': sha(out)}))
    return int(report['status'].startswith('FAIL'))

if __name__ == '__main__':
    raise SystemExit(main())
