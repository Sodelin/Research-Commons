#!/usr/bin/env python3
"""Prepare exact natural COMMON141 plus four nonexecuted namespace guards.

Codex / lean_integration_successor, 2026-10-11. No Lean invocation here.
Storage/source byte gates are required before materialization; mathematical
launch remains a separate root-reviewed resource plan. Accepted paths untouched.
"""
from __future__ import annotations
import argparse, datetime, errno, json, os, re, shutil, subprocess, sys
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = ROOT.parents[2]
PARENT = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
ARM = Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z')
FREEZE = ROOT/'proposals/reuse-integration-20261010T2138Z/natural-common-factorization/PROPOSAL-FREEZE-V4.json'
STORAGE = ROOT/'proposals/compressed-loader-storage-20261010T235105.986329Z/v3-partial-failure/storage_wrapper.py'
STORAGE_SHA = 'd774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810'
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
AUDIT = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
OVERLAY = '09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0'
AUTH = 'ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'
GUARD = '4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4'
LAUNCHER = ROOT/'scripts/run_proof_extensions_with_storage_20261011.py'
LAUNCHER_SHA = '1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c'


def allocated(roots, follow=False):
    seen, total = set(), 0
    for root in roots:
        for directory, _, files in os.walk(root):
            for path in [Path(directory), *(Path(directory)/n for n in files)]:
                stat = path.stat() if follow else path.lstat()
                key = (stat.st_dev, stat.st_ino)
                if key not in seen:
                    seen.add(key); total += stat.st_blocks*512
    return total


def link(source, destination):
    source = Path(source); expected = sha(source)
    destination.parent.mkdir(parents=True, exist_ok=True)
    assert not destination.exists()
    try:
        os.link(source,destination); mode='SAME_FILESYSTEM_HARD_LINK'
        assert (source.stat().st_dev,source.stat().st_ino)==(destination.stat().st_dev,destination.stat().st_ino)
    except OSError as error:
        if error.errno!=errno.EXDEV: raise
        shutil.copy2(source,destination); mode='EXDEV_HASH_CHECKED_COPY2'
    assert sha(source)==sha(destination)==expected
    return {'source':str(source),'destination':str(destination),'sha256':expected,
            'bytes':source.stat().st_size,'transport':mode}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture-gate',required=True,type=Path)
    parser.add_argument('--capture-gate-sha256',required=True)
    args=parser.parse_args()
    assert sha(args.capture_gate)==args.capture_gate_sha256
    gate=json.loads(args.capture_gate.read_bytes())
    assert gate['status']=='APPROVED_SOURCE_AND_SAVED_BYTE_CAPTURE_GATE'
    assert gate['storage_wrapper_sha256']==sha(STORAGE)==STORAGE_SHA
    for row in gate['evidence']:
        assert sha(Path(row['path']))==row['sha256']
    assert sha(LAUNCHER)==LAUNCHER_SHA
    assert sha(FREEZE)=='e3391d165f5f3253a6de2876544ac6568dca3013cbc5d294a6cd55c9a4f39b41'
    proposal=json.loads(FREEZE.read_bytes())
    for row in proposal['acceptance_bindings']:
        assert sha(REPOSITORY/row['path'])==row['sha256']
    parent_graph=json.loads((PARENT/'DEPENDENCY-GRAPH.json').read_bytes())
    parent=parent_graph['targets']['current/connected']
    arm_graph=json.loads((ARM/'DEPENDENCY-GRAPH.json').read_bytes())
    parent_prep=json.loads((PARENT/'PREPARATION.json').read_bytes())
    arm_plan=json.loads((ARM/'RESOURCE-AND-RUN-PLAN.json').read_bytes())
    assert len(parent['modules'])==1504
    pins=proposal['exact_composition']['accepted_providers']
    assert len(pins)==139 and len({r['module'] for r in pins})==139
    modules={}; parent_workspace={}
    for row in pins:
        name=row['module']; source=REPOSITORY/row['path']
        assert sha(source)==row['sha256']
        assert re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',source.read_text(),re.M)==row['imports']
        workspace=PARENT if name in parent['modules'] else ARM
        original=parent['modules'][name] if workspace==PARENT else next(t['modules'][name] for t in arm_graph['targets'].values() if name in t['modules'])
        assert (original['sha256'],original['imports'])==(row['sha256'],row['imports'])
        modules[name]=original; parent_workspace[name]=workspace
    assert sum(w==PARENT for w in parent_workspace.values())==138
    fresh={}; fresh_sources={}
    for row in proposal['sources']:
        source=REPOSITORY/row['immutable_version']; name=row['module']
        assert sha(source)==sha(REPOSITORY/row['path'])==row['sha256']
        imports=re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',source.read_text(),re.M)
        assert imports==row['imports']
        fresh[name]={'module':name,'sha256':row['sha256'],'imports':imports}
        fresh_sources[name]=source
    assert len(fresh)==2
    modules.update(fresh)
    order=proposal['exact_composition']['topological_modules']
    assert len(order)==len(modules)==141 and set(order)==set(modules)
    for i,name in enumerate(order):
        assert all(d not in modules or d in order[:i] for d in modules[name]['imports'])
    root='G6NaturalCommonForestFactorization'
    label=next(r['suggested_target'] for r in proposal['intended_targets'] if r['root']==root)
    target={'roots':[root],'order':order,'modules':{n:modules[n] for n in order},
            'required_for_accepted_release':False,'status':'UNCOMPILED_EXACT_NATURAL_COMMON_PROOF_EXTENSION'}
    protected={n:r for n,r in parent['modules'].items() if n.startswith('Mathlib.')}
    assert len(protected)==4 and not (set(protected)&set(modules))
    guard_order=[n for n in parent['order'] if n in protected]
    modules.update(protected); staging_order=order+guard_order
    graph={'targets':{label:target,'context/protected-mathlib-providers':{
        'roots':guard_order,'order':guard_order,'modules':protected,
        'required_for_accepted_release':False,'status':'PROTECTED_NAMESPACE_CONTEXT_ONLY_NOT_EXECUTED'}},
        'scope':'Natural COMMON141 executable proof root;145 staging records includes four exact nonexecuted namespace guards. No1504 widening claim.'}
    roots=list(arm_plan['allocation_roots'])
    roots += [str(p) for p in sorted(Path('/dev/shm').glob('rc-lean-g6-natural-common-*')) if p.is_dir()]
    roots += gate.get('byte_trial_allocation_roots',[])
    roots=list(dict.fromkeys(roots))
    existing=allocated(roots); conservative=allocated(roots,True)
    reserves={'fresh_object_companions_single_copy':32*2**20,'four_bounded_gzip_captures':4*2**20,
              'minimal_aggregate_and_raw_owned_audit':16*2**20,'metadata_and_transient_writes':16*2**20,
              'lossless_export_staging':8*2**20}
    bound=conservative+sum(reserves.values())
    assert bound < 2**31-128*2**20
    assert shutil.disk_usage('/dev/shm').free>sum(reserves.values())
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
    work=Path('/dev/shm')/('rc-lean-g6-natural-common-'+stamp)
    evidence=work/'evidence/preparation'; evidence.mkdir(parents=True)
    (work/'scripts').mkdir()
    save(work/'DEPENDENCY-GRAPH.json',graph); save(work/'FRESH-SOURCES.json',fresh)
    source_records=[];closure=[]; pin_by_module={r['module']:r for r in pins}
    parent_closure={r['module']:r for r in json.loads((PARENT/'SOURCE-CLOSURE.json').read_bytes())}
    for name in staging_order:
        row=modules[name]
        source=fresh_sources[name] if name in fresh else (parent_workspace.get(name,PARENT)/'source-store'/(row['sha256']+'.lean'))
        assert sha(source)==row['sha256']
        destination=work/'source-store'/(row['sha256']+'.lean')
        if not destination.exists(): source_records.append(link(source,destination))
        preserved=fresh_sources[name] if name in fresh else REPOSITORY/pin_by_module[name]['path'] if name in pin_by_module else Path(parent_closure[name]['preserved_source'])
        assert sha(preserved)==row['sha256']
        closure.append({**row,'scratch_source':str(destination),'preserved_source':str(preserved)})
    save(work/'SOURCE-CLOSURE.json',closure);save(work/'SOURCE-TRANSPORT.json',source_records)
    cache_by_module={}
    for workspace in [PARENT,ARM]:
        for entry in (workspace/'.build/cache').iterdir():
            rec=json.loads((entry/'receipt.json').read_bytes());name=rec['module']
            if name not in modules or name in fresh or name in cache_by_module: continue
            assert rec['source_sha256']==modules[name]['sha256']
            cache_by_module[name]={'module':name,'source_sha256':rec['source_sha256'],
                'source_path':str(work/'source-store'/(rec['source_sha256']+'.lean')),
                'cache_entry':str(entry),'cache_key':entry.name,'receipt_sha256':sha(entry/'receipt.json'),
                'cached_object':rec['cached_object'],'object_artifacts':rec['object_artifacts']}
    assert len(cache_by_module)==143 and set(cache_by_module)==set(modules)-set(fresh)
    selected=[cache_by_module[n] for n in staging_order if n not in fresh]
    save(work/'SELECTED-CACHE-IDENTITIES.json',selected)
    wrappers=PARENT/parent_prep['cache_install_transport_derivation']['evidence']
    for source,name,expected in [
        (PARENT/'scripts/build_connected.py','build_connected.py',CORE),
        (PARENT/'scripts/AuditTemplate.lean','AuditTemplate.lean',AUDIT),
        (wrappers/'ORIGINAL-NAMESPACE-OVERLAY.py','build_with_mathlib_overlay.py',OVERLAY),
        (wrappers/'ORIGINAL-AUTHENTICATED-OVERLAY.py','build_with_authenticated_overlay.py',AUTH)]:
        assert sha(source)==expected;shutil.copyfile(source,work/'scripts'/name)
    for name in ['check_core.py','seed_exact_cache.py']:
        shutil.copyfile(ROOT/'scripts'/name,work/'scripts'/name)
    shutil.copytree(PARENT/'third-party',work/'third-party')
    shutil.copyfile(STORAGE,work/'scripts/storage_wrapper.py')
    original_seeder=ROOT/'scripts/seed_exact_cache_transport.py';seeder=original_seeder.read_text()
    before='    assert len(identities) == len(selected)\n    assert {row["module"] for row in identities} == set(selected)'
    after="""    fresh = json.loads((destination / 'FRESH-SOURCES.json').read_bytes())
    warm = {row['module'] for row in identities}
    assert len(selected) == 145 and len(identities) == len(warm) == 143 and len(fresh) == 2
    assert warm == set(selected) - set(fresh)
    assert all(selected[m] == row for m, row in fresh.items())"""
    assert seeder.count(before)==1;seeder=seeder.replace(before,after)
    original_installer=ROOT/'scripts/prepare_cache_install_transport_history_1497.py';installer=original_installer.read_text()
    before='    assert len(selected) == len(owned) and {r["module"] for r in selected} == set(owned)'
    after="""    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    warm = {r['module'] for r in selected}
    assert len(owned) == 145 and len(selected) == len(warm) == 143 and len(fresh) == 2
    assert warm == set(owned) - set(fresh)
    assert all(owned[m] == row for m, row in fresh.items())"""
    assert installer.count(before)==1
    installer=installer.replace(before,after).replace('CACHE-INSTALL-TRANSPORT-HISTORY-1497-DERIVATION.json','CACHE-INSTALL-TRANSPORT-NATURAL141-DERIVATION.json')
    original_guard=ROOT/'scripts/guard_g7_survival_run_20261010_v2.py';assert sha(original_guard)==GUARD
    guard=original_guard.read_text()
    before="choices=['primary', 'secondary', 'union1503', 'union1504']"
    assert guard.count(before)==1;guard=guard.replace(before,"choices=['natural']")
    before="    phase = config['phases'][args.phase]"
    after="""    for name, row in prep['additional_storage_input_pins'].items():
        assert sha(row['path']) == row['sha256'], ('Storage input drift', name)
        checked_inputs[name] = row
    phase = config['phases'][args.phase]"""
    assert guard.count(before)==1;guard=guard.replace(before,after)
    derived=[('seed_natural_common_cache.py',seeder),('prepare_natural_common_install.py',installer),('guard_natural_common_20261011.py',guard)]
    for name,text in derived:
        compile(text,name,'exec');(work/'scripts'/name).write_text(text)
    policy={'schema':'reviewed_compressed_stderr_policy_v1','runtime_authorized':True,
            'raw_limit_bytes':32*2**20,'gzip_limit_bytes':2**20,
            'capture_gate_path':str(args.capture_gate),'capture_gate_sha256':args.capture_gate_sha256,
            'qualification':'Capability enabled only after the pinned source/saved-byte gate; mathematical execution remains separately root approved.'}
    save(work/'STDERR-STORAGE-POLICY.json',policy)
    budget={'guard_lstat_prior_distinct_inode_bytes':existing,'conservative_followed_target_prior_bytes':conservative,
            'new_allocation_reserves':reserves,'planned_conservative_combined_bound_bytes':bound,
            'combined_scratch_limit_bytes':2**31,'scratch_abort_bytes':2**31-128*2**20,
            'memory_nonreclaimable_abort_bytes':15*2**30,'monitor_poll_seconds':0.5,
            'overlay_free_at_preparation':shutil.disk_usage(str(ROOT)).free,
            'packet_export_transient_reserve_bytes':8*2**20,
            'packet_export_policy':'Measure fixed complete lossless shmem export; copy only if exact bytes+8MiB fit overlay, otherwise keep complete fixed-shmem export with explicit distribution manifest. No duplicate parent sources/objects/ELF or old-byte deletion.'}
    derivation={'status':'PRE_USE_NATURAL141_LOCATION_AND_STORAGE_DERIVATION','preparer_sha256':sha(Path(__file__)),
        'parent_workspaces':[str(PARENT),str(ARM)],'source_freeze':{'path':str(FREEZE),'sha256':sha(FREEZE)},
        'capture_gate':{'path':str(args.capture_gate),'sha256':args.capture_gate_sha256},
        'source_partition':{'accepted1504':138,'separately_accepted_parallel_arm':1,'fresh':fresh,
                            'executed':141,'protected_nonexecuted_guard_records':4,'staged':145,'warm':143},
        'derivation_basis':{'path':str(ROOT/'scripts/prepare_g6_parallel_arm_transport_20261010.py'),
                            'sha256':sha(ROOT/'scripts/prepare_g6_parallel_arm_transport_20261010.py')},
        'seed_source':{'path':str(original_seeder),'sha256':sha(original_seeder)},
        'install_source':{'path':str(original_installer),'sha256':sha(original_installer)},
        'guard_source':{'path':str(original_guard),'sha256':GUARD},
        'derived_scripts':{n:sha(work/'scripts'/n) for n,_ in derived},
        'storage_wrapper':{'path':str(STORAGE),'sha256':STORAGE_SHA},
        'storage_changes':'Combined stderr gzip replaces separated raw loader logs; native presence explicitly required; only fresh attempt/cache companions get same-FS aliases. Canonical core and all policy checks/caps remain frozen.',
        'transport_changes':'Coverage assertions143 warm+2 fresh/145 staged and unique derivative outputname; source/cache hardlinks with EXDEV hash-checked copy; installer alias policy unchanged.',
        'guard_changes':'Only natural phase label and explicit prelaunch adapter/policy/source-byte-gate hash gates; final thresholds, process-group cleanup, all kernel/resource caps unchanged.',
        'source_repair_derivation':{'prior_preparer_sha256':'1ba6a93a39c6323ec82c96c89090cdd645edf5e011c190cab6f4aa8c2ee5f16b',
            'prior_workspace':'/dev/shm/rc-lean-g6-natural-common-20261011T002247.540229Z',
            'failed_source_sha256':'ce9ec8df671d52cb45d3855353faa7c46cffb6660a00cdc2e0f61110602507bd',
            'proof_only_repair_sha256':'a2275917b1a844e7b12c5198419f17f51646ff5ac84fee435e0c90f1b129eca3',
            'qualification':'Only source freeze V4 replaces V3; exact141 topology,139 accepted providers,4 protected guards, storage adapter/core/flags/caps and transport policies unchanged. Previous context and its failure are preserved and counted in allocation roots.'},
        'compiler_launched':False,'original_sources_receipts_native_accepted_evidence_written':False,'budget':budget}
    prep={'status':'PREPARED_UNCOMPILED_NATURAL_COMMON141','workspace':str(work),'evidence':str(evidence),
        'targets':[label,'context/protected-mathlib-providers'],'requested_targets':[label],
        'executed_modules':141,'staging_modules':145,'graph_sha256':sha(work/'DEPENDENCY-GRAPH.json'),
        'contexts':[{'workspace':str(PARENT),'selected_modules':142,'scope':'138 executable plus4 guards; authenticated component reuse only'},
                    {'workspace':str(ARM),'selected_modules':1,'scope':'Exact separately accepted f40 provider'}],
        'source_versions_and_literal_imports_pinned':True,'source_pins':{n:r['sha256'] for n,r in modules.items()},
        'builder_sha256':CORE,'audit_template_sha256':AUDIT,'official_complete_mathlib_namespace_overlay':True,
        'namespace_overlay_wrapper_sha256':OVERLAY,'optimized_overlay_sha256':AUTH,
        'namespace_adapter_derivation':parent_prep['namespace_adapter_derivation'],
        'storage_wrapper_sha256':STORAGE_SHA,'storage_policy_sha256':sha(work/'STDERR-STORAGE-POLICY.json'),
        'additional_storage_input_pins':{'storage_wrapper.py':{'path':str(work/'scripts/storage_wrapper.py'),'sha256':STORAGE_SHA},
            'storage_policy':{'path':str(work/'STDERR-STORAGE-POLICY.json'),'sha256':sha(work/'STDERR-STORAGE-POLICY.json')},
            'capture_gate':{'path':str(args.capture_gate),'sha256':args.capture_gate_sha256},
            **{'capture_gate_evidence_'+str(i):row for i,row in enumerate(gate['evidence'])}},
        'scratch_location_derivation':derivation,'historical_passes_copied':False,'native_execution_claimed':False}
    save(work/'PREPARATION.json',prep);save(evidence/'PREPARATION.json',prep)
    save(work/'LOCATION-AND-COMPOSITION-DERIVATION.json',derivation)
    selection=str(work/'SELECTED-CACHE-IDENTITIES.json')
    for name in ['seed_natural_common_cache.py','prepare_natural_common_install.py']:
        subprocess.run([sys.executable,str(work/'scripts'/name),str(work),'--selection-manifest',selection],check=True)
    # Actual new parent byte derivation is qualified, not a literal ARM SHA claim.
    arm_namespace=ARM/'scripts/build_with_mathlib_overlay.py'
    arm_authenticated=ARM/'scripts/build_with_authenticated_overlay.py'
    assert sha(arm_namespace)=='3d613f389158ad106741f72660429a6de28a18da498480c38072ce92b62c0a67'
    assert sha(arm_authenticated)=='5406eb1a68e8f6e35729f8ae991906213cf1e4f2628f6ce4aac019f8ee25ac46'
    prior_manifest=json.loads((ARM/'PREPARATION.json').read_bytes())['cache_install_transport_derivation']['alias_manifest_sha256']
    current_prep=json.loads((work/'PREPARATION.json').read_bytes())
    new_manifest=current_prep['cache_install_transport_derivation']['alias_manifest_sha256']
    old_namespace=arm_namespace.read_text()
    assert old_namespace.count(prior_manifest)==1
    assert old_namespace.replace(prior_manifest,new_manifest)==(work/'scripts/build_with_mathlib_overlay.py').read_text()
    old_authenticated=arm_authenticated.read_text()
    assert old_authenticated.count(sha(arm_namespace))==1
    assert old_authenticated.replace(sha(arm_namespace),sha(work/'scripts/build_with_mathlib_overlay.py'))==(work/'scripts/build_with_authenticated_overlay.py').read_text()
    equivalence={'status':'EXACT_PARENT_SOURCE_EQUIVALENCE_EXCEPT_MANIFEST_AND_BASE_PINS',
        'accepted_namespace':{'path':str(arm_namespace),'sha256':sha(arm_namespace)},
        'accepted_authenticated':{'path':str(arm_authenticated),'sha256':sha(arm_authenticated)},
        'actual_namespace':{'path':str(work/'scripts/build_with_mathlib_overlay.py'),'sha256':sha(work/'scripts/build_with_mathlib_overlay.py')},
        'actual_authenticated':{'path':str(work/'scripts/build_with_authenticated_overlay.py'),'sha256':sha(work/'scripts/build_with_authenticated_overlay.py')},
        'namespace_exact_replacement':{'old':prior_manifest,'new':new_manifest,'occurrences':1},
        'authenticated_exact_replacement':{'old':sha(arm_namespace),'new':sha(work/'scripts/build_with_mathlib_overlay.py'),'occurrences':1},
        'inventory_invoke_dependency_core_identity_and_namespace_guard_method_bodies_unchanged':True,
        'runtime_core_object_binding':'builder_module.original.core; same exact core object used by all parents',
        'no_literal_runtime_parent_hash_equality_claim':True,'compiler_launched':False}
    save(work/'PARENT-WRAPPER-EQUIVALENCE.json',equivalence)
    current_prep['runtime_parent_derivation']={'path':str(work/'PARENT-WRAPPER-EQUIVALENCE.json'),'sha256':sha(work/'PARENT-WRAPPER-EQUIVALENCE.json')}
    current_prep['additional_storage_input_pins']['actual_parent_source_equivalence']=current_prep['runtime_parent_derivation']
    save(work/'PREPARATION.json',current_prep);save(evidence/'PREPARATION.json',current_prep)
    plan={'status':'READY_FOR_ROOT_PLAN_REVIEW_NO_COMPILER_LAUNCHED','workspace':str(work),
          'graph_sha256':sha(work/'DEPENDENCY-GRAPH.json'),'preparation_sha256':sha(work/'PREPARATION.json'),
          'monitor_path':str(work/'scripts/guard_natural_common_20261011.py'),
          'monitor_sha256':sha(work/'scripts/guard_natural_common_20261011.py'),
          'python':sys.executable,'launcher':str(LAUNCHER),'launcher_sha256':LAUNCHER_SHA,
          'lean_bin':'/workspace/toolchains/lean-4.33.1-linux/bin','mathlib':'/workspace/dependencies/mathlib4',
          'phases':{'natural':{'target':label,'requires':[]}},'allocation_roots':roots+[str(work)],
          'scratch_abort_bytes':2**31-128*2**20,'scratch_hard_limit_bytes':2**31,
          'memory_abort_bytes':15*2**30,'budget':budget,'compiler_launched':False,
          'normal_compiler_caps':'Actual extraction components/aggregate/audit unchanged4GiB/180s; retained connected-label policy6GiB/300s; -j1 -t0 -Ddebug.skipKernelTC=false',
          'preservation':budget['packet_export_policy']}
    save(work/'RESOURCE-AND-RUN-PLAN.json',plan);shutil.copyfile(Path(__file__),evidence/'PREPARER.py')
    packet=ROOT/('G6-NATURAL-COMMON-PREPARATION-'+stamp+'.json')
    save(packet,{'status':plan['status'],'workspace':str(work),'evidence':str(evidence),
                 'plan_path':str(work/'RESOURCE-AND-RUN-PLAN.json'),'plan_sha256':sha(work/'RESOURCE-AND-RUN-PLAN.json'),
                 'preparer_sha256':sha(Path(__file__)),'graph_sha256':plan['graph_sha256'],'budget':budget})
    print(json.dumps({'workspace':str(work),'packet_preparation':str(packet),'plan_sha256':sha(work/'RESOURCE-AND-RUN-PLAN.json'),
                      'preparer_sha256':sha(Path(__file__)),'monitor_sha256':plan['monitor_sha256'],'budget':budget}))

if __name__=='__main__': main()
