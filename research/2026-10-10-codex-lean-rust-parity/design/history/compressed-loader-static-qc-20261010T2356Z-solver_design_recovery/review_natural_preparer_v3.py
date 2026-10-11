#!/usr/bin/env python3
"""Own source-only review; no preparer, seeder, installer, Builder or compiler runs."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
V=P/'lean/proposals/compressed-loader-storage-20261010T235105.986329Z/v3-partial-failure'
ARM=Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z')
PARENT=Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')

def require(value,label):
    if not value: raise AssertionError(label)

def sha(raw): return hashlib.sha256(raw).hexdigest()

def pin(path,expected):
    path=Path(path); raw=path.read_bytes(); require(sha(raw)==expected,'pin '+str(path))
    return {'path':str(path),'bytes':len(raw),'sha256':expected}

def ordered(body,parts,label):
    offset=-1
    for part in parts:
        offset=body.find(part,offset+1); require(offset>=0,label+': '+part)

def check():
    freeze_pin=pin(V/'NATURAL141-PREPARATION-SOURCE-FREEZE-V4-20261011.json','f6d8bdff5b5ed7fd2afb6f5e61e89dcdc06d28e2fa427735cc753e40ed698cc5')
    freeze=json.loads(Path(freeze_pin['path']).read_bytes())
    require(freeze['status']=='SOURCE_CONFIG_ONLY_NO_NEW_CONTEXT_OR_COMPILER' and
            [freeze[k] for k in ('executed_modules','staging_modules','warm_modules','fresh_modules')]==[141,145,143,2], 'source-only graph partition')
    source_pins=[pin(freeze[k]['path'],freeze[k]['sha256']) for k in ('preparer','launcher','capture_wrapper','old_unexecuted_preparer','static_resource_measurement')]
    old=[pin(freeze[k]['path'] if 'path' in freeze[k] else freeze[k]['supersedes'],freeze[k]['sha256']) for k in ('supersedes','metadata_correction')]
    old.append(pin(P/'lean/scripts/prepare_g6_natural_common_factorization_20261011_v2.py','4a9d02da8fee7e840a233da28f9c51abc02ca29cc2d95c6c0067a3718e92ca3b'))
    qc_refs=[pin(P/'design/history/g6-natural-common-static-qc-20261010T2350Z-solver_design_recovery/G6-NATURAL-COMMON-STATIC-QC-ATTEMPT2.json','aeb75ab184e093d90204dc249ef41cbf4c7f735eb8beccbcf80fe9de0582c053'),
             pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/COMPRESSED-LOADER-V3-STATIC-QC-ATTEMPT1.json','9fde1c98aea1389b90551f6df8dc1b75a3fc25defb863c4194a609a0f6c8ea18'),
             pin(P/'design/history/storage-saved-qc-20261011T0009Z-solver_design_recovery/COMPRESSED-LOADER-V3-SAVED-QC-ATTEMPT1.json','f0c5402861b73536105ac64d278fbb1198a488e072e85911b9214cfe62f160ba')]
    source=Path(freeze['preparer']['path']).read_text(); launcher=Path(freeze['launcher']['path']).read_text()
    tree,ltree=ast.parse(source),ast.parse(launcher)
    require(freeze['preparation_command_after_root_gate'][2]==freeze['preparer']['path'], 'V4 command uses v3, preserved V3 metadata error qualified')
    ordered(source,["sha(args.capture_gate)==args.capture_gate_sha256", "gate['status']=='APPROVED_SOURCE_AND_SAVED_BYTE_CAPTURE_GATE'",
                    "for row in gate['evidence']:", "sha(Path(row['path']))==row['sha256']", "len(pins)==139",
                    "len(fresh)==2", "len(order)==len(modules)==141", "len(protected)==4 and not (set(protected)&set(modules))",
                    "roots += gate.get('byte_trial_allocation_roots',[])", "bound < 2**31-128*2**20", "evidence.mkdir(parents=True)"],
            'root/source/gate/partition/resource checks before materialization')
    for text in ['sum(w==PARENT for w in parent_workspace.values())==138', 'len(cache_by_module)==143',
                 'len(selected) == 145 and len(identities) == len(warm) == 143 and len(fresh) == 2',
                 'len(owned) == 145 and len(selected) == len(warm) == 143 and len(fresh) == 2',
                 "'requested_targets':[label]", "'compiler_launched':False", "'memory_abort_bytes':15*2**30"]:
        require(text in source,'exact source/metadata-only staging policy '+text)
    ordered(launcher,["sha(adapter_path) == prep['storage_wrapper_sha256']", "sha(policy_path) == prep['storage_policy_sha256']",
                      "policy['runtime_authorized'] is True", 'adapter_spec.loader.exec_module(adapter_module)',
                      'builder_module.OverlayBuilder, builder_module.original.core, policy', 'builder = builder_class()'], 'exact authenticated core object binding before constructor')
    ordered(source,["subprocess.run([sys.executable,str(work/'scripts'/name)", "old_namespace.count(prior_manifest)==1",
                    "old_namespace.replace(prior_manifest,new_manifest)==", "old_authenticated.count(sha(arm_namespace))==1",
                    "old_authenticated.replace(sha(arm_namespace),sha(work/'scripts/build_with_mathlib_overlay.py'))==",
                    "save(work/'PARENT-WRAPPER-EQUIVALENCE.json',equivalence)", "['actual_parent_source_equivalence']",
                    "'preparation_sha256':sha(work/'PREPARATION.json')"], 'full exact two-literal parent equivalence recorded and pinned before plan freeze')
    original_installer=P/'lean/scripts/prepare_cache_install_transport_history_1497.py'
    installer_tree=ast.parse(original_installer.read_text())
    method=next(ast.literal_eval(n.value) for n in installer_tree.body if isinstance(n,ast.Assign) and
                any(isinstance(t,ast.Name) and t.id=='INSTALL_METHOD' for t in n.targets))
    parent_prep=json.loads((PARENT/'PREPARATION.json').read_bytes())
    templates=PARENT/parent_prep['cache_install_transport_derivation']['evidence']
    template_pins=[pin(templates/'ORIGINAL-NAMESPACE-OVERLAY.py','09b24ef22790f14e0fa7bc3ae6b0a9c2b1fe8d2d9cbfdfae5333b0dd566536c0'),
                   pin(templates/'ORIGINAL-AUTHENTICATED-OVERLAY.py','ffc577ca31389936554dd64b53664452f6274b910fc5508b6c246a5709a993cc'),
                   pin(ARM/'scripts/build_with_mathlib_overlay.py','3d613f389158ad106741f72660429a6de28a18da498480c38072ce92b62c0a67'),
                   pin(ARM/'scripts/build_with_authenticated_overlay.py','5406eb1a68e8f6e35729f8ae991906213cf1e4f2628f6ce4aac019f8ee25ac46')]
    raw_namespace=(templates/'ORIGINAL-NAMESPACE-OVERLAY.py').read_text()
    start=raw_namespace.index('    def install(self, base, out, expected):'); end=raw_namespace.index('    def dependencies(',start)
    projected=raw_namespace[:start]+method+raw_namespace[end:]
    require(projected.count('sha = lambda p:')==1,'one installer constant insertion marker')
    projected=projected.replace('sha = lambda p:',"CACHE_INSTALL_MANIFEST_SHA = "+repr('0'*64)+'\nsha = lambda p:')
    accepted=(ARM/'scripts/build_with_mathlib_overlay.py').read_text()
    arm_prep=json.loads((ARM/'PREPARATION.json').read_bytes()); manifest=arm_prep['cache_install_transport_derivation']['alias_manifest_sha256']
    require(accepted.count(manifest)==1 and accepted.replace(manifest,'0'*64)==projected, 'independent full namespace projection changes ONLY one manifest literal')
    projected_auth=(templates/'ORIGINAL-AUTHENTICATED-OVERLAY.py').read_text().replace(template_pins[0]['sha256'],sha(projected.encode()))
    accepted_auth=(ARM/'scripts/build_with_authenticated_overlay.py').read_text()
    require(accepted_auth.count(template_pins[2]['sha256'])==1 and
            accepted_auth.replace(template_pins[2]['sha256'],sha(projected.encode()))==projected_auth, 'independent full auth projection changes ONLY dependent BASE literal')
    guard_pin=pin(P/'lean/scripts/guard_g7_survival_run_20261010_v2.py','4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4')
    main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
    before=[ast.literal_eval(n.value) for n in main.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='before']
    after=[ast.literal_eval(n.value) for n in main.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='after']
    require(len(before)==4 and len(after)==3,'exact frozen template derivative markers')
    raw_guard=Path(guard_pin['path']).read_text()
    require(raw_guard.count(before[2])==raw_guard.count(before[3])==1,'one phase and one prelaunch gate marker')
    projected_guard=raw_guard.replace(before[2],"choices=['natural']").replace(before[3],after[2])
    ast.parse(projected_guard)
    require("prep['additional_storage_input_pins'].items()" in projected_guard and "sha(row['path']) == row['sha256']" in projected_guard,
            'gate/equivalence/policy/source evidence rehashed immediately before guarded launch')
    reserves=[32,4,16,16,8]
    require(sum(reserves)*2**20==freeze['resource_incremental_reserve_bytes']==79691776 and
            freeze['packet_export_headroom_bytes']==8388608 and 'Actual narrow extraction component/aggregate/audit:4GiB/180s' in freeze['ordinary_caps_unchanged'], 'resource reserve and actual narrow cap statement')
    return {'status':'PASS_FINAL_V3_PREPARER_V4_METADATA_AND_EXACT_CORE_FACADE_SOURCE_ONLY',
            'freeze':freeze_pin,'source_and_measurement_pins':source_pins,'preserved_predecessor_pins':old,'independent_gate_evidence':qc_refs,
            'parent_template_and_accepted_pins':template_pins,'original_guard_pin':guard_pin,'projected_new_guard_sha256':sha(projected_guard.encode()),
            'partition':{'executed':141,'accepted1504':138,'separate_accepted_parallel_arm':1,'new_sources':2,'staged':145,'guard_only':4,'warm_staged':143},
            'reserved_bytes':79691776,'packet_export_headroom_bytes':8388608,'actual_narrow_caps':{'memory_mib':4096,'seconds':180},
            'checked_properties':['exact natural V2 sources/parents/imports; guard-only records disjoint and never requested as target',
                'root gate and every evidence SHA checked during preparation and immediately before mathematical launch',
                'same authenticated.original.core object in launcher composition',
                'full namespace/auth source equality limited to one cache-manifest literal and its one dependent BASE hash literal; explicit equivalence receipt and actual runtime pins',
                'independent in-memory AST-literal installer projection agrees with accepted ARM sources under only those two exact replacements',
                'guard only changes natural phase choice and adds input-pin checks; resource thresholds, process-group cleanup and final gates retained',
                '76MiB reserve and all fixed byte-trial allocation roots included; current resource measurement/actual prepared plan remain separate gates'],
            'qualifications':['This reader imported or ran no preparer, installer, seeder, Builder, guard, compiler or provider. Projected source strings stayed in memory and were only AST-parsed.',
                'The new context parent SHA will differ from accepted5406/3d613 because its immutable alias manifest differs. Acceptance is the exact two-literal derivation, never literal runtime parent hash equality or generic body normalization.',
                'Preparation needs root concrete capture gate containing actual source/saved-byte evidence and all fixed codec8/portable9/loader15 allocation roots. The frozen command still has root-owned gate placeholders.',
                'Actual preparation must preserve the new equivalence/seed/transport/graph/resource receipts for review. Mathematical execution needs a separately root-approved actual plan.',
                'The extraction target retains4GiB/180s for components, aggregate and audit. Connected-label6GiB/300s is an unchanged separate core branch.',
                'Historical static resource values are dated observations, not current budget approval; no coherent union count or mathematical acceptance is established.']}

def main():
    result={'schema':'natural141_preparer_and_storage_facade_independent_static_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
            'target_modules_imported':False,'preparation_or_compiler_processes_started':0,'new_context_materialized':False,'mathematical_acceptance_modified':False}
    try: result.update(check())
    except Exception as error: result.update(status='FAIL_STATIC_QC',error_type=type(error).__name__,error=str(error))
    path=Path(sys.argv[1])
    with path.open('x') as handle: json.dump(result,handle,indent=2,sort_keys=True); handle.write('\n')
    print(json.dumps({'path':str(path),'sha256':sha(path.read_bytes()),'status':result['status']}))

if __name__=='__main__': main()
