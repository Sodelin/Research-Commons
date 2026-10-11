#!/usr/bin/env python3
"""Read-only saved preparation checks; never launches its guard or helpers."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W=Path('/dev/shm/rc-lean-g6-natural-common-20261011T002733.947509Z')

def require(value,label):
    if not value:raise AssertionError(label)

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as handle:
        while piece:=handle.read(65536):h.update(piece)
    return h.hexdigest()

def pin(path,expected=None):
    path=Path(path); actual=sha(path); require(expected is None or actual==expected,'pin '+str(path))
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':actual}

def read(path):return json.loads(Path(path).read_bytes())

def companion(base,suffix):
    return base.with_suffix(suffix) if suffix in ('.olean','.ilean','.ir') else Path(str(base)+suffix[len('.olean'):])

def check():
    plan_pin=pin(W/'RESOURCE-AND-RUN-PLAN.json','1bda1226b7c3ae21427df81ea11af62f6ec6751881e8fb1ad627cff2e23645ec')
    plan=read(plan_pin['path']); prep_pin=pin(W/'PREPARATION.json',plan['preparation_sha256']); prep=read(prep_pin['path'])
    graph_pin=pin(W/'DEPENDENCY-GRAPH.json',plan['graph_sha256']); graph=read(graph_pin['path'])
    source_qc_pin=pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/NATURAL141-PREPARER-V3-FACADE-STATIC-QC-ATTEMPT1.json','fbc8d2ca0111b2accad87be86b96335e87a36f0f0036dc8782cbb893555c01ee')
    source_qc=read(source_qc_pin['path'])
    repair_qc_pin=pin(Path(__file__).with_name('A227-REPAIR-V5-PREPARER-STATIC-QC-ATTEMPT2.json'),'f9cb832971a6e47c96cb26e6729cb10f65c437373c54d8fb5b86fdca27d75df4')
    repair_qc=read(repair_qc_pin['path'])
    frozen=prep['scratch_location_derivation']['source_freeze']
    freeze_pin=pin(frozen['path'],frozen['sha256']);require(frozen['sha256']=='e3391d165f5f3253a6de2876544ac6568dca3013cbc5d294a6cd55c9a4f39b41','exact repairedV4 source freeze')
    freeze=read(frozen['path'])
    guard_pin=pin(plan['monitor_path'],plan['monitor_sha256']); require(guard_pin['sha256']==source_qc['projected_new_guard_sha256'],'exact reviewed guard source')
    launcher_pin=pin(plan['launcher'],plan['launcher_sha256']); require(launcher_pin['sha256']=='1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c','exact core-binding facade')
    evidence=[pin(r['path'],r['sha256']) for r in prep['additional_storage_input_pins'].values()]
    equivalence=read(prep['runtime_parent_derivation']['path'])
    for name in ('namespace','authenticated'):
        old,new=equivalence['accepted_'+name],equivalence['actual_'+name]; replacement=equivalence[name+'_exact_replacement']
        pin(old['path'],old['sha256']);pin(new['path'],new['sha256'])
        a,b=Path(old['path']).read_text(),Path(new['path']).read_text()
        require(replacement['occurrences']==a.count(replacement['old'])==1 and a.replace(replacement['old'],replacement['new'])==b,
                'actual full source differs only by exact one '+name+' hash literal')
    target=graph['targets'][plan['phases']['natural']['target']]; guards=graph['targets']['context/protected-mathlib-providers']
    modules={**target['modules'],**guards['modules']}; fresh=read(W/'FRESH-SOURCES.json')
    require(len(target['modules'])==len(target['order'])==141 and len(guards['modules'])==4 and len(modules)==145 and len(fresh)==2 and
            not (set(target['modules'])&set(guards['modules'])) and prep['requested_targets']==[plan['phases']['natural']['target']], '141 executed/4 guard-only disjoint/2new')
    require({r['module']:r['sha256'] for r in freeze['sources']}=={n:r['sha256'] for n,r in fresh.items()},'actual new roots exactly a227/fcad')
    require({r['module']:r['sha256'] for r in repair_qc['parent_source_pins']}=={r['module']:r['sha256'] for r in freeze['exact_composition']['accepted_providers']},'same139 accepted source pins')
    for r in freeze['exact_composition']['accepted_providers']:
        require((r['sha256'],r['imports'])==(target['modules'][r['module']]['sha256'],target['modules'][r['module']]['imports']),'actual139 provider/source/import selection')
    require(Path(prep['additional_storage_input_pins']['capture_gate']['path']).is_absolute(),'absolute capture gate removes relative-cwd qualification')
    require({'/dev/shm/rc-lean-g6-natural-common-20261011T001250.195773Z','/dev/shm/rc-lean-g6-natural-common-20261011T002247.540229Z'}<=set(plan['allocation_roots']),'both failed contexts preserved and counted')
    closure=read(W/'SOURCE-CLOSURE.json'); require(len(closure)==145 and {r['module'] for r in closure}==set(modules),'145 exact staged sources')
    for r in closure:
        require(r['sha256']==modules[r['module']]['sha256'] and r['imports']==modules[r['module']]['imports'],'exact staged graph source/import metadata')
        pin(r['scratch_source'],r['sha256']);pin(r['preserved_source'],r['sha256'])
        require(re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',Path(r['scratch_source']).read_text(),re.M)==r['imports'],'staged literal imports')
    selection=read(W/'SELECTED-CACHE-IDENTITIES.json'); require(len(selection)==143 and {r['module'] for r in selection}==set(modules)-set(fresh),'143 exact warm cache records')
    artifact_count=0
    for r in selection:
        old=Path(r['cache_entry'])/'receipt.json'; new=W/'.build/cache'/r['cache_key']/'receipt.json'
        pin(old,r['receipt_sha256']);pin(new,r['receipt_sha256']); require(old.read_bytes()==new.read_bytes(),'unchanged exact selected receipt bytes')
        rec=read(old);require(rec['source_sha256']==modules[r['module']]['sha256'] and rec['object_artifacts']==r['object_artifacts'],'selected source/bundle')
        for suffix,digest in r['object_artifacts'].items():
            pin(companion(Path(r['cached_object']),suffix),digest);pin(companion(new.parent/'artifact.olean',suffix),digest);artifact_count+=1
    budget=plan['budget']; require(budget['planned_conservative_combined_bound_bytes']==budget['conservative_followed_target_prior_bytes']+sum(budget['new_allocation_reserves'].values())==1786318848,
                                'dated exact budget arithmetic')
    require(plan['scratch_abort_bytes']==2013265920 and plan['scratch_hard_limit_bytes']==2147483648 and plan['memory_abort_bytes']==16106127360 and
            len(plan['allocation_roots'])==21 and budget['packet_export_transient_reserve_bytes']==8388608,'unchanged21-root resource policy')
    gate=read(prep['additional_storage_input_pins']['capture_gate']['path'])
    require(set(gate['byte_trial_allocation_roots'])<=set(plan['allocation_roots']) and len(gate['byte_trial_allocation_roots'])==7,'all seven fixed byte support roots counted')
    return {'status':'PASS_SAVED_PREPARATION_SOURCE_TRANSPORT_PARENT_EQUIVALENCE_AND_DATED_BUDGET_ONLY',
            'repair_source_static_gate':repair_qc_pin,'actual_freeze':freeze_pin,
            'plan':plan_pin,'preparation':prep_pin,'graph':graph_pin,'reviewed_source_gate':source_qc_pin,'guard':guard_pin,'facade':launcher_pin,
            'prelaunch_storage_input_pins':evidence,'parent_equivalence':equivalence,'staged_sources_checked':145,'executed_modules_planned':141,
            'warm_cache_receipt_pairs_checked':143,'original_and_staged_artifact_pairs_checked':artifact_count,'fresh_source_modules':sorted(fresh),
            'dated_conservative_bound_bytes':1786318848,'reserve_bytes':79691776,'allocation_roots_count':21,'fixed_byte_support_roots_count':7,
            'qualifications':['Saved preparation only. No guard, compiler, provider, seeder, installer or adapter was run by this reader.',
                'The original preparation/plan compiler_launched:false fields describe preparation time; this review does not infer current process state or mathematical results.',
                'Every cache receipt and artifact was inspected as retained bytes; actual source/import/native admissions must still be measured by the unchanged core during execution.',
                'Budget is the exact dated preparation arithmetic. Current resource viability and mathematical launch remain Root/scheduler gates.',
                'No generated declaration/audit/axiom count, theorem acceptance or coherent union scope is inferred.']}

def main():
    report={'schema':'natural141_saved_preparation_independent_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),
            'reviewer_sha256':sha(__file__),'target_modules_imported':False,'preparer_guard_or_compiler_processes_started':0,'mathematical_acceptance_modified':False}
    try:report.update(check())
    except Exception as error:report.update(status='FAIL_SAVED_PREPARATION_QC',error_type=type(error).__name__,error=str(error))
    destination=Path(sys.argv[1])
    with destination.open('x') as handle:json.dump(report,handle,indent=2,sort_keys=True);handle.write('\n')
    print(json.dumps({'path':str(destination),'sha256':sha(destination),'status':report['status']}))

if __name__=='__main__':main()
