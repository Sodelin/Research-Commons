#!/usr/bin/env python3
"""Independent source/import/header/contract review; no Lean or target run."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import sys

REPO=Path('/workspace/Research-Commons')
ROOT=REPO/'research/2026-10-10-codex-lean-rust-parity'
PROPOSAL=ROOT/'lean/proposals/reuse-integration-20261010T2138Z/natural-common-factorization'
V1_SHA='61b69059626df1e410758343bdf1e4a2a99aedb1a292803adb2024057b8a7a5e'
V2_SHA='6a9c47ca70e504477ceb15cbbd98f9f819ffeb4f82805122a004f3b1daec5b49'

def demand(condition,reason):
    if not condition:
        raise AssertionError(reason)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def pin(path,expected=None):
    path=Path(path)
    raw=path.read_bytes()
    digest=sha(raw)
    demand(expected is None or digest==expected,'pin '+str(path))
    return {'path':str(path),'bytes':len(raw),'sha256':digest}

def without_comments(text):
    result=[]
    depth=0
    i=0
    while i<len(text):
        pair=text[i:i+2]
        if pair=='/-':
            depth+=1;result.extend('  ');i+=2
        elif pair=='-/' and depth:
            depth-=1;result.extend('  ');i+=2
        elif not depth and pair=='--':
            end=text.find('\n',i)
            if end<0:end=len(text)
            result.extend(' '*(end-i));i=end
        else:
            result.append(text[i] if not depth or text[i]=='\n' else ' ');i+=1
    demand(depth==0,'balanced Lean comments')
    return ''.join(result)

def imports(text):
    result=[]
    for line in without_comments(text).splitlines():
        match=re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$',line)
        if match:result.extend(match.group(1).split())
    return result

def check():
    old_pin=pin(PROPOSAL/'PROPOSAL-FREEZE.json',V1_SHA)
    new_pin=pin(PROPOSAL/'PROPOSAL-FREEZE-V2.json',V2_SHA)
    old=json.loads((PROPOSAL/'PROPOSAL-FREEZE.json').read_text())
    freeze=json.loads((PROPOSAL/'PROPOSAL-FREEZE-V2.json').read_text())
    correction=freeze['metadata_correction']
    demand(correction['previous_sha256']==V1_SHA and correction['old_recorded_entry']==old['sources'][1]['declarations'][0], 'explicit previous header correction')
    reconstructed=json.loads(json.dumps(freeze))
    reconstructed.pop('metadata_correction')
    reconstructed['sources'][1]['declarations'][0]=correction['old_recorded_entry']
    demand(reconstructed==old,'exactly one corrected recordEnd header/hash entry and no other change')
    demand(correction['corrected_entry']==freeze['sources'][1]['declarations'][0], 'exact corrected header entry')
    demand('UNCOMPILED' in freeze['status'] and freeze['execution']['Lean_compiler_calls']==0, 'uncompiled proposal scope')
    bindings=[pin(REPO/b['path'],b['sha256']) for b in freeze['acceptance_bindings']]
    parent=json.loads((ROOT/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json').read_text())
    arm_acceptance=json.loads((ROOT/'lean/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-ACCEPTANCE.json').read_text())
    demand(arm_acceptance['status']=='ACCEPTED_SEPARATE_ORIGINAL_PARALLEL_ARM_TRANSPORT_117'
           and not arm_acceptance['combined_union1504_changed'], 'accepted separate arm authority')
    providers=freeze['exact_composition']['accepted_providers']
    demand(len(providers)==len({p['module'] for p in providers})==139,'139 unique accepted parents')
    provider_pins=[]
    graph={}
    inherited_count=separate_count=0
    for row in providers:
        item=pin(REPO/row['path'],row['sha256'])
        item.update(module=row['module'],imports=imports(Path(item['path']).read_text()))
        demand(item['imports']==row['imports'],'literal parent imports '+row['module'])
        if row['module']=='G6OriginalParallelArmTransport':
            demand(row['sha256']==arm_acceptance['source']['sha256'] and row['acceptance']=='separate accepted117','separate exact f40 provider')
            separate_count+=1
        else:
            demand(parent['source_pins'][row['module']]==row['sha256'],'accepted1504 exact parent '+row['module'])
            inherited_count+=1
        graph[row['module']]=item['imports']
        provider_pins.append(item)
    demand((inherited_count,separate_count)==(138,1),'138 exact1504 plus one separate f40')
    source_pins=[]
    authored=[]
    source_bodies={}
    expected_sources={'G6OriginalCommonPrefix':'68e0130ba41f55a7d87d0d8847dff504d53e55fe947020214e57ba42702b010b',
                      'G6NaturalCommonForestFactorization':'fcadb6c4029b06eed32c8d037f294e373d1f91be692807fa477ccbc8edd75f2c'}
    for row in freeze['sources']:
        source=REPO/row['path']
        item=pin(source,expected_sources[row['module']])
        version=pin(REPO/row['immutable_version'],row['sha256'])
        demand(source.read_bytes()==Path(version['path']).read_bytes(),'exact immutable source version')
        text=source.read_text()
        code=without_comments(text)
        actual_imports=imports(text)
        demand(actual_imports==row['imports'],'literal new imports')
        demand(not re.search(r'\b(sorry|admit|axiom|unsafe|partial|native_decide)\b',code.replace('#print axioms','')), 'no new admitted/unsafe producer proof')
        matches=list(re.finditer(r'^(?:private )?(?:noncomputable )?(?:def|theorem)\s+(\w+)',code,re.M))
        demand([m.group(1) for m in matches]==[d['name'] for d in row['declarations']],'exact authored head order')
        for i,(match,d) in enumerate(zip(matches,row['declarations'])):
            end=matches[i+1].start() if i+1<len(matches) else len(text)
            span=text[match.start():end]
            header=span.split('\n  |',1)[0].strip() if d['name']=='recordEnd' else span.split(':=',1)[0].strip()
            demand(header==d['header'] and sha(header.encode())==d['sha256'],'strict actual header '+d['name'])
            demand(text[:match.start()].count('\n')+1==d['line'],'actual header line '+d['name'])
            authored.append({'module':row['module'],**d,'visibility':'private' if header.startswith('private ') else 'public',
                             'kind':'theorem' if re.search(r'\btheorem\b',header) else 'definition'})
            source_bodies[d['name']]=span
        source_pins.append({'current':item,'immutable_version':version,'literal_imports':actual_imports})
        graph[row['module']]=actual_imports
    demand(len(source_pins)==2 and len(authored)==29,'two new sources and29 authored heads')
    external=set()
    for module,parents in graph.items():
        for name in parents:
            if name not in graph:
                demand(name.startswith(('Mathlib.','Lean.')),'missing owned import '+module+':'+name)
                external.add(name)
    demand(sorted(external)==freeze['exact_composition']['protected_external_imports'],'exact external import list')
    reached=set();active=set()
    def visit(module):
        demand(module not in active,'import cycle')
        if module in reached:return
        active.add(module)
        for child in graph[module]:
            if child in graph:visit(child)
        active.remove(module);reached.add(module)
    visit('G6NaturalCommonForestFactorization')
    demand(reached==set(graph) and len(reached)==freeze['exact_composition']['closure_size']==141, 'independent complete reachable141')
    order=freeze['exact_composition']['topological_modules']
    demand(len(order)==len(set(order))==141 and set(order)==reached,'exact topological module inventory')
    positions={m:i for i,m in enumerate(order)}
    demand(all(positions[p]<positions[m] for m in graph for p in graph[m] if p in graph),'topological dependency order')
    demand('hprefix : NoPrivateWordRead' in source_bodies['actual_natural_common_erased_full_forest_factorization']
           and 'actual_private_seed_erased_history_product' in source_bodies['actual_natural_common_erased_full_forest_factorization']
           and 'actual_natural_stored_selector' in source_bodies['actual_natural_common_erased_full_forest_factorization'], 'natural support, seed and no-read bridge used')
    demand('actual_source_time_add' in source_bodies['actual_arm_baseline_residual']
           and 'add_tsub_cancel_of_le hle' in source_bodies['actual_arm_baseline_residual'], 'actual semigroup residual split')
    demand('actual_parallel_arm_full_forest_transport' in source_bodies['actual_arm_erased_reference']
           and 'original_epoch_eq_of_exposure_eq' in source_bodies['actual_arm_erased_reference'], 'actual original exposure and f40 transport')
    demand('originalRegister N coin h.val = coin h' in source_bodies['actual_natural_stored_selector'], 'same original stored selector')
    demand('hf : NoPrivateWordRead N P future' in source_bodies['actual_no_read_future_erased_full_forest'], 'explicit future guard')
    demand('hdates' in source_bodies['actual_before_node_noPrivateWordRead'] and 'hnodes' in source_bodies['actual_before_node_noPrivateWordRead']
           and '.Nodup' in source_bodies['actual_before_node_noPrivateWordRead'], 'actual date and tied-node duplicate exclusion')
    counts={'all_authored':29,'public':sum(d['visibility']=='public' for d in authored),
            'private_helpers':sum(d['visibility']=='private' for d in authored),
            'theorems':sum(d['kind']=='theorem' for d in authored),'definitions':sum(d['kind']=='definition' for d in authored),
            'public_theorems':sum(d['visibility']=='public' and d['kind']=='theorem' for d in authored)}
    demand(counts=={'all_authored':29,'public':21,'private_helpers':8,'theorems':20,'definitions':9,'public_theorems':12},'authored source-only counts')
    return {'status':'PASS_STATIC_SOURCE_IMPORT_HEADER_AND_SCOPED_CONTRACT_QC; proposals remain uncompiled',
            'original_freeze':old_pin,'corrected_freeze':new_pin,'exact_metadata_correction':correction,
            'accepted_evidence_bindings':bindings,'source_pins':source_pins,'parent_source_import_pins':provider_pins,
            'authored_declarations':authored,'authored_counts':counts,
            'independent_closure':{'modules':141,'accepted1504_parents':138,'separate_accepted_f40_parents':1,
                                  'new_roots':2,'all_reachable':True,'exact_literal_imports':True,'external_imports':sorted(external),
                                  'guard_staging_not_executed_closure':'sole scheduler must add exact protected Mathlib records separately'},
            'static_math_and_scope_findings':[
                'beforeNodeWord is the literal original calendar prefix through all earlier dates and all tied exits, ending before the selected node. hdates/hnodes and Nodup exclude an earlier occurrence of this selected register read without reordering.',
                'The fixed-Code local common law executes its actual stored register bit, not a Bernoulli mixture. actual_natural_stored_selector binds that same bit to the unchanged original natural initializer through every actual endpoint step, including empty prefix.',
                'The accepted private seed/erased-history product is used once. Old can read the entire erased initialized vector, including entering Code and all endpoint states. The private seed is marginalized; original true/parent1 gamma gives the residual weight.',
                'Each arm uses the accepted full-Code exposure theorem and exact f40 original E-occurrence transport, with V/Copy fixed and full carried unranked genealogy and every outside register slot retained.',
                'All actual live owners must be at the selected hybrid on the original entering-law support. No global/source-class population-support construction or outside-cohort rate rescaling is supplied.',
                'Positive physical arm exposures give a positive minimum baseline. The long-arm exposure minus short exposure is nonnegative and may be zero. Semigroup splitting allows algebraic identity at zero; it does not construct a positive identity edge.',
                'The longArm flag is selected by an explicit comparison. Residual probability is gamma when longArm=true and 1-gamma when false; no refitted or complemented original seed is introduced. Gamma endpoints are allowed by the stated unitInterval law.',
                'hparents identifies the actual original registry occurrence pair. The tied-calendar corollary proves the compiled prefix/common-node split and the separate local bigon law; it does not identify the whole generated calendar with that local bigonProgram.',
                'The future-erasure theorem retains explicit NoPrivateWordRead and runs the same source future from the erased original Code. Equality of forest/register endpoints alone does not identify different physical edge/location states.'
            ],
            'remaining':freeze['remaining_interfaces'],
            'additional_boundaries':['Local reference epochs are pre-exit. Full physical exit/context and carried-current-root/K-only insertion into actual future, and proper outside panels, remain downstream.',
                'Guarded bins retain actual supplied CutRefines/wordBinContract and constant-tag forest decoder requirements; arbitrary timed/bin exposure equality is not supplied.',
                'Separate narrow141 kernel/aggregate/owned-audit execution and ownership/context review remain required. No1504/1570 union is widened by this source receipt.',
                'No global legal positive short-chain reconstruction, executable extractor, runtime/source provenance, universal native refinement, or G6/G7 master closure is accepted.']}

def main():
    destination=Path(sys.argv[1])
    report={'schema':'g6_natural_common_independent_static_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
            'Lean_compiler_producer_native_reference_processes_started':0,'accepted_union_modified':False,
            'machine_verified_proof_claim_for_new_sources':False}
    try:report.update(check())
    except Exception as error:report.update(status='FAIL_STATIC_QC',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,indent=2,sort_keys=True,ensure_ascii=False);handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':sha(destination.read_bytes())}))
    return 1 if report['status']=='FAIL_STATIC_QC' else 0

if __name__=='__main__':raise SystemExit(main())
