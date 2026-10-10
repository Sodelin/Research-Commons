#!/usr/bin/env python3
"""Saved-byte/source-statement QC of family normalization; launch no Lean.

Contributor: Codex / solver_design_recovery, independent design/QC lane.
No compiler, helper, evaluator, source adapter, native process or proof producer
is imported or executed. Kernel evidence is the separately authenticated saved
run. Static statement review retains its exact supplied-family premises.
"""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

PACKET=Path(__file__).resolve().parents[3]
EVIDENCE=PACKET/'lean/evidence/proof-extensions/g7-family-normalization/rc-lean-g7-family-normalization-20261010T230143.534018Z/81DC-PASS-MINIMAL168-EXPORT-V2-20261010T230235.850157Z'
TARGET='extraction/g7-original-family-calendar-normalization'
MODULE='G7OriginalFamilyCalendarNormalization'
SOURCE='81dcd9983e73eecd5f59caac14ee6231825fdd9ae25dd9cf64bafbc06b6f2f08'
MANIFEST='c17ce6e69c520478304c3a8a9d87b20b3e745161a56ab3640f6c890a9eb25ff7'
PARENTS={'G7OriginalFamilyStrategy':'1a95edf6b4a0e361ccc053531fd24de4de45b6253a139b266e68d282c3fbecd5',
    'G7OriginalSurvivalCoverage':'59314f77f7c450321a8683bc938b6372e2c1450b6eb8b2d179a99ed696f362e9'}
FOUNDATIONS={'propext','Classical.choice','Quot.sound'}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def demand(condition, detail):
    if not condition:
        raise AssertionError(detail)


def raw(path):
    data=path.read_bytes()
    return gzip.decompress(data) if path.suffix=='.gz' else data


def read(path):
    return json.loads(raw(path))


def import_names(text):
    # Saved modules use ordinary leading import declarations; remove comments.
    text=re.sub(r'/\-.*?\-/','',text,flags=re.S)
    text=re.sub(r'--[^\n]*','',text)
    return [name for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M)
        for name in match.group(1).split()]


def check():
    manifest_path=EVIDENCE/'PRESERVATION-MANIFEST.json'
    demand(sha(manifest_path.read_bytes())==MANIFEST,'family preservation manifest identity')
    m=read(manifest_path)
    demand(len(m['preserved_files'])==60,'family preserved file count')
    total_stored=total_restored=compressed=0
    for item in m['preserved_files']:
        stored=(EVIDENCE/item['path']).read_bytes()
        demand(sha(stored)==item['sha256'] and len(stored)==item['bytes'],'stored binding: '+item['path'])
        restored=gzip.decompress(stored) if item.get('encoding')=='gzip' else stored
        if item.get('encoding')=='gzip':
            compressed+=1
            demand(sha(restored)==item['restored_sha256'] and len(restored)==item['restored_bytes'],
                'lossless gzip restoration')
        demand(sha(restored)==item['original_sha256'] and Path(item['original_path']).read_bytes()==restored,
            'raw original/restored preservation')
        total_stored+=len(stored);total_restored+=len(restored)
    demand(m['compiled_artifact_bytes_distributed'] is False and m['original_attempts_overwritten'] is False
        and m['protected_provider_context_executed'] is False,'preservation scope')
    final=read(EVIDENCE/'FINAL-RECEIPT.json')
    demand(final==m['final_receipt'] and final['status']=='PASS_ALL_REQUESTED_TARGETS' and
        final['targets_passed']==final['targets_requested']==[TARGET],'final saved target receipt')
    demand(final['counts']=={'cache_reuse':167,'fresh_components':1} and final['trust_level']==0
        and final['kernel_checking'] is True and final['compiler_identity_stable'] is True
        and final['native_runtime_final_rehash_stable'] is True,'actual fresh/reuse/kernel scope')
    graph_raw=raw(EVIDENCE/'DEPENDENCY-GRAPH.json.gz');graph=json.loads(graph_raw)
    demand(sha(graph_raw)==final['graph_sha256'],'saved graph identity')
    target=graph['targets'][TARGET]
    guards=graph['targets']['context/protected-mathlib-providers']
    demand(len(target['modules'])==len(target['order'])==168 and target['roots']==[MODULE],'executed family closure')
    demand(len(guards['modules'])==4 and guards['required_for_accepted_release'] is False and
        guards['status']=='PROTECTED_NAMESPACE_CONTEXT_ONLY_NOT_EXECUTED','four protected-provider context-only records')
    closure=read(EVIDENCE/'preparation/SOURCE-CLOSURE.json.gz')
    demand(len(closure)==172,'complete staging source closure')
    accepted=read(PACKET/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json')
    for item in closure:
        demand(sha(Path(item['scratch_source']).read_bytes())==item['sha256'] and
            sha(Path(item['preserved_source']).read_bytes())==item['sha256'],'source closure byte identity')
        demand(import_names(Path(item['preserved_source']).read_text())==item['imports'],'literal import identity')
        record=(target['modules'] if item['module'] in target['modules'] else guards['modules'])[item['module']]
        demand(record['sha256']==item['sha256'] and record['imports']==item['imports'],'graph/source closure consistency')
        if item['module']!=MODULE:
            demand(accepted['source_pins'][item['module']]==item['sha256'],'unchanged accepted parent source')
    freeze=read(PACKET/'lean/proposals/reuse-integration-20261010T2138Z/family-normalization/PROPOSAL-FREEZE.json')
    source_path=Path(freeze['source_path']);source=source_path.read_text()
    demand(freeze['sha256']==SOURCE==sha(source_path.read_bytes())==sha(Path(freeze['immutable_source_path']).read_bytes())
        ==sha((EVIDENCE/'sources'/f'{MODULE}.lean').read_bytes()),'frozen 81dc source and version')
    demand(import_names(source)==list(PARENTS),'two accepted parent imports')
    for module,pin in PARENTS.items():
        demand(accepted['source_pins'][module]==target['modules'][module]['sha256']==pin,'accepted exact parent versions')
    result_path=EVIDENCE/'targets/extraction_g7-original-family-calendar-normalization/RESULT.json.gz'
    result=read(result_path)
    demand((result['status'],result['roots'],result['closure_modules'],result['declarations'],result['theorems'])
        ==('PASS',1,168,4907,3072),'target counts')
    demand(len(result['component_receipts'])==168,'all selected component records')
    current_run=final['run']
    fresh=[r for r in result['component_receipts'] if r['receipt_directory'].startswith(current_run+'/')]
    demand(len(fresh)==1 and fresh[0]['module']==MODULE and fresh[0]['source_sha256']==SOURCE,'one current fresh component')
    for receipt in result['component_receipts']+[result['aggregate_receipt'],result['audit_receipt']]:
        demand(receipt['exit_code']==0 and receipt['source_and_imports_stable'] is True
            and receipt['compiler_sha256']==final['compiler_sha256'] and
            '-Ddebug.skipKernelTC=false' in receipt['command'],'saved kernel command/source binding')
        demand(receipt['native_runtime_digest']==final['native_runtime_digest'],'same observed native identity')
    for kind in ('aggregate_receipt','audit_receipt'):
        demand(result[kind]['receipt_directory'].startswith(current_run+'/'),'fresh aggregate/ownership audit')
    root=fresh[0]
    root_dir=EVIDENCE/'attempts/00001-G7OriginalFamilyCalendarNormalization'
    demand(read(root_dir/'receipt.json')==root,'saved fresh root receipt identity')
    for module,binding in root['direct_import_bindings'].items():
        demand(module in PARENTS and sha(Path(binding['path']).read_bytes())==binding['sha256'],
            'actual direct parent object binding')
    audit=read(EVIDENCE/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json.gz')
    demand(audit['selected_modules']==target['order'] and audit['owned_axioms']==[] and
        audit['nonstandard_axiom_rows']==[] and audit['missing_modules']==[],'complete owned audit gates')
    demand(audit['declaration_count']==len(audit['declarations'])==4907 and
        audit['theorem_declaration_count']==3072,'owned audit counts')
    for declaration in audit['declarations']:
        demand(set(declaration['axioms'])<=FOUNDATIONS,'nonstandard declaration foundation')
    actual_head_names=re.findall(r'^(?:noncomputable\s+)?(?:def|theorem)\s+([A-Za-z0-9_]+)',source,re.M)
    demand(actual_head_names==freeze['declaration_names'] and len(actual_head_names)==8,'eight unchanged public declaration heads')
    owned=[d for d in audit['declarations'] if d['module']==MODULE]
    namespace='GProgram.G7.OriginalFamilyCalendarNormalization.'
    demand({d['name'] for d in owned}=={namespace+n for n in actual_head_names}|{namespace+'normalizedFamily._proof_1'},
        'eight public heads plus one generated positivity proof')
    expected_dependencies={'normalizedFamily':'ratesFromSurvival',
        'actual_normalized_family_survival':'ratesFromSurvival_survival',
        'actual_normalized_family_completed_law':'actual_source_survival_chart',
        'actual_original_row_normalization':'actual_normalized_family_completed_law',
        'actual_original_programme_normalization':'actual_original_row_normalization',
        'actual_original_reset_response_normalization':'actual_original_programme_normalization',
        'actual_original_reset_experiment_normalization':'actual_original_reset_response_normalization',
        'actual_original_reset_history_normalization':'actual_original_reset_experiment_normalization'}
    heads=[]
    for name,dependency in expected_dependencies.items():
        declaration=next(d for d in owned if d['name']==namespace+name)
        demand(any(r.endswith('.'+dependency) for r in declaration['body_references']),
            'owned dependency chain: '+name)
        heads.append({'name':name,'kind':declaration['kind'],'body_dependency':dependency,
            'axioms':declaration['axioms']})
    guard_dir=next((EVIDENCE/'resource-guard').iterdir());guard=read(guard_dir/'RECEIPT.json')
    plan=read(EVIDENCE/'preparation/RESOURCE-AND-RUN-PLAN.json')
    demand(guard['status']=='PASS_UNCHANGED_BUILDER_EXIT_ZERO' and guard['exit_code']==0
        and guard['abort_reason'] is None and guard['monitor_error'] is None and
        guard['resource_caps_kernel_flags_core_or_audit_changed'] is False,'actual resource guard result')
    demand(guard['peak_distinct_inode_allocation_bytes']<plan['scratch_abort_bytes']<plan['scratch_hard_limit_bytes']
        and guard['peak_nonreclaimable_estimate_bytes']<plan['memory_abort_bytes'],'actual scoped resource measurements')
    for stream in ('stdout','stderr'):
        demand(sha((guard_dir/(stream+'.txt')).read_bytes())==guard[stream+'_sha256'],'guard output binding')
    post=read(EVIDENCE/'post-run/POST-RUN-TRANSPORT-REHASH-20261010T230235.850157Z.json.gz')
    demand(post['status']=='PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION' and
        post['selected_modules_verified']==168 and post['installed_same_filesystem_hardlinks']==168 and
        post['compiler_or_evaluator_invoked'] is False and post['accepted_inputs_modified'] is False,
        'saved post-transport record')
    demand(post['final_receipt_sha256']==sha((EVIDENCE/'FINAL-RECEIPT.json').read_bytes()),'post/final receipt binding')
    export_failure=EVIDENCE/'preparation/EXPORT-FAMILY-HEADROOM-PREFLIGHT-FAILURE-20261010.json'
    ef=read(export_failure)
    demand(ef['raw_run_originals_unmodified'] is True and ef['compiler_or_runtime_rerun'] is False,
        'old export-only preflight failure retained')
    early_failure=PACKET/'lean/G7-FAMILY-NORMALIZATION-81DC-PREFLIGHT-GUARDS-FAILED-20261010T225713.818482Z-RESULT.json'
    demand(early_failure.is_file(),'old protected-provider graph failure retained')
    # These assertions identify the independently read construction and all
    # downstream levels. They are static checks, not a second kernel proof.
    normalized=source.split('noncomputable def normalizedFamily',1)[1].split('variable (F',1)[0]
    demand('rates s := ratesFromSurvival' in normalized and 'row' not in normalized
        and 'programme' not in normalized,'one normalized bank per s before rows/programmes')
    demand('C₀ : ∀ s, Calendar (F.network s).graph' in source and
        'fun law : PMF (Code (F.network s) sample)' in source and
        '(programme a).weights.bind' in source and 'law.bind ((programme a).channel row)' in source,
        'supplied calendar/full Code/PMF map/bind construction')
    return {'status':'PASS_INDEPENDENT_SAVED_FAMILY_NORMALIZATION_DESIGN_QC',
        'manifest_sha256':MANIFEST,'preserved_files':60,'stored_bytes':total_stored,
        'restored_bytes':total_restored,'gzip_restorations':compressed,'all_original_and_restored_bytes_checked':True,
        'source_sha256':SOURCE,'proposal_freeze_sha256':sha((PACKET/'lean/proposals/reuse-integration-20261010T2138Z/family-normalization/PROPOSAL-FREEZE.json').read_bytes()),
        'accepted_parents':PARENTS,'staging_graph_modules':172,'executed_closure_modules':168,
        'protected_guard_providers':4,'protected_provider_context_executed':False,
        'owned_declarations':4907,'owned_theorems':3072,'public_heads':heads,
        'root_owned_declarations':9,'root_generated_positivity_theorems':1,
        'fresh_components':1,'authenticated_reused_components':167,'fresh_aggregate_and_owned_audit':True,
        'trust_level':0,'owned_axioms':0,'nonstandard_axiom_rows':0,'missing_modules':0,
        'compiler_sha256':final['compiler_sha256'],'observed_native_runtime_digest':final['native_runtime_digest'],
        'resource_guard_sha256':sha((guard_dir/'RECEIPT.json').read_bytes()),
        'post_transport_raw_sha256':sha(raw(EVIDENCE/'post-run/POST-RUN-TRANSPORT-REHASH-20261010T230235.850157Z.json.gz')),
        'preserved_pre_target_guard_failure_sha256':sha(early_failure.read_bytes()),
        'preserved_export_only_preflight_failure_sha256':sha(export_failure.read_bytes()),
        'premises':freeze['premises'],
        'scope':'Supplied strict comparison calendar C0(s), one ratesFromSurvival bank for each original source point s before masks/rows/programmes. Same completed-Code PMF, finite original-ID row and programme laws, same supplied reset Experiment fields and whole-history Consistent predicate.',
        'qualifications':['The supplied admitted predicate and target are reused as the same fields; this is no independent decoder or proof that a new encoded source satisfies scientific admission.',
            'C0 is supplied per source point. No effective uniform canonical-calendar selector is constructed.',
            'Completed-Code PMF equality is not a mixture theorem for a fixed full Code containing a preselected private bit.',
            'No timed/binned retiming, independent-segment coordinates, polynomial/compiler/runtime refinement, QE/census/policy algorithm or G6/G7 master closure.',
            'Original source comments remain frozen. Current compilation acceptance comes only from the authenticated dated saved run.',
            'Counts describe this narrow context, overlap accepted parents and do not widen the accepted1504 union.'],
        'accepted_union_changed_by_reviewer':False}


def main():
    receipt_path=Path(sys.argv[1])
    report={'schema':'g7_family_normalization_saved_design_qc_v1','contributor':'Codex / solver_design_recovery',
        'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
        'compiler_helper_evaluator_adapter_native_processes_started_by_reviewer':0}
    try:
        report.update(check())
    except Exception as error:
        report.update(status='FAIL_SAVED_REVIEW',error_type=type(error).__name__,error=str(error))
    with receipt_path.open('x') as handle:
        json.dump(report,handle,sort_keys=True,indent=2);handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path.read_bytes())}))
    return 1 if report['status']=='FAIL_SAVED_REVIEW' else 0


if __name__=='__main__':
    raise SystemExit(main())
