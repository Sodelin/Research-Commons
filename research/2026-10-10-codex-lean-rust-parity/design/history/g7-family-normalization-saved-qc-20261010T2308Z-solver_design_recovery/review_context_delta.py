#!/usr/bin/env python3
"""Check only the exact 19 saved audit context differences; execute no Lean.

Contributor: Codex / solver_design_recovery. This comparison checks the saved
audit metadata and exact source/artifact context bindings. It does not equate
arbitrary bodies, normalize arbitrary private constants or widen union1504.
"""
from datetime import datetime,timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

PACKET=Path(__file__).resolve().parents[3]
EVIDENCE=PACKET/'lean/evidence/proof-extensions/g7-family-normalization/rc-lean-g7-family-normalization-20261010T230143.534018Z/81DC-PASS-MINIMAL168-EXPORT-V2-20261010T230235.850157Z'
OLD_ALIAS='_private.UnifiedLean.G6.PrivateRegisterCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
NEW_ALIAS='_private.UnifiedLean.Source.SourceInitializedCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
ALIAS_ROW='UnifiedLean.Source.SourceCalendarCompiler.calendarTail.eq_def'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def demand(condition,description):
    if not condition:
        raise AssertionError(description)


def read_raw(path):
    data=path.read_bytes()
    return gzip.decompress(data) if path.suffix=='.gz' else data


def check():
    parent_path=PACKET/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'
    parent=json.loads(parent_path.read_bytes())
    parent_target=parent['targets']['current/connected']
    parent_audit_path=PACKET/'lean'/parent['evidence']/parent_target['audit_distribution']
    parent_audit_raw=read_raw(parent_audit_path)
    demand(sha(parent_audit_raw)==parent_target['audit_raw_sha256'],'accepted parent audit binding')
    old={d['name']:d for d in json.loads(parent_audit_raw)['declarations']}
    family_audit_path=EVIDENCE/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json.gz'
    family_audit_raw=read_raw(family_audit_path)
    new={d['name']:d for d in json.loads(family_audit_raw)['declarations']}
    root_prefix='GProgram.G7.OriginalFamilyCalendarNormalization.'
    new_root=[name for name in new if name.startswith(root_prefix)]
    demand(len(new_root)==9,'nine owned root rows including generated positivity proof')
    inherited={name:d for name,d in new.items() if name not in new_root}
    demand(len(inherited)==4898 and all(name in old for name in inherited),'all narrow-context inherited names')
    differences=[]
    for name,d in inherited.items():
        before=old[name]
        demand(set(before)==set(d),'unchanged metadata field set')
        changed={key:[before[key],d[key]] for key in before if before[key]!=d[key]}
        if changed:
            differences.append({'name':name,'differences':changed})
    declared_path=PACKET/'quality/evidence/family-root-reviewer-preflight-1/FAILURE.json'
    declared=json.loads(declared_path.read_bytes())
    demand(len(differences)==19 and {x['name']:x['differences'] for x in differences}==
        {x['name']:x['differences'] for x in declared['differences']},'independently reproduce exactly root saved19 delta')
    owners=[]
    alias=None
    for item in differences:
        name,changed=item['name'],item['differences']
        if name==ALIAS_ROW:
            demand(set(changed)=={'body_references'},'only exact private-splitter body-reference difference')
            before,after=changed['body_references']
            demand(len(before)==len(after),'same body-reference count')
            positions=[i for i,(a,b) in enumerate(zip(before,after)) if a!=b]
            demand(len(positions)==1 and before[positions[0]]==OLD_ALIAS and after[positions[0]]==NEW_ALIAS,
                'exactly one qualified private splitter alias')
            alias={'name':name,'body_reference_index':positions[0], 'old_private_alias':OLD_ALIAS,
                'new_private_alias':NEW_ALIAS,'all_other_metadata_fields_identical':True}
        else:
            demand(set(changed)=={'module'} and re.search(r'(?:\.eq_[0-9]+|\.congr_simp)$',name),
                'only named generated equation/congruence owner attribution')
            demand(old[name]['kind']==new[name]['kind']=='theorem','generated rows remain theorems')
            demand(old[name]['type_references']==new[name]['type_references'] and
                old[name]['axioms']==new[name]['axioms'] and old[name]['body_references']==new[name]['body_references'],
                'generated owner rows retain type/axiom/body-reference metadata')
            owners.append({'name':name,'old_owner_module':changed['module'][0],
                'new_owner_module':changed['module'][1],'all_other_metadata_fields_identical':True})
    demand(len(owners)==18 and alias is not None,'exact18+1 classification')
    demand(OLD_ALIAS in old and NEW_ALIAS in old,'both exact private splitter declarations already in accepted1504')
    old_splitter,new_splitter=old[OLD_ALIAS],old[NEW_ALIAS]
    demand({k:v for k,v in old_splitter.items() if k not in {'name','module'}}==
        {k:v for k,v in new_splitter.items() if k not in {'name','module'}},
        'both parent private splitter declarations have identical remaining audited fields')
    graph=json.loads(read_raw(EVIDENCE/'DEPENDENCY-GRAPH.json.gz'))
    selected=graph['targets']['extraction/g7-original-family-calendar-normalization']['modules']
    parent_owner_filtered={name for name,d in old.items() if d['module'] in selected}
    demand(len(parent_owner_filtered)==4882 and not(parent_owner_filtered-set(inherited)) and
        len(set(inherited)-parent_owner_filtered)==16,'exact16 additional inherited labels under owner reassignment')
    for module,record in selected.items():
        if module!='G7OriginalFamilyCalendarNormalization':
            demand(parent['source_pins'][module]==record['sha256'],'all167 inherited source identities retained')
    actual=EVIDENCE/'attempts/00003-OwnedAudit/work/OwnedAudit.lean'
    demand('environment.getModuleIdxFor? name' in actual.read_text(),'auditor records context module-index attribution')
    return {'status':'PASS_EXACT_19_SAVED_AUDIT_CONTEXT_DELTA',
        'parent_certificate_sha256':sha(parent_path.read_bytes()),'accepted_parent_audit_raw_sha256':sha(parent_audit_raw),
        'family_audit_raw_sha256':sha(family_audit_raw),'root_preflight_failure_sha256':sha(declared_path.read_bytes()),
        'inherited_rows':4898,'strictly_identical_complete_records':4879,'different_records':19,
        'generated_owner_module_only_differences':owners,'private_splitter_alias_only_difference':alias,
        'both_parent_private_splitter_declarations_equal_except_name_and_module':True,
        'old_context_owner_filtered_rows':4882,'additional_existing_names_from_owner_reassignment':16,
        'all_inherited_type_reference_and_axiom_metadata_identical':True,
        'all_other_inherited_record_fields_identical_except_the_exact_19_listed_fields':True,
        'qualified_classification':'Eighteen generated equation/congruence theorem owner-module attributions vary with the imported context. One generated calendarTail.eq_def record references the exact alternative private splitter alias at one position. Sources/import graph and inherited component bindings remain separately authenticated; these are exact saved metadata exceptions, not permission for arbitrary body changes.',
        'limits':['The audit reports used-constant lists, not full serialized type or proof expressions. This comparison does not prove arbitrary private aliases interchangeable.',
            'No general name normalization, body-reference relaxation, old1504 ownership retention claim or accepted-union widening is authorized.'],
        'new_root_owned_rows':9,'new_root_public_heads':8,'generated_positivity_theorems':1,
        'no_full_parent_metadata_retention_claim_for_narrow_context':True}


def main():
    receipt=Path(sys.argv[1])
    data={'schema':'family_saved_exact_audit_context_delta_qc_v1','contributor':'Codex / solver_design_recovery',
        'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
        'compiler_helper_evaluator_adapter_native_processes_started_by_reviewer':0,'accepted_union_modified':False}
    try:
        data.update(check())
    except Exception as error:
        data.update(status='FAIL_SAVED_REVIEW',error_type=type(error).__name__,error=str(error))
    with receipt.open('x') as f:
        json.dump(data,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({'status':data['status'],'receipt':str(receipt),'receipt_sha256':sha(receipt.read_bytes())}))
    return 1 if data['status']=='FAIL_SAVED_REVIEW' else 0


if __name__=='__main__':
    raise SystemExit(main())
