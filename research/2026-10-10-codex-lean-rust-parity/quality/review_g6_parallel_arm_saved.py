#!/usr/bin/env python3
"""Review the narrow original parallel-arm kernel/audit evidence without starting Lean."""
import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path

from check_source_graph import imports
from review_survival_union import AUDIT, CORE, Evidence, checked, load, preservation_review, review_transport, sha


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parents[1]
    result_path = packet / 'lean/G6-PARALLEL-ARM-TRANSPORT-F40-PASS-MINIMAL117-20261010T232230.265801Z-RESULT.json'
    certificate_path = packet / 'lean/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-CERTIFICATE.json'
    require(sha(result_path.read_bytes()) == '46162cec63db9ee00eeed58d65a056ff276cc19d66fa773e3b584bfb3136b8b4', 'Result pin')
    require(sha(certificate_path.read_bytes()) == 'b8436ddfd5b53fae8d6d26a1931d262a85df4758ca3aa62057e1f50e00af6210', 'Certificate pin')
    item = Evidence(result_path)
    preservation = preservation_review(result_path)
    certificate = load(certificate_path)
    final = item.manifest['final_receipt']
    label = 'extraction/g6-original-parallel-arm-transport-f40a0d66'
    require(final['targets_requested'] == final['targets_passed'] == [label] and
            final['counts'] == {'cache_reuse': 116, 'fresh_components': 1}, 'Target/freshness')
    graph = item.json('DEPENDENCY-GRAPH.json')
    selected = graph['targets'][label]
    protected = graph['targets']['context/protected-mathlib-providers']['modules']
    require(len(selected['modules']) == len(selected['order']) == 117 and len(protected) == 4,
            'Executed versus protected context')
    prefix = 'targets/' + re.sub('[^A-Za-z0-9_-]', '_', label) + '/'
    target = item.json(prefix + 'RESULT.json')
    receipts = {r['module']: r for r in target['component_receipts']}
    require(target['status'] == 'PASS' and target['closure_modules'] == 117 and
            len(receipts) == len(target['component_receipts']) == 117 and
            set(receipts) == set(selected['modules']) == set(selected['order']), 'Complete selected modules')
    audit_output = target['audit_receipt']['auxiliary_outputs'][0]
    audit_relative = Path(target['audit_receipt']['receipt_directory']).relative_to(Path(item.manifest['actual_run'])) / audit_output['path']
    audit_raw = item.raw(str(audit_relative))
    require(sha(audit_raw) == audit_output['sha256'] == certificate['targets'][label]['audit_raw_sha256'], 'Audit binding')
    audit = json.loads(audit_raw)
    require(audit['selected_modules'] == selected['order'] and
            audit['declaration_count'] == len(audit['declarations']) ==
            len({r['name'] for r in audit['declarations']}) == target['declarations'] == 3063 and
            audit['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in audit['declarations']) ==
            target['theorems'] == 1976, 'Complete owned inventory')
    require(not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and
            not audit['missing_modules'], 'Axioms or missing modules')
    root_name = 'G6OriginalParallelArmTransport'
    root = receipts[root_name]
    require(root['source_sha256'] == certificate['root_source_pin'] ==
            'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc' and
            Path(root['receipt_directory']).is_relative_to(Path(item.manifest['actual_run'])), 'Fresh root source')
    for row in (root, target['aggregate_receipt'], target['audit_receipt']):
        require(checked(row, final['compiler_sha256'], final['native_runtime_digest']) and
                Path(row['receipt_directory']).is_relative_to(Path(item.manifest['actual_run'])), 'Fresh strict root/aggregate/audit')
    require(final['trust_level'] == 0 and final['kernel_checking'] and
            final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable'], 'Strict stable compiler')
    prep = item.json('preparation/PREPARATION.json')
    require(prep['builder_sha256'] == sha(item.raw('BUILDER.py')) == CORE and
            prep['audit_template_sha256'] == sha(item.raw('AuditTemplate.lean')) == AUDIT and
            sha(item.raw('DEPENDENCY-GRAPH.json')) == prep['graph_sha256'] == final['graph_sha256'], 'Frozen core/audit/graph')
    require(sha(item.raw('NAMESPACE-OVERLAY-WRAPPER.py')) == prep['namespace_overlay_wrapper_sha256'] and
            sha(item.raw('AUTHENTICATED-OVERLAY-WRAPPER.py')) == prep['optimized_overlay_sha256'] and
            not prep['namespace_adapter_derivation']['compiler_kernel_cache_and_resource_policies_changed'], 'Namespace/storage policy')
    closure = {r['module']: r for r in item.json('preparation/SOURCE-CLOSURE.json')}
    require(len(closure) == 121 and set(closure) == set(receipts) | set(protected), 'Staged closure')
    for name, model in selected['modules'].items():
        raw = Path(closure[name]['scratch_source']).read_bytes()
        row = receipts[name]
        require(sha(raw) == model['sha256'] == row['source_sha256'] and imports(raw.decode()) == model['imports'], 'Source/import: ' + name)
        require(checked(row, final['compiler_sha256'], final['native_runtime_digest']), 'Component context: ' + name)
        for imported in model['imports']:
            if imported in receipts:
                require(row['direct_import_sha256'][imported] == receipts[imported]['object_sha256'], 'Compiled import: ' + name)
    parent_result = packet / 'lean/G7-SURVIVAL-COHERENT-PASS-UNION1504-EXPORT-V5-20261010T223805.816906Z-RESULT.json'
    parent = Evidence(parent_result)
    parent_modules = parent.json('DEPENDENCY-GRAPH.json')['targets']['current/connected']['modules']
    for name in closure:
        if name != root_name:
            model = selected['modules'].get(name, protected.get(name))
            require(model == parent_modules[name], 'Parent1504 graph record: ' + name)
    parent_certificate = load(Path(certificate['parent1504_certificate']['path']))
    require(sha(Path(certificate['parent1504_certificate']['path']).read_bytes()) == certificate['parent1504_certificate']['sha256'], 'Parent certificate')
    parent_audit = parent.json(parent_certificate['targets']['current/connected']['audit_distribution'].removesuffix('.gz'))
    old_records = {r['name']: r for r in parent_audit['declarations']}
    inherited = [r for r in audit['declarations'] if r['module'] != root_name]
    differences = []
    for row in inherited:
        old = old_records.get(row['name'])
        require(old is not None, 'Inherited name absent from parent audit')
        if old != row:
            differences.append({'name': row['name'], 'differences': {
                k: [old.get(k), row.get(k)] for k in set(old) | set(row)
                if old.get(k) != row.get(k)}})
    require(len(differences) == 11 and
            sha(json.dumps(differences, sort_keys=True, separators=(',', ':')).encode()) ==
            'aa90cd13fdcc18a73d4676ae99ee3955b71024cb53e480275a3ac3bffc4563fe',
            'Unqualified inherited audit-record differences')
    owner_names = set()
    old_alias = '_private.UnifiedLean.G6.PrivateRegisterCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
    new_alias = '_private.UnifiedLean.Source.SourceInitializedCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
    alias_records = [old_records[n] for n in (old_alias, new_alias)]
    require({k:v for k,v in alias_records[0].items() if k not in ('name', 'module')} ==
            {k:v for k,v in alias_records[1].items() if k not in ('name', 'module')},
            'Private splitter alias metadata differs')
    for difference in differences:
        fields = difference['differences']
        if set(fields) == {'module'}:
            require(re.search(r'\.(?:eq_[123]|congr_simp)$', difference['name']) is not None,
                    'Owner change is not a generated equation/congruence record')
            owner_names.add(difference['name'])
        else:
            require(difference['name'] == 'UnifiedLean.Source.SourceCalendarCompiler.calendarTail.eq_def'
                    and set(fields) == {'body_references'}
                    and [new_alias if n == old_alias else n for n in fields['body_references'][0]] ==
                    fields['body_references'][1], 'Unqualified proof-reference change')
    expected_inherited = [r for r in parent_audit['declarations'] if r['module'] in receipts]
    require({r['name'] for r in inherited} ^ {r['name'] for r in expected_inherited} <= owner_names,
            'Inherited names differ beyond generated owner reassignment')
    added = [r for r in audit['declarations'] if r['module'] == root_name]
    require(len(added) == 24 and sum(r['kind'] == 'theorem' for r in added) == 20 and not any(r['name'] in old_records for r in added), 'New owned declarations')
    guards = [item.json(k) for k in item.records if k.startswith('resource-guard/') and k.endswith('/RECEIPT.json')]
    plan = item.json('preparation/RESOURCE-AND-RUN-PLAN.json')
    require(len(guards) == 1, 'Guard receipt count')
    guard = guards[0]
    require(guard['exit_code'] == 0 and guard['abort_reason'] is None and guard['monitor_error'] is None
            and guard['monitor_sha256'] == 'ebc3612c1a85bffad688171968d5a0150495e5fbb61a045f25b60ce9c8b59077'
            and not guard['resource_caps_kernel_flags_core_or_audit_changed'] and
            guard['peak_distinct_inode_allocation_bytes'] < plan['scratch_abort_bytes'] and
            guard['peak_nonreclaimable_estimate_bytes'] < plan['memory_abort_bytes'], 'Resource guard')
    transport = review_transport(item, receipts, prefix)
    result = dict(status='PASS_EXACT_G6_PARALLEL_117_SAVED_KERNEL_AND_CONTEXT_REVIEW',
                  observed_utc=datetime.now(timezone.utc).isoformat(),
                  reviewer_sha256=sha(Path(__file__).read_bytes()),
                  result_manifest_sha256=sha(result_path.read_bytes()), certificate_sha256=sha(certificate_path.read_bytes()),
                  preservation=preservation, transport=transport,
                  executable_modules=117, staging_modules=121, protected_provider_target_executed=False,
                  owned_declarations=3063, theorem_declarations=1976, inherited_owned_records=len(inherited),
                  new_owned_heads=added, new_owned_count=24, new_owned_theorem_count=20,
                  public_source_heads=12, public_source_theorems=10, authored_heads=17,
                  qualified_parent_audit_record_differences=differences,
                  parent_audit_record_qualification='10 generated equation/congruence owner labels and one equation-theorem private splitter alias differ in the narrow context. All other inherited record fields, exact source/import records and compiled transports remain checked. No literal full-record retention or widened1504 claim.',
                  aggregate1504_widened=False, compiler_or_evaluator_called=False,
                  full_G6_or_G7_master_complete=False, universal_native_refinement_verified=False)
    with args.output.open('x') as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('preservation', 'new_owned_heads')}, sort_keys=True))


if __name__ == '__main__':
    main()
