#!/usr/bin/env python3
"""Authenticate saved G6 run bytes/metadata; never invoke Lean or providers."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

PACKET = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
EVIDENCE = PACKET / 'lean/evidence/proof-extensions/g6-parallel-arm-transport/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z/F40-PASS-MINIMAL117-20261010T232230.265801Z'
TARGET = 'extraction/g6-original-parallel-arm-transport-f40a0d66'
TARGET_DIR = EVIDENCE / 'targets/extraction_g6-original-parallel-arm-transport-f40a0d66'
MODULE = 'G6OriginalParallelArmTransport'
SOURCE = 'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc'
MANIFEST = '46162cec63db9ee00eeed58d65a056ff276cc19d66fa773e3b584bfb3136b8b4'
CERTIFICATE = 'b8436ddfd5b53fae8d6d26a1931d262a85df4758ca3aa62057e1f50e00af6210'
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}
OLD_ALIAS = '_private.UnifiedLean.G6.PrivateRegisterCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
NEW_ALIAS = '_private.UnifiedLean.Source.SourceInitializedCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
ALIAS_ROW = 'UnifiedLean.Source.SourceCalendarCompiler.calendarTail.eq_def'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def demand(condition, reason):
    if not condition:
        raise AssertionError(reason)

def raw(path):
    data = Path(path).read_bytes()
    return gzip.decompress(data) if Path(path).suffix == '.gz' else data

def read(path):
    return json.loads(raw(path))

def imports(text):
    text = re.sub(r'/\-.*?\-/','',text,flags=re.S)
    text = re.sub(r'--[^\n]*','',text)
    return [name for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)',text,re.M)
            for name in match.group(1).split()]

def check():
    demand(sha((EVIDENCE/'PRESERVATION-MANIFEST.json').read_bytes()) == MANIFEST, 'manifest identity')
    manifest = read(EVIDENCE/'PRESERVATION-MANIFEST.json')
    demand(len(manifest['preserved_files']) == 60, '60 preserved files')
    stored_bytes = restored_bytes = compressed = 0
    for item in manifest['preserved_files']:
        data = (EVIDENCE/item['path']).read_bytes()
        demand(sha(data) == item['sha256'] and len(data) == item['bytes'], 'stored bytes '+item['path'])
        restored = gzip.decompress(data) if item.get('encoding') == 'gzip' else data
        if item.get('encoding') == 'gzip':
            compressed += 1
            demand(sha(restored) == item['restored_sha256'] and len(restored) == item['restored_bytes'], 'restored binding')
        demand(sha(restored) == item['original_sha256'] and Path(item['original_path']).read_bytes() == restored,
               'fixed raw original byte equality '+item['path'])
        stored_bytes += len(data)
        restored_bytes += len(restored)
    demand(manifest['compiled_artifact_bytes_distributed'] is False
           and manifest['original_attempts_overwritten'] is False
           and manifest['protected_provider_context_executed'] is False, 'preservation scope')
    final = read(EVIDENCE/'FINAL-RECEIPT.json')
    demand(final == manifest['final_receipt'] and final['status'] == 'PASS_ALL_REQUESTED_TARGETS'
           and final['targets_requested'] == final['targets_passed'] == [TARGET], 'actual final target PASS')
    demand(final['counts'] == {'cache_reuse':116,'fresh_components':1}
           and final['trust_level'] == 0 and final['kernel_checking'] is True
           and final['compiler_identity_stable'] is True and final['native_runtime_final_rehash_stable'] is True,
           'actual trust/kernel/freshness')
    certificate_path = PACKET/'lean/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-CERTIFICATE.json'
    demand(sha(certificate_path.read_bytes()) == CERTIFICATE, 'certificate identity')
    certificate = read(certificate_path)
    demand(certificate['preservation_manifest_sha256'] == MANIFEST
           and certificate['full_1504_owned_metadata_retention_claimed'] is False
           and certificate['coherent_union1506_executed'] is False, 'narrow certificate scope')
    graph_raw = raw(EVIDENCE/'DEPENDENCY-GRAPH.json.gz')
    graph = json.loads(graph_raw)
    demand(sha(graph_raw) == final['graph_sha256'] == certificate['graph_sha256'], 'graph pin')
    selected = graph['targets'][TARGET]
    guards = graph['targets']['context/protected-mathlib-providers']
    demand(len(selected['modules']) == len(selected['order']) == 117 and selected['roots'] == [MODULE], '117 executed modules')
    demand(len(guards['modules']) == 4 and guards['status'] == 'PROTECTED_NAMESPACE_CONTEXT_ONLY_NOT_EXECUTED'
           and guards['required_for_accepted_release'] is False, 'four staging guards not executed')
    parent = read(PACKET/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json')
    closure = read(EVIDENCE/'preparation/SOURCE-CLOSURE.json.gz')
    demand(len(closure) == 121, '121 staging sources')
    for item in closure:
        demand(sha(Path(item['scratch_source']).read_bytes()) == item['sha256']
               == sha(Path(item['preserved_source']).read_bytes()), 'source bytes '+item['module'])
        demand(imports(Path(item['preserved_source']).read_text()) == item['imports'], 'literal imports '+item['module'])
        record = (selected['modules'] if item['module'] in selected['modules'] else guards['modules'])[item['module']]
        demand(record['sha256'] == item['sha256'] and record['imports'] == item['imports'], 'source/graph agreement')
        if item['module'] != MODULE:
            demand(parent['source_pins'][item['module']] == item['sha256'], 'accepted exact parent/guard source')
    freeze = read(PACKET/'lean/proposals/reuse-integration-20261010T2138Z/parallel-arm-transport/PROPOSAL-FREEZE.json')
    repo = PACKET.parents[1]
    demand(sha((repo/freeze['source']['path']).read_bytes()) == SOURCE
           == sha((repo/freeze['source']['immutable_version']).read_bytes())
           == sha((EVIDENCE/'sources'/f'{MODULE}.lean').read_bytes()), 'same frozen full source')
    static_path = PACKET/'design/history/g6-parallel-arm-static-qc-20261010T2322Z-solver_design_recovery/G6-PARALLEL-ARM-STATIC-QC-ATTEMPT1.json'
    demand(sha(static_path.read_bytes()) == '6ddf8390f415959662aab867e26a5593b9fa39f8f5d7e08fca0a7dcfad03cb62', 'prior independent static QC')

    result = read(TARGET_DIR/'RESULT.json.gz')
    demand((result['status'],result['roots'],result['closure_modules'],result['declarations'],result['theorems'])
           == ('PASS',1,117,3063,1976), 'result counts')
    components = result['component_receipts']
    demand(len(components) == 117 and {r['module'] for r in components} == set(selected['modules']), 'all component receipts')
    fresh = [r for r in components if r['receipt_directory'].startswith(final['run']+'/')]
    demand(len(fresh) == 1 and fresh[0]['module'] == MODULE and fresh[0]['source_sha256'] == SOURCE, 'one fresh module')
    for item in components + [result['aggregate_receipt'],result['audit_receipt']]:
        demand(item['exit_code'] == 0 and item['source_and_imports_stable'] is True
               and item['compiler_sha256'] == final['compiler_sha256']
               and item['native_runtime_digest'] == final['native_runtime_digest']
               and '-Ddebug.skipKernelTC=false' in item['command'], 'component/aggregate/audit kernel command binding')
    demand(all(result[k]['receipt_directory'].startswith(final['run']+'/')
               for k in ['aggregate_receipt','audit_receipt']), 'fresh aggregate and complete owned audit')
    root_saved = read(EVIDENCE/f'attempts/00001-{MODULE}/receipt.json')
    demand(set(fresh[0])-set(root_saved) == {'cached_object'}
           and {k:v for k,v in fresh[0].items() if k!='cached_object'} == root_saved,
           'raw fresh root receipt plus exact one cached_object annotation')

    compiled = {}
    def bind(path, digest):
        path = str(path)
        if path in compiled:
            demand(compiled[path] == digest, 'consistent repeated compiled pin')
            return
        h = hashlib.sha256()
        with Path(path).open('rb') as handle:
            while block := handle.read(1024*1024):
                h.update(block)
        demand(h.hexdigest() == digest, 'compiled/artifact binding '+path)
        compiled[path] = digest
    def bundle(path, artifacts):
        path = str(path)
        demand(path.endswith('.olean'), 'compiled object base suffix')
        for suffix, digest in artifacts.items():
            bind(path[:-len('.olean')]+suffix,digest)
    for receipt in components:
        demand(receipt['source_sha256'] == selected['modules'][receipt['module']]['sha256'], 'receipt source identity')
        bundle(receipt['cached_object'],receipt['object_artifacts'])
        for binding in receipt['direct_import_bindings'].values():
            demand(binding['sha256'] == binding['artifacts']['.olean'], 'direct object/bundle pin')
            bundle(binding['path'],binding['artifacts'])
    post_path = EVIDENCE/'post-run/POST-RUN-TRANSPORT-REHASH-20261010T232230.265801Z.json.gz'
    post = read(post_path)
    demand(post['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
           and post['selected_modules_verified'] == post['installed_same_filesystem_hardlinks'] == 117
           and post['original_staged_cache_files_rehashed'] == 252
           and post['compiler_or_evaluator_invoked'] is False and post['accepted_inputs_modified'] is False,
           'post-transport scope')
    demand(post['final_receipt_sha256'] == sha((EVIDENCE/'FINAL-RECEIPT.json').read_bytes()), 'post/final binding')
    for item in post['records']:
        demand(item['source_sha256'] == selected['modules'][item['module']]['sha256'], 'post record source binding')
        bind(item['original_receipt'],item['original_receipt_sha256'])
        for key in ['original_object','staged_object','installed_object']:
            bundle(item[key],item['object_artifacts'])
        source_stat = Path(item['staged_object']).stat()
        installed_stat = Path(item['installed_object']).stat()
        demand((source_stat.st_dev,source_stat.st_ino) == (installed_stat.st_dev,installed_stat.st_ino), 'installed hardlink')
    transport = read(EVIDENCE/'preparation/CACHE-TRANSPORT-PRE-USE-PLAN.json.gz')
    demand(len(transport['entries']) == 120 and transport['compiler_launched'] is False,
           '120 existing pre-use aliases include separate protected guards')
    transport_count = 0
    for item in transport['entries']:
        demand(parent['source_pins'][item['module']] == item['source_sha256'], 'pre-use alias accepted source')
        for artifact in item['files']:
            bind(artifact['source'],artifact['sha256'])
            bind(artifact['destination'],artifact['sha256'])
            demand(Path(artifact['source']).stat().st_size == artifact['bytes'], 'transport byte count')
            a,b = Path(artifact['source']).stat(),Path(artifact['destination']).stat()
            demand((a.st_dev,a.st_ino) == (b.st_dev,b.st_ino), 'source/destination hardlink')
            transport_count += 1
    demand(transport_count == 252, '252 staged cache artifact/receipt files')
    actual_artifacts = read(TARGET_DIR/'ACTUAL-IMPORTED-ARTIFACTS.json.gz')
    own_artifacts = [a for a in actual_artifacts if a['module'] in selected['modules']]
    demand({a['module'] for a in own_artifacts} == set(selected['modules']), 'actual imported full own closure')
    for item in own_artifacts:
        bind(item['path'],item['sha256'])
        demand(Path(item['path']).stat().st_size == item['bytes'], 'actual imported own artifact size')

    audit_path = EVIDENCE/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json.gz'
    audit_raw = raw(audit_path)
    audit = json.loads(audit_raw)
    demand(audit['selected_modules'] == selected['order'] and audit['owned_axioms'] == []
           and audit['nonstandard_axiom_rows'] == [] and audit['missing_modules'] == [], 'owned audit gates')
    demand(audit['declaration_count'] == len(audit['declarations']) == 3063
           and audit['theorem_declaration_count'] == 1976, 'owned audit counts')
    demand(sha(audit_raw) == certificate['targets'][TARGET]['audit_raw_sha256'], 'certificate raw audit binding')
    demand(all(set(d['axioms']) <= FOUNDATIONS for d in audit['declarations']), 'standard foundations only')
    new = {d['name']:d for d in audit['declarations']}
    demand(len(new) == 3063, 'no duplicate declaration names')
    owned = [d for d in audit['declarations'] if d['module'] == MODULE]
    demand(len(owned) == 24 and sum(d['kind']=='theorem' for d in owned) == 20, '24 owned names/20 theorems')
    namespace = 'GProgram.G6.OriginalParallelArmTransport.'
    private = '_private.G6OriginalParallelArmTransport.0.'
    source_owned_names = {((private if d['header'].startswith('private ') else '')+namespace+
                          re.search(r'(?:def|theorem)\s+(\w+)',d['header']).group(1))
                         for d in freeze['source']['declarations']}
    generated = {
        namespace+'edgeSwap.eq_1', private+namespace+'castCode._proof_1',
        'GProgram.G7.SourceStateRelabelling.location.eq_1',
        private+'GProgram.G7.SourceStateRelabelling.location.match_1.eq_1',
        private+'GProgram.G7.SourceStateRelabelling.location.match_1.eq_2',
        private+'GProgram.G7.SourceStateRelabelling.location.match_1.eq_3',
        private+'GProgram.G7.SourceStateRelabelling.location.match_1.splitter',
    }
    demand(len(source_owned_names) == 17 and {d['name'] for d in owned} == source_owned_names | generated,
           'exact17 source heads plus exact7 generated helpers')
    final_head = new[namespace+'actual_parallel_arm_full_forest_transport']
    demand('G1ContextualForestReplacement.rootForest' in final_head['type_references']
           and 'GProgram.SourceForest.State.register' in final_head['type_references']
           and 'UnifiedLean.Source.SourcePoissonKernel.sourceTimeKernel' in final_head['type_references']
           and namespace+'armCode_time_kernel' in final_head['body_references'], 'actual final typed observable and proof dependency')
    demand('GProgram.G7.ProgramRelabelling.time_kernel' in new[namespace+'armCode_time_kernel']['body_references'],
           'actual accepted time-kernel provider used')
    parent_target = parent['targets']['current/connected']
    parent_audit_raw = raw(PACKET/'lean'/parent['evidence']/parent_target['audit_distribution'])
    demand(sha(parent_audit_raw) == parent_target['audit_raw_sha256'], 'accepted parent audit binding')
    old = {d['name']:d for d in json.loads(parent_audit_raw)['declarations']}
    demand(all(d['name'] not in old for d in owned), '24 owned names absent parent')
    inherited = [d for d in audit['declarations'] if d['module'] != MODULE]
    demand(len(inherited) == 3039 and all(d['name'] in old for d in inherited), 'all3039 inherited names')
    differences = []
    for declaration in inherited:
        before = old[declaration['name']]
        demand(set(before) == set(declaration), 'same audit metadata field set')
        changed = {k:[before[k],declaration[k]] for k in before if before[k] != declaration[k]}
        if changed:
            differences.append({'name':declaration['name'],'differences':changed})
    delta_preflight_path = PACKET/'quality/G6-PARALLEL-117-CONTEXT-DELTA-PREFLIGHT-20261010T2325Z.json'
    delta_preflight = read(delta_preflight_path)
    demand(len(differences) == 11 and differences == delta_preflight['inherited_differences'], 'exact independently reproduced11 record differences')
    owner_rows = []
    for item in differences:
        changed = item['differences']
        if item['name'] == ALIAS_ROW:
            demand(set(changed) == {'body_references'}, 'only private alias body-reference field')
            before,after = changed['body_references']
            changed_positions = [i for i,(a,b) in enumerate(zip(before,after)) if a != b]
            demand(len(before) == len(after) and len(changed_positions) == 1
                   and before[changed_positions[0]] == OLD_ALIAS and after[changed_positions[0]] == NEW_ALIAS,
                   'exact one old/new private splitter reference')
        else:
            demand(set(changed) == {'module'} and re.search(r'(?:\.eq_[0-9]+|\.congr_simp)$',item['name']),
                   'only exact generated owner-module attribution')
            owner_rows.append(item)
    demand(len(owner_rows) == 10, '10 owner labels plus one alias')
    demand({k:v for k,v in old[OLD_ALIAS].items() if k not in {'name','module'}}
           == {k:v for k,v in old[NEW_ALIAS].items() if k not in {'name','module'}}, 'both parent aliases identical remaining audit fields')
    demand(all(d['type_references'] == old[d['name']]['type_references']
               and d['axioms'] == old[d['name']]['axioms'] and d['kind'] == old[d['name']]['kind']
               for d in inherited), 'all inherited type-reference/axiom/kind metadata unchanged')
    guard_dir = next((EVIDENCE/'resource-guard').iterdir())
    guard = read(guard_dir/'RECEIPT.json')
    plan = read(EVIDENCE/'preparation/RESOURCE-AND-RUN-PLAN.json')
    demand(guard['status'] == 'PASS_UNCHANGED_BUILDER_EXIT_ZERO' and guard['exit_code'] == 0
           and guard['abort_reason'] is None and guard['monitor_error'] is None
           and guard['resource_caps_kernel_flags_core_or_audit_changed'] is False, 'actual unchanged resource guard PASS')
    demand(guard['peak_distinct_inode_allocation_bytes'] < plan['scratch_abort_bytes'] < plan['scratch_hard_limit_bytes']
           and guard['peak_nonreclaimable_estimate_bytes'] < plan['memory_abort_bytes'], 'actual scratch/memory guard measurements')
    for stream in ['stdout','stderr']:
        demand(sha((guard_dir/(stream+'.txt')).read_bytes()) == guard[stream+'_sha256'], 'guard stream identity')
    return {
        'status':'PASS_INDEPENDENT_SAVED_G6_PARALLEL_ARM_DESIGN_QC',
        'source_sha256':SOURCE,'manifest_sha256':MANIFEST,'certificate_sha256':CERTIFICATE,
        'prior_static_qc_sha256':sha(static_path.read_bytes()),
        'preserved_files':60,'stored_bytes':stored_bytes,'restored_bytes':restored_bytes,'gzip_restorations':compressed,
        'all_preserved_and_fixed_original_bytes_equal':True,
        'executed_modules':117,'staging_modules':121,'protected_guard_modules_not_executed':4,
        'authenticated_reuse':116,'fresh_components':1,'fresh_aggregate_and_owned_audit':True,
        'trust_level':0,'owned_axioms':0,'nonstandard_axiom_rows':0,'missing_modules':0,
        'owned_declarations':3063,'owned_theorems':1976,
        'root_owned_names':24,'root_owned_theorems':20,'authored_source_heads':17,
        'authored_public_heads':12,'authored_private_helpers':5,'generated_names':sorted(generated),
        'all_root_owned_rows':owned,
        'inherited_rows':3039,'strictly_identical_inherited_records':3028,
        'exact_qualified_inherited_differences':differences,
        'both_parent_private_splitters_equal_except_name_and_module':True,
        'all_inherited_type_reference_axiom_kind_metadata_identical':True,
        'context_delta_preflight_sha256':sha(delta_preflight_path.read_bytes()),
        'original_staged_cache_files_independently_checked':transport_count,
        'compiled_receipt_object_and_import_paths_independently_rehashed':len(compiled),
        'scheduler_post_transport_reported_unique_paths':post['unique_object_and_import_bundle_paths_rehashed'],
        'actual_imported_own_module_artifacts_checked':len(own_artifacts),
        'actual_imported_library_manifest_entries_authenticated_as_preserved_bytes_only':len(actual_artifacts)-len(own_artifacts),
        'compiled_binding_map_sha256':sha(json.dumps(compiled,sort_keys=True,separators=(',',':')).encode()),
        'post_transport_raw_sha256':sha(raw(post_path)),
        'resource_guard_sha256':sha((guard_dir/'RECEIPT.json').read_bytes()),
        'kernel_compiler_sha256':final['compiler_sha256'],'observed_native_runtime_digest':final['native_runtime_digest'],
        'actual_raw_audit_sha256':sha(audit_raw),'accepted_parent_raw_audit_sha256':sha(parent_audit_raw),
        'scope':'Actual original parallel E-occurrence automorphism with V/Copy fixed. All-live-at-original-hybrid admitted entering Code, arbitrary carried genealogy, positive original rate bank and nonnegative epoch duration. Compare pulse b/r with pulse !b/edge-swapped r after explicit full original-register and rooted labelled unranked forest readout.',
        'remaining_g6_obligations':freeze['remaining_factorization_interface'],
        'qualifications':[
            'The final observed forest is rootForest: a finite rooted labelled unranked live-tree forest. This receipt does not promote it to an ordered raw-Code dictionary or a timed observation.',
            'A fixed Code already contains a stored bit. Natural private-seed marginalization, NoPrivateWordRead prefix and any required no-read future erasure are additional source operations.',
            'The epoch identity alone supplies no completed bigon-exit/calendar factorization, global joint positive-source normalization, protected bins or G6 master closure.',
            'Audit metadata are constant-reference/kind/axiom lists, not serialized full type or proof expressions. Only the exact ten owner labels and one qualified private alias field are excepted.',
            'Kernel execution is the authenticated saved sole-scheduler run. This reviewer rehashes bytes and checks metadata; it launches no theorem, helper, native or evaluator producer.',
            'Counts describe separate117 scope; accepted1504 is not widened and no blanket parent ownership metadata retention is claimed.',
        ],
    }

def main():
    destination = Path(sys.argv[1])
    report = {'schema':'g6_parallel_arm_saved_design_qc_v1','contributor':'Codex / solver_design_recovery',
              'observed_utc':datetime.now(timezone.utc).isoformat(),
              'reviewer_sha256':sha(Path(__file__).read_bytes()),
              'compiler_helper_evaluator_adapter_native_processes_started_by_reviewer':0,
              'accepted_union_modified':False}
    try:
        report.update(check())
    except Exception as error:
        report.update(status='FAIL_SAVED_REVIEW',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,sort_keys=True,indent=2,ensure_ascii=False)
        handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':sha(destination.read_bytes())}))
    return 1 if report['status'] == 'FAIL_SAVED_REVIEW' else 0

if __name__ == '__main__':
    raise SystemExit(main())
