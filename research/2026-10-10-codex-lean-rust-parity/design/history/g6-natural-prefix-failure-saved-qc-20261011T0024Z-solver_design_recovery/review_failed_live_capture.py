#!/usr/bin/env python3
"""Independently reads saved failure bytes and ASTs; no target execution."""
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T001250.195773Z')
R = W/'.build/runs/20261011T001624.474830Z'
A = R/'attempts/00001-G6OriginalCommonPrefix'
F = P/'lean/evidence/proof-extensions/g6-natural-common-factorization/rc-lean-g6-natural-common-20261011T001250.195773Z/prefix-68e-failed-20261011T001624.474830Z'


def demand(condition, reason):
    if not condition: raise AssertionError(reason)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path, expected=None):
    path = Path(path); h = hashlib.sha256(); size = 0
    with path.open('rb') as f:
        for block in iter(lambda:f.read(65536),b''):
            size += len(block); h.update(block)
    sha = h.hexdigest()
    demand(expected is None or sha == expected, 'pin '+str(path))
    return {'path':str(path),'sha256':sha,'bytes':size}


def load(path): return json.loads(Path(path).read_bytes())


def compare_decoded(encoded, original, expected_sha, expected_bytes):
    h = hashlib.sha256(); count = 0
    with gzip.open(encoded,'rb') as z, Path(original).open('rb') as raw:
        while True:
            block = z.read(65536)
            if not block:
                demand(raw.read(1)==b'', 'original has no extra bytes'); break
            demand(block == raw.read(len(block)), 'every restored byte matches original')
            h.update(block); count += len(block)
    demand(count == expected_bytes and h.hexdigest() == expected_sha, 'decoded byte/hash/EOF identity')
    return {'decoded_bytes':count,'decoded_sha256':h.hexdigest(),'all_original_bytes_compared':True,'gzip_complete_EOF':True}


def c3(node, bases):
    parents = bases[node]
    if not parents: return [node]
    seqs = [c3(b,bases)[:] for b in parents] + [parents[:]]
    out = [node]
    while any(seqs):
        seqs = [s for s in seqs if s]
        candidate = next((s[0] for s in seqs if all(s[0] not in t[1:] for t in seqs)), None)
        demand(candidate is not None, 'valid static C3')
        out.append(candidate)
        for seq in seqs:
            if seq and seq[0] == candidate: seq.pop(0)
    return out


def check():
    refs = [pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/NATURAL141-PREPARATION-SAVED-QC-ATTEMPT1.json',
                '45daff8bd336ba450d28b33334d870b0e5c5baa1412bcbc8e64b58fb2c27eb31'),
            pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/COMPRESSED-LOADER-V3-STATIC-QC-ATTEMPT1.json',
                '9fde1c98aea1389b90551f6df8dc1b75a3fc25defb863c4194a609a0f6c8ea18'),
            pin(P/'design/history/storage-saved-qc-20261011T0009Z-solver_design_recovery/COMPRESSED-LOADER-V3-SAVED-QC-ATTEMPT1.json',
                'f0c5402861b73536105ac64d278fbb1198a488e072e85911b9214cfe62f160ba')]
    manifest_pin = pin(F/'PRESERVATION-MANIFEST.json','39f11359152d655ba1568572593a67c09f51b7a252353fe273bdf9eced84dbfe')
    manifest = load(manifest_pin['path']); stage = Path(manifest['complete_lossless_export_original'])
    demand(manifest['workspace'] == str(W) and manifest['actual_run'] == str(R), 'exact failed context/run')
    demand(manifest['status'] == 'INCOMPLETE_TARGET_FAILURES_PRESERVED' and manifest['packet_distribution_complete'], 'explicit failed complete export')
    demand(not manifest['compiled_artifact_bytes_distributed'] and not manifest['original_attempts_overwritten'], 'no ELF/object distribution or overwrite')
    rows = manifest['preserved_files']
    demand(len(rows) == len({r['path'] for r in rows}) == 50, '50 unique saved evidence rows')
    checked = []; compressed = []
    for row in rows:
        rel = Path(row['path']); demand(not rel.is_absolute() and '..' not in rel.parts, 'relative export path')
        exported = F/rel; staged = stage/rel; original = Path(row['original_path'])
        a = pin(exported,row['sha256']); b = pin(staged,row['sha256']); c = pin(original,row['original_sha256'])
        demand(a['bytes'] == b['bytes'] == row['bytes'], 'encoded/copy length')
        demand(exported.read_bytes() == staged.read_bytes(), 'complete fixed-stage/portable byte equality')
        item = {'row':row,'portable':a,'fixed_stage':b,'original':c}
        if row.get('encoding') == 'gzip':
            demand(row['restored_sha256'] == row['original_sha256'] and row['restored_bytes'] == c['bytes'], 'declared restored identity')
            item['restoration_comparison'] = compare_decoded(exported,original,row['restored_sha256'],row['restored_bytes'])
            compressed.append(row)
        else:
            demand(row.get('encoding') is None and exported.read_bytes() == original.read_bytes(), 'every normal row exact original bytes')
        demand(exported.open('rb').read(4) != b'\x7fELF', 'no exported ELF')
        checked.append(item)
    distribution_pin = pin(F/'COMPRESSED-DISTRIBUTIONS.json',manifest['compressed_distributions_manifest_sha256'])
    demand(pin(stage/'COMPRESSED-DISTRIBUTIONS.json',distribution_pin['sha256'])['bytes'] == distribution_pin['bytes'], 'distribution manifest stage pair')
    distribution = load(distribution_pin['path'])
    demand(distribution['status']=='PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION' and distribution['original_run_unchanged'], 'lossless original retention')
    demand(distribution['distributions'] == compressed, 'exact all gzip-restoration rows')
    demand(sum(r['bytes'] for r in rows)+distribution_pin['bytes'] == manifest['measured_export_bytes_before_manifest'] == 799831, 'exact50 rows plus distribution bytes')
    demand(pin(stage/'PRESERVATION-MANIFEST.json',manifest_pin['sha256'])['bytes'] == manifest_pin['bytes'], 'same complete stage manifest')
    expected_names = {r['path'] for r in rows}|{'PRESERVATION-MANIFEST.json','COMPRESSED-DISTRIBUTIONS.json'}
    demand({str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()} == expected_names, 'complete exported file inventory')
    attempt_pin = pin(A/'receipt.json','2883964dd5a127ed015f8b31b4d5998cbc3198f2e6fb422150ad9cfea9b8c81a')
    receipt = load(attempt_pin['path']); capture = load(A/'STDERR-CAPTURE.json')
    descriptor_pin = pin(A/'STDERR-CAPTURE.json','3fb2bf2540fcb116716dedaccc457467d6908e902cea2cc5ce4ae147aaa1aacc')
    encoded_pin = pin(A/'stderr.raw.gz','5286463283f785aa962082014bff8aa7116145ca3d7c0b551fa66adf11631e6e')
    demand(receipt['stderr_storage'] == capture, 'capture descriptor exactly bound by failed receipt')
    demand(capture['eof'] and capture['complete'] and not capture['truncated'] and capture['reason'] is None, 'complete nontruncated actual stream')
    demand(capture['gzip_path'] == encoded_pin['path'] and capture['gzip_bytes'] == encoded_pin['bytes'] == 290507 and capture['gzip_sha256'] == encoded_pin['sha256'], 'encoded capture identity')
    h = hashlib.sha256(); n = 0; raw_parts = []
    with gzip.open(A/'stderr.raw.gz','rb') as z:
        while True:
            block=z.read(65536)
            if not block: break
            h.update(block); n += len(block); raw_parts.append(block)
    demand(n == capture['raw_bytes'] == 12579325 and h.hexdigest() == capture['raw_sha256'] == receipt['stderr_sha256'], 'full decoded live byte/EOF identity')
    raw = b''.join(raw_parts); names = re.findall(rb'calling init:\s*(\S+)',raw)
    resolved = {str(Path(x.decode()).resolve()) for x in names}
    demand(len(names) == len(resolved) == 10 and resolved == set(receipt['native_initialized_libraries']), 'all10 actual initialized library names')
    loader = receipt['native_loader_outputs']; demand(len(loader)==1, 'one complete combined capture')
    demand(loader[0]['path']==str(A/'stderr.raw.gz') and loader[0]['sha256']==encoded_pin['sha256'] and loader[0]['raw_sha256']==h.hexdigest() and loader[0]['raw_bytes']==n, 'live native evidence raw and encoded bindings')
    runtime = load(R/'NATIVE-RUNTIME-PINS.json'); final_rehash=load(R/'NATIVE-RUNTIME-FINAL-REHASH.json')
    demand(runtime['native_runtime_digest'] == receipt['native_runtime_digest'], 'same native digest')
    demand(final_rehash['stable'] and final_rehash['hashes'] == {k:v['sha256'] for k,v in runtime['libraries'].items()}, 'initial/final all-library identity equality')
    current_libs = []
    for path, identity in runtime['libraries'].items():
        item = pin(path,identity['sha256']); demand(item['bytes'] == identity['bytes'], 'current native byte size')
        current_libs.append(item)
    demand(all(receipt['native_initialized_libraries'][k] == runtime['libraries'][k] for k in resolved), 'all10 initialized full bound identities')
    stdout_pin = pin(A/'stdout','d7e88708ec6e041d7a556cd5fb55c51902af19e328aec89bdf763650d5851a8a')
    stdout = (A/'stdout').read_text()
    errors = [(int(a),int(b)) for a,b in re.findall(r'^G6OriginalCommonPrefix\.lean:(\d+):(\d+): error:',stdout,re.M)]
    demand(errors == [(59,20),(83,17),(139,22),(140,36),(148,16),(149,30)], 'exact six preserved errors')
    axiom_records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",stdout,re.S)
    demand(len(axiom_records)==3 and all('sorryAx' in axes for _,axes in axiom_records), 'all3 sorryAx diagnostics refused')
    demand(receipt['status']=='FAILED_OR_RESOURCE' and receipt['exit_code']==capture['exit_code']==1, 'compiler/capture failed exit1')
    demand(receipt['source_and_imports_stable'] and receipt['native_runtime_stat_stable'] and receipt['native_initialized_libraries_bound'], 'stable source/import/native boundaries')
    demand(receipt['cap_seconds']==180 and receipt['cap_memory_mib']==4096 and all(x in receipt['command'] for x in ['-j1','-t0','-M4096','-Ddebug.skipKernelTC=false']), 'unchanged strict narrow cap/flags')
    source_pin = pin(A/'work/G6OriginalCommonPrefix.lean','68e0130ba41f55a7d87d0d8847dff504d53e55fe947020214e57ba42702b010b')
    demand(receipt['source_sha256']==source_pin['sha256'], 'failed source exact immutable68e')
    imports_checked = []
    for name,binding in receipt['direct_import_bindings'].items():
        item=pin(binding['path'],binding['sha256']); demand(binding['artifacts']=={'.olean':item['sha256']},'original imported artifact bundle')
        demand(receipt['direct_import_sha256'][name]==item['sha256'], 'import receipt agreement'); imports_checked.append({'module':name,**item})
    final=load(R/'FINAL-RECEIPT.json'); demand(final == manifest['final_receipt'], 'embedded exact final failure receipt')
    demand(final['status']=='INCOMPLETE_TARGET_FAILURES_PRESERVED' and not final['targets_passed'] and final['counts']=={'cache_reuse':126}, 'no successful new target or component')
    demand(final['trust_level']==0 and final['kernel_checking'] and final['native_runtime_final_rehash_stable'] and final['compiler_identity_stable'], 'strict rejected-run provenance')
    demand({p.name for p in (R/'attempts').iterdir()} == {'00001-G6OriginalCommonPrefix'}, 'exactly1 actual new failed attempt; no fcad/aggregate/audit invocation')
    target=load(R/'targets/extraction_g6-natural-common-forest-factorization-fcadb6c4/RESULT.json')
    demand(target['status']=='FAILED_OR_BLOCKED' and target['error']=='Component failed G6OriginalCommonPrefix' and len(target['component_receipts'])==126, '126 inherited admissions then prefix failure')
    demand(all(x['module'] not in ['G6OriginalCommonPrefix','G6NaturalCommonForestFactorization'] and not x['receipt_directory'].startswith(str(R)) for x in target['component_receipts']), 'successful entries belong to prior contexts')
    prelaunch = load(W/'guard-runs/natural-20261011T001623.782686Z/PRE-PHASE-INPUT-PINS.json')
    prelaunch_pins=[pin(v['path'],v['sha256']) for v in prelaunch.values()]
    equivalence = load(W/'PARENT-WRAPPER-EQUIVALENCE.json'); parent_equivalence_pins=[]
    for role in ['namespace','authenticated']:
        before=equivalence['accepted_'+role]; after=equivalence['actual_'+role]; replacement=equivalence[role+'_exact_replacement']
        parent_equivalence_pins += [pin(before['path'],before['sha256']),pin(after['path'],after['sha256'])]
        a=Path(before['path']).read_text(); b=Path(after['path']).read_text()
        demand(a.count(replacement['old'])==replacement['occurrences']==1 and a.replace(replacement['old'],replacement['new'],1)==b, 'full parent source equality except exact one pin literal')
    scripts = W/'scripts'; trees={name:ast.parse((scripts/name).read_text()) for name in ['storage_wrapper.py','build_with_authenticated_overlay.py','build_with_mathlib_overlay.py']}
    cls = {f:{c.name:c for c in ast.walk(t) if isinstance(c,ast.ClassDef)} for f,t in trees.items()}
    demand([ast.unparse(x) for x in cls['storage_wrapper.py']['StorageBuilder'].bases]==['parent','StorageInvocation'] and
           [ast.unparse(x) for x in cls['storage_wrapper.py']['StorageInvocation'].bases]==['core.Builder'], 'actual frozen storage class bases')
    demand([ast.unparse(x) for x in cls['build_with_authenticated_overlay.py']['OverlayBuilder'].bases]==['original.OverlayBuilder'] and
           [ast.unparse(x) for x in cls['build_with_mathlib_overlay.py']['OverlayBuilder'].bases]==['core.Builder'], 'actual parent class bases')
    mro=c3('StorageBuilder',{'StorageBuilder':['Auth','StorageInvocation'],'Auth':['Namespace'],'Namespace':['Core'],'StorageInvocation':['Core'],'Core':['object'],'object':[]})
    demand(mro==['StorageBuilder','Auth','Namespace','StorageInvocation','Core','object'], 'static same-core C3 retains parent invoke')
    facade=(P/'lean/scripts/run_proof_extensions_with_storage_20261011.py').read_text()
    demand('builder_module.OverlayBuilder, builder_module.original.core, policy' in facade, 'authenticated original exact core passed')
    storage_pins=load(R/'COMPRESSED-STDERR-STORAGE-PINS.json')
    demand(storage_pins['same_core_module_object'] and storage_pins['adapter_sha256']==receipt['storage_wrapper_sha256'] and
           storage_pins['authenticated_parent_sha256']==equivalence['actual_authenticated']['sha256'] and
           storage_pins['namespace_parent_sha256']==equivalence['actual_namespace']['sha256'], 'actual recorded composition bound to source')
    guard=load(W/'guard-runs/natural-20261011T001623.782686Z/RECEIPT.json'); plan=load(W/'RESOURCE-AND-RUN-PLAN.json')
    demand(guard['exit_code']==1 and guard['abort_reason'] is None and guard['monitor_error'] is None and not guard['resource_caps_kernel_flags_core_or_audit_changed'], 'ordinary proof failure with no resource abort/policy change')
    demand(guard['peak_nonreclaimable_estimate_bytes']<plan['memory_abort_bytes'] and guard['peak_distinct_inode_allocation_bytes']<plan['scratch_abort_bytes'], 'saved resource peaks within explicit guards')
    demand(guard['config_sha256']==pin(W/'RESOURCE-AND-RUN-PLAN.json')['sha256'] and guard['monitor_sha256']==pin(W/'scripts/guard_natural_common_20261011.py')['sha256'], 'actual monitor/plan identity')
    compiler=pin(receipt['command'][0],receipt['compiler_sha256'])
    demand(compiler['sha256']==final['compiler_sha256']==final['compiler_final_sha256'], 'current compiler bytes retained without executing')
    return {'status':'PASS_SAVED_LIVE_CAPTURE_BYTES_NATIVE_COMPOSITION_AND_FAILURE_PRESERVATION_QC; LEAN_RESULT_FAIL',
        'prior_independent_qc':refs,'manifest':manifest_pin,'distribution_manifest':distribution_pin,'preserved_file_comparisons':checked,
        'file_counts':{'preserved_rows':50,'gzip_restoration_rows':len(compressed),'other_manifest_files':2,'row_bytes':sum(r['bytes'] for r in rows),'measured_payload_before_manifest_bytes':799831,'exported_ELFs':0},
        'live_capture':{'descriptor':descriptor_pin,'encoded':encoded_pin,'decoded_bytes':n,'decoded_sha256':h.hexdigest(),'full_gzip_EOF_verified':True,
                        'decoded_raw_file_exists':False,'raw_identity_qualification':'Independent full gzip decoding/hash/EOF verification; no separate uncompressed live file exists for direct original-byte comparison.',
                        'already_gzip_export_identical':True,'double_gzip_applied':False,'native_initialized_count':10,'native_initialized_resolved_paths':sorted(resolved)},
        'current_all_native_library_byte_pins':current_libs,'current_compiler_byte_pin':compiler,
        'failed_attempt':attempt_pin,'stdout':stdout_pin,'actual_error_locations':errors,'printed_axiom_records':[{'name':name,'axioms':axes.split(',')} for name,axes in axiom_records],
        'failed_source':source_pin,'actual_direct_import_byte_pins':imports_checked,'prelaunch_current_pins':prelaunch_pins,
        'actual_parent_source_equivalence':equivalence,'parent_byte_pins':parent_equivalence_pins,'independent_static_C3':mro,
        'outcome':{'compiler_exit_code':1,'new_failed_attempts':1,'prior_authenticated_cache_reuses':126,'successful_new_modules':0,'fcad_compiled':False,'fresh_aggregate_or_owned_audit':False,'target_accepted':False,
                   'manifest141_count_semantics':'Selected executable closure contains141 modules; it does not report141 completed modules.145 includes4 nonexecuted protected guard records.'},
        'resource_observation':{'peak_nonreclaimable_estimate_bytes':guard['peak_nonreclaimable_estimate_bytes'],'memory_abort_bytes':plan['memory_abort_bytes'],
                                'peak_distinct_inode_allocation_bytes':guard['peak_distinct_inode_allocation_bytes'],'scratch_abort_bytes':plan['scratch_abort_bytes'],'no_resource_abort':True},
        'qualification':['This is the first actual live compressed stderr capture, complete on a rejected Lean invocation. Storage evidence passes; the prefix proof and whole141 target fail.',
                         'The three diagnostic sorryAx occurrences are unsolved-goal artifacts and are refused; no component, aggregate or audit acceptance is inferred.',
                         'C3 is independently reconstructed from authenticated source AST and the same-core facade; no target module import, constructor, subprocess or compiler rerun was used.',
                         'All50 portable/original/fixed-stage identities and all gzip-restored original bytes were independently checked; live stderr encoded/raw identities are separately bound.',
                         'Accepted1504, separate168/117, old failures/versions, runtime/application/source-fit scope remain unchanged. No general live-failure recovery, future-union capacity or master closure claim.']}


def main():
    report={'schema':'g6_natural_failed_live_capture_independent_saved_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':digest(Path(__file__).read_bytes()),
            'target_modules_imported_or_producers_started':0,'mathematical_acceptance_promoted':False}
    try: report.update(check())
    except Exception as e: report.update(status='FAIL_SAVED_QC',error_type=type(e).__name__,error=str(e))
    out=Path(sys.argv[1])
    with out.open('x') as f: json.dump(report,f,indent=2,sort_keys=True,ensure_ascii=False); f.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(out),'sha256':digest(out.read_bytes())}))
    return 1 if report['status']=='FAIL_SAVED_QC' else 0


if __name__=='__main__': raise SystemExit(main())
