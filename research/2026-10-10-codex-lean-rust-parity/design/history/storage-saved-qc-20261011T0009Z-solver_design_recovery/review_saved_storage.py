#!/usr/bin/env python3
"""Saved-byte QC only. Never imports a codec/loader or repeats its trial."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import struct
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')

def require(value, text):
    if not value:
        raise AssertionError(text)

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as handle:
        while piece := handle.read(65536):
            h.update(piece)
    return h.hexdigest()

def pin(path, expected, size=None):
    path = Path(path)
    require(digest(path) == expected and (size is None or path.stat().st_size == size), 'pin '+str(path))
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':expected}

def read(path):
    return json.loads(Path(path).read_bytes())

def small_gzip(path, cap=1048576):
    with gzip.open(path,'rb') as handle:
        raw = handle.read(cap+1)
        require(len(raw) <= cap and handle.read(1) == b'', 'bounded complete saved gzip '+str(path))
    return raw

def wrapper():
    pub_path = P/'lean/evidence/storage-adapters/compressed-loader-v3-saved-trial-20261011T0005Z/PUBLICATION.json'
    pub_pin = pin(pub_path,'6badc69572b2cbb3bcc0edf09274edd1eeb03a22eb30aed0300ed9b91b60227f')
    pub = read(pub_path)
    require(len(pub['files']) == pub['file_count'] == 26 and sum(r['bytes'] for r in pub['files']) == pub['portable_raw_bytes'] == 658952,
            'exact26 portable files/bytes')
    copies = []
    for r in pub['files']:
        copies.extend([pin(r['original'],r['sha256'],r['bytes']),pin(r['portable'],r['sha256'],r['bytes'])])
        require(Path(r['original']).read_bytes() == Path(r['portable']).read_bytes(), 'lossless publication pair')
    trial = Path(pub['actual_receipt']['path']).parent
    actual_pin = pin(pub['actual_receipt']['path'],pub['actual_receipt']['sha256'])
    outer_pin = pin(pub['outer_receipt']['path'],pub['outer_receipt']['sha256'])
    actual,outer = read(actual_pin['path']),read(outer_pin['path'])
    static_pin = pin(P/'design/history/compressed-loader-static-qc-20261010T2356Z-solver_design_recovery/COMPRESSED-LOADER-V3-STATIC-QC-ATTEMPT1.json',
                     '9fde1c98aea1389b90551f6df8dc1b75a3fc25defb863c4194a609a0f6c8ea18')
    static = read(static_pin['path'])
    require(actual['status'] == 'PASS_ALL_SAVED_BYTE_CONTROLS' and actual['control_count'] == len(actual['controls']) == 15 and
            [r['control'] for r in actual['controls']] == static['expected_controls'], 'actual exact15 controls')
    require(outer['status'] == 'PASS_BOUNDED_BYTE_WORKER' and outer['exit_code'] == 0 and outer['reason'] is None and outer['error'] is None and
            outer['address_space_cap_bytes'] == 268435456 and outer['scratch_cap_bytes'] == 33554432 and outer['outer_seconds'] == 90 and
            outer['max_rss_kib'] == 49920 and outer['peak_distinct_inode_allocated_bytes'] == 720896 and
            outer['mathematical_or_native_calls'] == 0 and outer['byte_worker_calls'] == 1, 'one capped byte-only worker')
    approval_pin = pin(outer['approval_path'],outer['approval_sha256'])
    approval = read(approval_pin['path'])
    for path,expected in actual['inputs'].items():
        pin(path,expected)
    require(actual['script_sha256'] == 'f425ce06219db0245b6e5c936f501022552c74b6e584843749b06d300cc92de7' and
            not actual['runtime_capture_process_or_builder_exercised'] and actual['inert_cache_result_method_exercised'] and
            actual['inert_artifacts_are_not_kernel_evidence'] and actual['compiler_native_or_subprocess_calls'] == 0,
            'saved/inert execution boundary')
    positive = actual['positive_capture']
    raw_path,gz_path = Path(positive['source_path']),Path(positive['gzip_path'])
    pin(raw_path,positive['raw_sha256'],12561449); pin(gz_path,positive['gzip_sha256'],290421)
    h,count,chunks = hashlib.sha256(),0,[]
    with raw_path.open('rb') as original, gzip.open(gz_path,'rb') as encoded:
        while piece := encoded.read(65536):
            require(count+len(piece) <= 33554432 and original.read(len(piece)) == piece, 'existing raw/gzip complete direct bytes')
            h.update(piece); count += len(piece); chunks.append(piece)
        require(original.read(1) == b'', 'original raw EOF')
    require(count == positive['raw_bytes'] == 12561449 and h.hexdigest() == positive['raw_sha256'] and
            positive['complete'] and positive['eof'] and not positive['truncated'], 'complete existing capture identity')
    text = b''.join(chunks).decode('utf-8',errors='replace')
    native = sorted({str(Path(s).resolve()) for s in re.findall(r'calling init:\s*(/[^\s]+)',text)})
    original_receipt = read(raw_path.parent/'receipt.json')
    require(native == positive['native_used'] == sorted(original_receipt['native_initialized_libraries']) and len(native) == 10,
            'independent native identities equal actual original receipt')
    crossing = (trial/'cross-chunk-diagnostic.raw').read_bytes()
    require(crossing == b'x'*(65536-3)+b'sorryAx\n' and small_gzip(trial/'cross-chunk-diagnostic.gz') == crossing and
            crossing[65533:65540] == b'sorryAx', 'diagnostic spanning64KiB preserved')
    for name,expected in [('empty_native_evidence',b''),('diagnostic_without_native_init',b'Lean diagnostic only\n'),
                          ('unknown-native',b'calling init: /not/a/pinned/library.so\n')]:
        raw = (trial/(name+'.raw')).read_bytes()
        require(raw == expected and small_gzip(trial/(name+'.gz')) == raw, 'presence fixture saved bytes '+name)
        names = sorted({str(Path(s).resolve()) for s in re.findall(r'calling init:\s*(/[^\s]+)',raw.decode())})
        require(not (bool(names) and all(s in original_receipt['native_initialized_libraries'] for s in names)), 'independently refused native predicate '+name)
    require((trial/'missing-gzip-eof.gz').read_bytes() == gz_path.read_bytes()[:-8], 'exact absent8-byte gzip trailer control')
    controls = {r['control']:r for r in actual['controls']}
    require(controls['forged_raw_digest']['reason'] == controls['forged_raw_count']['reason'] == 'decoded stream byte identity mismatch' and
            controls['gzip_trailer_eof_required']['exception_type'] == 'EOFError' and
            controls['decoded_byte_limit']['reason'] == 'saved raw byte limit' and
            controls['encoded_byte_limit']['reason'] == 'gzip byte limit before physical write' and
            controls['refuse_destination_overwrite']['exception_type'] == 'FileExistsError' and
            controls['completed_new_cache_key_overwrite']['exception_type'] == 'RuntimeError', 'actual refusal reason bindings')
    partial_rows=[]
    for name in ('raw-limit','gzip-limit'):
        prefix = trial/(name+'.gz')
        sidecar = read(prefix.with_name(prefix.name+'.FAILED-PARTIAL.json'))
        require(sidecar['status'] == 'FAILED_PARTIAL_CAPTURE_NOT_VERIFIED' and not sidecar['complete'] and sidecar['truncated'] and
                not sidecar['eof'] and not sidecar['gzip_integrity_verified'] and 'raw_sha256' not in sidecar and
                sidecar['preserved_gzip_prefix_bytes'] == prefix.stat().st_size and sidecar['preserved_gzip_prefix_sha256'] == digest(prefix),
                'explicit unverified partial identities '+name)
        partial_rows.append({'name':name,'prefix_bytes':prefix.stat().st_size,'prefix_sha256':digest(prefix),'status':sidecar['status']})
    fresh = trial/'inert-run/attempts/inert/fixture.olean'
    cached = trial/('inert-cache/'+'a'*64+'/artifact.olean')
    require(fresh.read_bytes() == b'INERT BYTES: not a checked Lean object\n', 'fake object is explicitly inert')
    aliases=[]
    for suffix in ('.olean','.ilean'):
        a,b = fresh.with_suffix(suffix),cached.with_suffix(suffix)
        require(a.read_bytes() == b.read_bytes() and (a.stat().st_dev,a.stat().st_ino) == (b.stat().st_dev,b.stat().st_ino), 'physical same-inode inert alias '+suffix)
        aliases.append({'suffix':suffix,'same_inode':True,'bytes':a.stat().st_size,'sha256':digest(a)})
    require(aliases == controls['new_cache_aliases_are_single_copy']['detail']['aliases'] and
            not controls['new_cache_aliases_are_single_copy']['detail']['kernel_or_builder_constructor_called'], 'exact inert alias record')
    return {'status':'PASS_SAVED_15_BYTE_CONTROLS_AND_LOSSLESS_PUBLICATION_ONLY',
            'publication':pub_pin,'original_and_published_file_pins':copies,'actual_receipt':actual_pin,'outer_receipt':outer_pin,
            'root_approval':approval_pin,'independent_source_qc':static_pin,'actual_controls':actual['controls'],
            'independent_decoded_bytes_compared':count,'independent_raw_sha256':h.hexdigest(),'independent_native_identities':native,
            'partial_capture_checks':partial_rows,'physical_inert_alias_checks':aliases,
            'observed_resources':{'max_rss_kib':49920,'peak_distinct_inode_allocated_bytes':720896,'address_space_cap_bytes':268435456,
                                  'scratch_cap_bytes':33554432,'outer_timeout_seconds':90},
            'qualifications':['Saved byte/log/parser/sidecar and inert alias trial only; no live combined-stderr capture, new compiler, kernel, aggregate or owned-audit acceptance.',
                'Independent reader authenticated the already saved gzip against every original raw byte and EOF; no new capture or trial was executed.',
                'Fake .olean/.ilean bytes remain explicitly INERT_STORAGE_CONTROL_ONLY. Same inode establishes storage aliasing, not checked Lean evidence.',
                'V1/v2 predecessors and the original native log/receipt remain unchanged; prospective mathematical use requires separate plan/root approval.']}

def portable():
    folder=P/'rust/evidence/audit-portable-restore-family168-trial-1'
    pub_pin=pin(folder/'PUBLICATION.json','a42775ca1b982004426fda5a92c138065c916472f119f1a2ac649f74b23a8f4a',18276)
    pub=read(pub_pin['path']); copies=[]
    require(len(pub['copied_files']) == 23 and sum(r['published']['bytes'] for r in pub['copied_files']) == pub['copied_bytes'] == 234169 and
            pub['copied_elf_files'] == pub['new_large_raw_files_created'] == pub['raw_reference_files_required_by_restorer'] == 0, 'exact23 portable files and scope')
    for pair in pub['copied_files']:
        for r in pair.values():
            copies.append(pin(r['path'],r['sha256'],r['bytes']))
        require(Path(pair['original']['path']).read_bytes() == Path(pair['published']['path']).read_bytes(), 'lossless publication pair')
    references=[pin(r['path'],r['sha256'],r['bytes']) for r in pub['references']]
    for r in [*pub['required_compressed_inputs'].values(),*pub['driver_only_raw_comparison_references']]:
        pin(r['path'],r['sha256'],r['bytes'])
    actual_pin=pin(pub['trial_receipt']['path'],'20ba0bac43e165e5387fe96d11cfc143fab6af2b80f0355b44da027a2dba8a47',8563)
    actual=read(actual_pin['path']); trial=Path(actual['plan']['scratch_root'])
    require(actual['passed'] == actual['total'] == len(actual['tests']) == 9 and actual['status'] == 'PASS_FIXED_EXISTING_1504_TO_168_PORTABLE_RESTORE_ONLY', 'actual9 cases')
    scenario=read(P/'rust/evidence/audit-portable-restore-source-freeze-1/SCENARIO.json')
    require([r['name'] for r in actual['tests']] == scenario['expected_checks'] and actual['plan'] == scenario['plan'], 'exact nine-case scenario and plan')
    launch_path=Path('/dev/shm/rc-audit-portable-restore-family168-launch-1/RECEIPT.json')
    launch_pin=pin(launch_path,'746172955ca1f6d0d808e37a6285d507e9af199b60ca79d4afc7caa6ce805b56')
    launch=read(launch_path)
    require(launch['status'] == 'COMPLETED_PORTABLE_BYTE_DRIVER' and launch['return_code'] == 0 and not launch['timed_out'] and
            not launch['old_eight_case_trial_rerun'] and launch['address_space_cap_bytes'] == 268435456 and
            launch['trial_scratch_cap_bytes'] == 33554432 and launch['outer_timeout_seconds'] == 90 and
            launch['compiler_native_reference_processes'] == 0, 'one capped portable byte driver launch')
    for r in [*launch['pinned_inputs'],*launch['capture_files']]:
        pin(r['path'],r['sha256'],r['bytes'])
    require(actual['compiler_native_reference_processes'] == actual['new_large_raw_files_created'] == 0 and not actual['old_codec_producer_or_restore_called'] and
            not actual['future_union_created'] and not actual['mathematical_acceptance_claim'], 'no producer/new audit scope')
    standalone,optional=actual['tests'][0],actual['tests'][1]
    for row in (standalone,optional):
        result=row['result']
        require(result['base_raw_bytes_hashed'] == 114300292 and result['target_bytes_hashed'] == 6629112 and
                result['base_raw_sha256'] == actual['plan']['base_identity']['sha256'] and
                result['target_sha256'] == actual['plan']['target_identity']['sha256'] and result['base_gzip_decompression_passes'] == 1 and
                result['final_base_and_target_hashes_checked'] and result['required_raw_reference_files'] == 0 and result['output_file'] is None,
                'complete default/optional stream identities')
    require(not standalone['result']['optional_base_reference_checked'] and not standalone['result']['optional_target_reference_checked'] and
            standalone['raw_references_passed_to_restorer'] == 0 and standalone['independent_driver_compared_bytes'] == 6629112 and
            standalone['independent_driver_target_sha256'] == actual['plan']['target_identity']['sha256'] and
            optional['result']['optional_base_reference_checked'] and optional['result']['optional_target_reference_checked'], 'noncircular default and explicit optional refs separated')
    old_proof=pin(P/'design/history/audit-stream-codec-saved-qc-20261010T2353Z-solver_design_recovery/AUDIT-STREAM-CODEC-SAVED-QC-ATTEMPT1.json',
                  '1d9c1d40dfbf4aac342b1bff191788d0344188557905ca3e98f794e04d26ef7d')
    raw=small_gzip(pub['required_compressed_inputs']['patch_gzip']['path'])
    require(len(raw) == 388853 and hashlib.sha256(raw).hexdigest() == actual['patch_pin']['raw_sha256'] ==
            '050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f', 'unchanged exact saved patch; prior independent C/L byte proof applies')
    magic=b'RC-AUDIT-COPY-LITERAL-V1\0'; require(raw[:25] == magic, 'wire header')
    negative_checks=[]
    for label,start,reason,index in [('TARGET',57,'TARGET_DECODED_HASH',5),('BASE',25,'BASE_GZIP_RAW_HASH',6)]:
        plan=read(trial/('WRONG-FINAL-'+label+'-PLAN.json')); pinvalue=read(trial/('WRONG-FINAL-'+label+'-PIN.json'))
        negative=small_gzip(pinvalue['gzip_file']['path']); pin(pinvalue['gzip_file']['path'],pinvalue['gzip_file']['sha256'],pinvalue['gzip_file']['bytes'])
        require(negative == raw[:start]+bytes(32)+raw[start+32:] and hashlib.sha256(negative).hexdigest() == pinvalue['raw_sha256'], 'only32-byte identity header changes '+label)
        expected_plan=json.loads(json.dumps(actual['plan'])); expected_plan[label.lower()+'_identity']['sha256']='0'*64
        require(plan == expected_plan and pinvalue[label.lower()+'_raw_sha256'] == '0'*64, 'pathless corrupted identity binding '+label)
        row=actual['tests'][index]
        require(row['reason'] == reason and row['provisional_callback_bytes'] == 6629112 and
                row['provisional_target_sha256'] == actual['plan']['target_identity']['sha256'] and
                not row['verified_result_returned'] and not row['output_created'], 'post-stream refusal has no verified result '+label)
        negative_checks.append({'identity':label,'only_changed_byte_span':[start,start+32],'reason':reason,'provisional_bytes':6629112,'verified_result_returned':False})
    for i,name,reason in [(2,'base','PINNED_INPUT_HASH'),(3,'patch','PINNED_INPUT_HASH'),(4,'literal','TARGET_RANGE'),(7,'budget','OPTIONAL_OUTPUT_LIMIT')]:
        row=actual['tests'][i]
        require(row['reason'] == reason and row['consumer_pieces'] == 0 and not row['output_created'] and
                not (trial/('must-not-exist-'+name+'.json')).exists(), 'preflight refusal binding '+name)
    bad_base=json.loads(json.dumps(actual['plan'])); bad_base['base_gzip']['sha256']='0'*64
    bad_patch=json.loads(json.dumps(actual['patch_pin'])); bad_patch['gzip_file']['sha256']='0'*64
    low=json.loads(json.dumps(actual['plan'])); low['limits']['optional_output_bytes']=6629111
    require(read(trial/'BAD-BASE-GZIP-PLAN.json') == bad_base and read(trial/'BAD-PATCH-GZIP-PIN.json') == bad_patch and
            read(trial/'LOW-OPTIONAL-OUTPUT-PLAN.json') == low, 'single-field preflight corruption/budget fixtures')
    oversized=read(trial/'OVERSIZED-LITERAL-PIN.json'); malformed=small_gzip(oversized['gzip_file']['path'])
    require(len(malformed) == 106 and malformed[:97] == raw[:97] and malformed[97:98] == b'L' and
            struct.unpack('<Q',malformed[98:106])[0] == 6629113 and hashlib.sha256(malformed).hexdigest() == oversized['raw_sha256'], 'authenticated payload-free oversized literal control')
    marker=trial/'existing-output-must-stay.txt'
    require(marker.read_bytes() == b'keep original\n' and digest(marker) == actual['tests'][8]['existing_file_sha256'] and
            actual['tests'][8]['consumer_pieces'] == 0 and actual['tests'][8]['existing_output_unchanged'], 'existing output marker preserved')
    files=[r for r in trial.rglob('*') if r.is_file()]
    scratch=sum(r.stat().st_size for r in files)
    require(scratch == actual['resources']['scratch_bytes_before_receipt']+Path(actual_pin['path']).stat().st_size == 228624 and
            max(r.stat().st_size for r in files) < 1048576 and actual['resources']['max_rss_kib'] == 17900, 'actual bounded scratch/no large new raw artifact')
    return {'status':'PASS_SAVED_NINE_FIXED_COMPRESSED_ONLY_BYTE_RESTORE_CONTROLS',
            'publication':pub_pin,'original_and_published_file_pins':copies,'reference_pins':references,'actual_receipt':actual_pin,
            'launch_receipt':launch_pin,'prior_independent_exact_C_L_byte_proof':old_proof,'actual_tests':actual['tests'],
            'independent_negative_header_checks':negative_checks,'observed_resources':{'max_rss_kib':17900,'scratch_bytes':scratch,
                'address_space_cap_bytes':268435456,'scratch_cap_bytes':33554432,'outer_timeout_seconds':90},
            'qualifications':['No restorer/codec/driver was imported or run and no new restoration was performed by this saved reader.',
                'Current raw originals and compressed inputs were rehashed; the unchanged050b patch reuses the already independent all4879C/4880L direct byte comparison proof. Small preserved negative patches were decompressed only to inspect their exact header differences.',
                'Standalone restore received zero raw pins; the separate trial observer held the original target for independent comparison. Explicit optional comparison mode remains distinct.',
                'Wrong final identities streamed provisional bytes but returned no successful verification; callback/output chunks alone remain unverified.',
                'Fixed accepted1504→accepted168 byte restoration only, with no new theorem audit, prospective union, generic decoder or future full-union capacity acceptance.']}

def main():
    mode,destination=sys.argv[1],Path(sys.argv[2])
    report={'schema':'independent_saved_storage_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),
            'reviewer_sha256':digest(__file__),'target_modules_imported':False,'target_compiler_native_adapter_reference_processes_started':0,
            'capture_restore_or_producer_trial_rerun':False,'new_restored_or_captured_artifact_created':False,'mathematical_acceptance_modified':False}
    try:
        report.update({'wrapper':wrapper,'portable':portable}[mode]())
    except Exception as error:
        report.update(status='FAIL_SAVED_QC',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,indent=2,sort_keys=True); handle.write('\n')
    print(json.dumps({'path':str(destination),'sha256':digest(destination),'status':report['status']}))

if __name__ == '__main__':
    main()
