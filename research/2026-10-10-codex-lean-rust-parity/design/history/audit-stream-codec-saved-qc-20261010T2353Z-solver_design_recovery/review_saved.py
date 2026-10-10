#!/usr/bin/env python3
"""Verify already saved byte trial, all patch ranges and controls; no restore."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
import mmap
from pathlib import Path
import struct
import sys

ROOT=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
EXPORT=ROOT/'rust/evidence/audit-stream-codec-family168-trial-1'
PUBLICATION_SHA='9f5584bcfbed73a400b7bb4512fa6503f9f271060806c1aef75bb67574c81c57'
RECEIPT_SHA='e5c529958b3d7a5ef25f8dc6c8833b28fe5f6f036c0fccbadf7dc4153b9c63f4'
LAUNCH_SHA='7f45e9c638f54396e8fc89c381c0ac8b57cbf9be60e1401004ff26198ebf3748'
TARGET_SHA='0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e'
RAW_PATCH_SHA='050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f'
MAGIC=b'RC-AUDIT-COPY-LITERAL-V1\x00'

def demand(condition,reason):
    if not condition:raise AssertionError(reason)

def sha(raw):return hashlib.sha256(raw).hexdigest()

def pin(row):
    path=Path(row['path']);digest=hashlib.sha256();size=0
    with path.open('rb') as handle:
        while raw:=handle.read(65536):digest.update(raw);size+=len(raw)
    demand(digest.hexdigest()==row['sha256'] and size==row['bytes'],'byte pin '+str(path))
    return {'path':str(path),'sha256':digest.hexdigest(),'bytes':size}

def load(name):return json.loads((EXPORT/name).read_text())

def check():
    publication_pin=pin({'path':str(EXPORT/'PUBLICATION.json'),'bytes':14237,'sha256':PUBLICATION_SHA})
    publication=load('PUBLICATION.json')
    demand(publication['status']=='PASS_EIGHT_FIXED_EXISTING_AUDIT_BYTE_CONTROLS_ONLY','publication scope')
    copied=[]
    for row in publication['copied_files']:
        original=pin(row['original']);published=pin(row['published'])
        demand(Path(original['path']).read_bytes()==Path(published['path']).read_bytes(),'lossless publication copy')
        demand(not Path(published['path']).read_bytes().startswith(b'\x7fELF'),'no published ELF')
        copied.append({'original':original,'published':published})
    demand(len(copied)==17 and sum(row['published']['bytes'] for row in copied)==publication['copied_bytes']==135088,'17 exact small files')
    readiness=[pin(row) for row in publication['source_freeze_and_approval']]
    demand(not publication['future_union_audit_created'] and not publication['mathematical_acceptance_claim'],'not new scientific audit')
    receipt=load('RECEIPT.json')
    receipt_pin=pin(publication['trial_receipt'])
    demand(receipt_pin['sha256']==RECEIPT_SHA and receipt['status']=='PASS_EXISTING_ACCEPTED_1504_TO_168_BYTE_EXERCISE_ONLY'
           and receipt['passed']==receipt['total']==8,'actual eight-case trial')
    launch=load('launch/RECEIPT.json')
    launch_pin=pin({'path':str(EXPORT/'launch/RECEIPT.json'),'bytes':2741,'sha256':LAUNCH_SHA})
    scenario=json.loads((ROOT/'rust/evidence/audit-stream-codec-source-freeze-1/SCENARIO.json').read_text())
    demand(launch['argv']==scenario['planned_argv'] and launch['return_code']==0 and not launch['timed_out']
           and launch['status']=='COMPLETED_BYTE_DRIVER','actual authorized launch')
    demand(receipt['plan']==scenario['plan']==load('PLAN.json')==publication['comparison_input_refs'],'frozen/actual plan equality')
    launch_pins=[pin(row) for row in launch['pinned_inputs']]
    stdout=json.loads((EXPORT/'launch/stdout').read_text())
    demand(stdout['sha256']==RECEIPT_SHA and stdout['passed']==8,'actual process output binds receipt')
    demand((EXPORT/'launch/stderr').read_bytes()==b'','successful driver stderr empty')
    plan=receipt['plan']
    input_pins=[pin(plan[name]) for name in ('base_raw','base_gzip','target_raw')]
    patch_pin=load('PATCH-PIN.json')
    demand(patch_pin==receipt['patch_pin'],'exact separately preserved patch pin')
    gzip_pin=pin(patch_pin['gzip_file'])
    compressed=(EXPORT/'family168-from1504.monotone.copy-literal.gz').read_bytes()
    old=ROOT/'rust/evidence/audit-byte-delta-feasibility-1'
    demand(compressed==(old/'family168-from1504.copy-literal.gz').read_bytes(),'exact old compressed patch')
    raw=gzip.decompress(compressed)
    demand(raw==(old/'family168-from1504.copy-literal').read_bytes() and sha(raw)==RAW_PATCH_SHA and len(raw)==388853,'exact old raw patch')
    demand(raw[:25]==MAGIC and raw[25:57].hex()==plan['base_raw']['sha256'] and raw[57:89].hex()==TARGET_SHA
           and struct.unpack_from('<Q',raw,89)[0]==6629112,'patch header binds exact saved source/target')
    target=Path(plan['target_raw']['path']).read_bytes()
    cursor=97;position=0;source_end=0;copies=literals=copied_bytes=literal_bytes=0
    with Path(plan['base_raw']['path']).open('rb') as handle:
        with mmap.mmap(handle.fileno(),0,access=mmap.ACCESS_READ) as base:
            while cursor<len(raw):
                opcode=raw[cursor:cursor+1];cursor+=1
                if opcode==b'C':
                    demand(cursor+16<=len(raw),'complete copy frame')
                    start,length=struct.unpack_from('<QQ',raw,cursor);cursor+=16
                    demand(length>0 and source_end<=start and start+length<=len(base) and position+length<=len(target),'copy source/target bounds and encoded monotonicity')
                    demand(base[start:start+length]==target[position:position+length],'every saved copy equals original target bytes')
                    source_end=start+length;copies+=1;copied_bytes+=length
                elif opcode==b'L':
                    demand(cursor+8<=len(raw),'complete literal frame')
                    length=struct.unpack_from('<Q',raw,cursor)[0];cursor+=8
                    demand(length>0 and cursor+length<=len(raw) and position+length<=len(target),'literal bounds before byte inspection')
                    demand(raw[cursor:cursor+length]==target[position:position+length],'every literal equals original target bytes')
                    cursor+=length;literals+=1;literal_bytes+=length
                else:raise AssertionError('unknown patch opcode')
                position+=length
    demand(cursor==len(raw) and position==6629112 and (copies,literals,copied_bytes,literal_bytes)==(4879,4880,6367219,261893),'independent complete exact patch partition')
    demand((patch_pin['operations'],patch_pin['copies'],patch_pin['literals'],patch_pin['decoded_bytes'])==(9759,4879,4880,6629112)
           and patch_pin['source_copies_monotone'] is True,'patch pin exact counts')
    optional_pin=pin(publication['omitted_fixed_shmem_restored_target'])
    demand(optional_pin['sha256']==TARGET_SHA and Path(optional_pin['path']).read_bytes()==target,'already saved optional output whole-byte equality')
    demand(not (EXPORT/Path(optional_pin['path']).name).exists(),'large optional duplicate omitted from small export')
    expected=['stream-producer-exact-legacy-patch','restore-to-hash-and-byte-comparison','optional-exclusive-output','no-overwrite',
              'bad-compressed-hash-before-output','bad-raw-hash-before-output','oversized-literal-before-output','optional-output-size-before-output']
    tests=receipt['tests']
    demand([t['name'] for t in tests]==expected,'exact eight actual outcomes')
    demand(tests[0]['records']=={'backward_exact_records_literal':0,'base_records':100985,'changed_records':19,
                               'exact_copied_records':4879,'new_records':9,'target_records':4907},'exact producer record correspondence')
    for index,artifact in ((1,'STREAM-RESTORE.json'),(2,'EXCLUSIVE-OUTPUT-RESTORE.json')):
        result=tests[index]['result']
        demand(result==load(artifact) and result['status']=='PASS_PINNED_SAVED_BYTE_RESTORATION'
               and result['base_gzip_decompression_passes']==1 and result['base_raw_bytes_hashed']==114300292
               and result['target_bytes_compared']==6629112 and result['target_sha256']==TARGET_SHA
               and result['byte_for_byte_equal'] and result['patch_preflight_completed_before_output'],'saved complete restore result '+artifact)
    demand(tests[1]['result']['output_file'] is None and not tests[1]['result']['second_target_artifact_created']
           and tests[1]['independent_observer_sha256']==TARGET_SHA,'stream-only hash/no second target')
    demand(tests[2]['result']['output_file']==optional_pin['path'] and tests[3]['existing_file_sha256']==TARGET_SHA,'saved exclusive/no-overwrite output binding')
    zero='0'*64
    bad_compressed=load('BAD-COMPRESSED-HASH-PIN.json');bad_raw=load('BAD-RAW-HASH-PIN.json')
    restored=json.loads(json.dumps(bad_compressed));restored['gzip_file']['sha256']=patch_pin['gzip_file']['sha256']
    demand(restored==patch_pin and bad_compressed['gzip_file']['sha256']==zero,'only compressed digest differs in control')
    restored=json.loads(json.dumps(bad_raw));restored['raw_sha256']=RAW_PATCH_SHA
    demand(restored==patch_pin and bad_raw['raw_sha256']==zero,'only raw digest differs in control')
    malformed_pin=load('OVERSIZED-LITERAL-PIN.json')
    malformed_gzip=pin(malformed_pin['gzip_file'])
    malformed=gzip.decompress((EXPORT/'oversized-literal.copy-literal.gz').read_bytes())
    demand(len(malformed)==malformed_pin['raw_bytes']==106 and sha(malformed)==malformed_pin['raw_sha256']
           and malformed[:97]==raw[:97] and malformed[97:98]==b'L'
           and struct.unpack_from('<Q',malformed,98)[0]==6629113,'authenticated oversize literal with no payload')
    demand((malformed_pin['operations'],malformed_pin['copies'],malformed_pin['literals'],malformed_pin['decoded_bytes'])==(1,0,1,6629112),'exact malformed control pin')
    low=load('LOW-OPTIONAL-OUTPUT-PLAN.json');patched=json.loads(json.dumps(low));patched['limits']['optional_output_bytes']=16777216
    demand(patched==plan and low['limits']['optional_output_bytes']==6629111,'only optional-output allowance differs')
    reasons=['PINNED_INPUT_HASH','PATCH_RAW_HASH','TARGET_RANGE','OPTIONAL_OUTPUT_LIMIT']
    absent=['must-not-exist-bad-compressed.json','must-not-exist-bad-raw.json','must-not-exist-oversized.json','must-not-exist-output-limit.json']
    for test,reason,name in zip(tests[4:],reasons,absent):
        demand(test['status']=='PASS_EXPECTED_PREFLIGHT_REFUSAL' and test['reason']==reason
               and test['consumer_pieces']==0 and test['output_created'] is False,'actual zero-output refusal '+name)
        demand(not (Path(plan['scratch_root'])/name).exists(),'refused output absent '+name)
    scratch_files=[p for p in Path(plan['scratch_root']).rglob('*') if p.is_file()]
    scratch_bytes=sum(p.stat().st_size for p in scratch_files)
    demand(scratch_bytes==stdout['scratch_bytes']==6759275 and scratch_bytes<33554432,'actual saved scratch bytes')
    demand(receipt['resources']['scratch_bytes_before_receipt']+receipt_pin['bytes']==scratch_bytes,'before/after receipt scratch accounting')
    demand(receipt['resources']['address_space_cap_bytes']==268435456 and receipt['resources']['max_rss_kib']==162780
           and receipt['resources']['max_rss_kib']*1024<268435456,'recorded capped memory observation')
    demand(receipt['compiler_native_reference_processes']==launch['compiler_native_reference_processes']==0
           and not receipt['prospective1505_audit_created'] and not receipt['prospective1506_audit_created']
           and not receipt['prospective1570_audit_created'] and not receipt['mathematical_acceptance_claim'],'byte-only scope')
    return {'status':'PASS_INDEPENDENT_SAVED_BYTE_AND_EIGHT_OUTCOME_QC; no fresh codec or restore run',
            'publication':publication_pin,'lossless_copied_files':copied,'source_freeze_and_approval':readiness,
            'actual_trial':receipt_pin,'actual_launch':launch_pin,'launch_pinned_inputs':launch_pins,
            'saved_comparison_inputs':input_pins,'actual_patch_gzip':gzip_pin,'saved_optional_output':optional_pin,
            'independent_patch_partition':{'raw_bytes':388853,'raw_sha256':RAW_PATCH_SHA,'gzip_bytes':72532,
                'copy_ops':4879,'literal_ops':4880,'all_ops':9759,'copied_bytes':6367219,'literal_bytes':261893,
                'target_bytes':6629112,'monotone_nonoverlapping_in_encoded_order':True,
                'every_copy_and_literal_compared_to_existing_original_target':True,'exact_legacy_raw_and_gzip_bytes':True},
            'eight_actual_outcomes':tests,'independently_authenticated_oversized_literal':malformed_gzip,
            'observed_saved_allocation':{'trial_scratch_bytes':scratch_bytes,'trial_scratch_files':len(scratch_files),
                'driver_reported_max_rss_kib':162780,'address_space_cap_bytes':268435456,'scratch_cap_bytes':33554432,
                'small_export_bytes':135088,'publication_bytes':14237,'whole_eight_case_elapsed_seconds':launch['elapsed_seconds']},
            'scope':['Only existing accepted1504 raw/gzip and existing accepted168 raw target were used.',
                'This reviewer authenticated saved bytes and outcomes, compared original/restored output, and checked every C/L range; it did not execute the target codec, produce a patch, or restore output.',
                'Source-level streaming/no-target-mmap claims are bound to the independently reviewed source; recorded one-pass/resource observations were not independently rerun.',
                'The recorded elapsed time covers the entire eight-case driver, not one standalone restoration.',
                'Original raw base and raw target remain mandatory comparison inputs; future actual unions require separate execution, pins, budget and acceptance.',
                'No theorem/audit synthesis, broader untrusted codec acceptance, scientific/runtime promotion or future compression/capacity result follows.']}

def main():
    destination=Path(sys.argv[1])
    report={'schema':'audit_stream_codec_independent_saved_design_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
            'target_codec_imports_or_executions':0,'fresh_patch_or_restore_outputs_created':0,
            'compiler_evaluator_native_reference_processes_started':0,'scientific_acceptance_modified':False}
    try:report.update(check())
    except Exception as error:report.update(status='FAIL_SAVED_BYTE_QC',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:json.dump(report,handle,indent=2,sort_keys=True);handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':sha(destination.read_bytes())}))
    return 1 if report['status']=='FAIL_SAVED_BYTE_QC' else 0

if __name__=='__main__':raise SystemExit(main())
