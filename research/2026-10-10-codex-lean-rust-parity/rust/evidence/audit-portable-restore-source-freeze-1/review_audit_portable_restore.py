"""Frozen byte-only portable restore trial; root approval is required first.

Exercises only the already independently produced accepted1504/family168 pair.
No old producer/restore, mathematical audit, compiler, or native solver runs.
"""
import argparse
from dataclasses import replace
import datetime
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import sys
import traceback

sys.dont_write_bytecode = True
SOURCE = Path(__file__).with_name('audit_portable_restore.py')
SOURCE_SHA = '39543d989895218cc91c088a36c747a2a287a32513d37cffb5d2f87ea62a5755'
CODEC_SHA = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'
PACKET = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
BASE_GZIP = PACKET/'lean/evidence/proof-extensions/g7-survival-integration/rc-lean-g7-survival-integration-20261010T223510.923050Z/COHERENT-PASS-UNION1504-EXPORT-V5-20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json.gz'
BASE_GZIP_SHA = 'ee19e06b02138e891f71b90f16497f0439dd2db0b00e4b191811c8f8f8f1be40'
BASE_RAW = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json')
BASE_SHA = '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813'
TARGET_RAW = Path('/dev/shm/rc-lean-g7-family-normalization-20261010T230143.534018Z/.build/runs/20261010T230235.850157Z/attempts/00003-OwnedAudit/work/AUDIT-RESULT.json')
TARGET_SHA = '0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e'
SAVED = PACKET/'rust/evidence/audit-stream-codec-family168-trial-1'
PATCH_PIN_SHA = '86672418399f22212c3ed855ade0187207e5c72557b821e19992aed7615de77b'
PATCH_GZIP_SHA = '8ffaeca558d58b02632cbe3e3f56f5e7112bda7568a44525a6e55af7d4271e02'
RAW_PATCH_SHA = '050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f'


def hash_file(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as f:
        while piece := f.read(65536):
            digest.update(piece)
    return digest.hexdigest()


def require(value, detail):
    if not value:
        raise AssertionError(detail)


def write_json(codec, stage, name, value):
    raw = codec.encode_json(value)
    codec.reserve_scratch(ACTIVE_PLAN, len(raw))
    path = stage/name
    with path.open('xb') as f:
        f.write(raw)
    return path


def pre_output_refusal(portable, plan, pin, output, expected):
    pieces = 0

    def observe(_piece):
        nonlocal pieces
        pieces += 1

    try:
        portable.restore(plan, pin, output=output, on_piece=observe)
    except ValueError as error:
        require(getattr(error, 'reason', None) == expected, 'wrong refusal: '+str(error))
        require(pieces == 0 and not output.exists(), 'preflight refusal exposed output')
        return {'status':'PASS_EXPECTED_PREFLIGHT_REFUSAL', 'reason':expected,
                'consumer_pieces':pieces, 'output_created':False}
    raise AssertionError('expected preflight refusal did not occur')


def cap_address_space():
    cap = 256*1024*1024
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    hard = cap if hard == resource.RLIM_INFINITY else min(hard, cap)
    soft = hard if soft == resource.RLIM_INFINITY else min(soft, hard)
    resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return soft


def run(stage):
    global ACTIVE_PLAN
    memory_limit = cap_address_space()
    raw_source = SOURCE.read_bytes()
    require(hashlib.sha256(raw_source).hexdigest() == SOURCE_SHA, 'portable source drift')
    codec_source = SOURCE.with_name('audit_copy_literal_codec.py').read_bytes()
    require(hashlib.sha256(codec_source).hexdigest() == CODEC_SHA, 'accepted codec drift')
    require(hash_file(SAVED/'PATCH-PIN.json') == PATCH_PIN_SHA, 'saved patch pin drift')
    patch_path = SAVED/'family168-from1504.monotone.copy-literal.gz'
    require(patch_path.stat().st_size == 72532 and hash_file(patch_path) == PATCH_GZIP_SHA,
            'saved compressed patch drift')
    stage.mkdir(exist_ok=False)
    for name, raw in [('audit_portable_restore.py',raw_source),
                      ('audit_copy_literal_codec.py',codec_source),
                      ('review_audit_portable_restore.py',Path(__file__).read_bytes())]:
        with (stage/name).open('xb') as f:
            f.write(raw)
    # Import only the exact frozen wrapper, after the approved capped launch.
    spec = importlib.util.spec_from_file_location('fixed_portable_audit_restore', SOURCE)
    portable = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = portable
    spec.loader.exec_module(portable)
    codec = portable.pinned_codec()
    plan = portable.PortablePlan(codec.FilePin(str(BASE_GZIP),7868154,BASE_GZIP_SHA),
                                  portable.RawIdentity(114300292,BASE_SHA),
                                  portable.RawIdentity(6629112,TARGET_SHA),str(stage),codec.Limits())
    ACTIVE_PLAN = plan
    plan.validate()
    old_patch = codec.PatchPin.decode(codec.parse_small_json((SAVED/'PATCH-PIN.json').read_bytes()))
    # Pin relocation changes only the path to an already authenticated copy.
    patch = replace(old_patch, gzip_file=codec.FilePin(str(patch_path),72532,PATCH_GZIP_SHA))
    patch.validate(plan)
    write_json(codec,stage,'PORTABLE-PLAN.json',plan.encode())
    write_json(codec,stage,'PATCH-PIN.json',patch.encode())
    require('base_raw' not in plan.encode() and 'target_raw' not in plan.encode(),
            'portable request contains mandatory raw paths')
    tests = []

    # The restorer receives NO raw reference. This independent driver observer
    # alone holds the existing raw target and checks every yielded byte/hash.
    observed = 0
    digest = hashlib.sha256()
    with TARGET_RAW.open('rb') as target:
        def independent_observer(piece):
            nonlocal observed
            require(0 < len(piece) <= 65536, 'unbounded callback')
            require(target.read(len(piece)) == piece, 'standalone decoded byte mismatch')
            digest.update(piece)
            observed += len(piece)

        standalone = portable.restore(plan,patch,on_piece=independent_observer)
        require(target.read(1) == b'', 'independent target length mismatch')
    require(observed == 6629112 and digest.hexdigest() == TARGET_SHA,
            'independent complete target identity')
    require(standalone['required_raw_reference_files'] == 0 and
            not standalone['optional_base_reference_checked'] and
            not standalone['optional_target_reference_checked'] and
            standalone['output_file'] is None and
            standalone['base_gzip_decompression_passes'] == 1,
            'standalone compressed-only contract')
    write_json(codec,stage,'STANDALONE-RESTORE.json',standalone)
    tests.append({'name':'compressed-only-stream-restorer','status':'PASS','result':standalone,
                  'independent_driver_compared_bytes':observed,
                  'independent_driver_target_sha256':digest.hexdigest(),
                  'raw_references_passed_to_restorer':0})

    # Explicit optional references are a distinct API mode, not required inputs.
    base_ref = codec.FilePin(str(BASE_RAW),114300292,BASE_SHA)
    target_ref = codec.FilePin(str(TARGET_RAW),6629112,TARGET_SHA)
    compared = portable.restore(plan,patch,compare_base_raw=base_ref,compare_target_raw=target_ref)
    require(compared['optional_base_reference_checked'] and compared['optional_target_reference_checked']
            and compared['required_raw_reference_files'] == 0 and compared['output_file'] is None,
            'explicit optional comparisons')
    write_json(codec,stage,'OPTIONAL-COMPARISON-RESTORE.json',compared)
    tests.append({'name':'explicit-optional-comparison-references','status':'PASS','result':compared})

    bad_base = replace(plan,base_gzip=replace(plan.base_gzip,sha256='0'*64))
    write_json(codec,stage,'BAD-BASE-GZIP-PLAN.json',bad_base.encode())
    tests.append({'name':'wrong-compressed-base-before-output',
                  **pre_output_refusal(portable,bad_base,patch,stage/'must-not-exist-base.json',
                                       'PINNED_INPUT_HASH')})
    bad_patch = replace(patch,gzip_file=replace(patch.gzip_file,sha256='0'*64))
    write_json(codec,stage,'BAD-PATCH-GZIP-PIN.json',bad_patch.encode())
    tests.append({'name':'wrong-compressed-patch-before-output',
                  **pre_output_refusal(portable,plan,bad_patch,stage/'must-not-exist-patch.json',
                                       'PINNED_INPUT_HASH')})

    require(hash_file(SAVED/'OVERSIZED-LITERAL-PIN.json') ==
            '49d8c5da0d31a8ce990ddbb865637a2c46d641f1a064e6cbf3ae64c3a289aa59',
            'saved oversized-literal pin drift')
    oversized = codec.PatchPin.decode(codec.parse_small_json((SAVED/'OVERSIZED-LITERAL-PIN.json').read_bytes()))
    malformed_path = SAVED/'oversized-literal.copy-literal.gz'
    require(hash_file(malformed_path) == oversized.gzip_file.sha256,
            'saved oversized-literal fixture drift')
    oversized = replace(oversized,gzip_file=replace(oversized.gzip_file,path=str(malformed_path)))
    write_json(codec,stage,'OVERSIZED-LITERAL-PIN.json',oversized.encode())
    tests.append({'name':'oversized-literal-before-output',
                  **pre_output_refusal(portable,plan,oversized,stage/'must-not-exist-literal.json',
                                       'TARGET_RANGE')})

    # A small negative patch changes only its claimed target header/hash. Its
    # complete patch preflight passes; final target hashing MUST reject after
    # provisional chunks. This is a corruption control, never a new audit.
    with patch_path.open('rb') as compressed_file:
        with gzip.GzipFile(fileobj=compressed_file,mode='rb') as z:
            raw_patch = z.read(1048577)
    require(len(raw_patch) == 388853 and hashlib.sha256(raw_patch).hexdigest() == RAW_PATCH_SHA,
            'bounded saved raw patch drift')
    offset = len(codec.MAGIC)+32
    forged_raw = raw_patch[:offset]+bytes(32)+raw_patch[offset+32:]
    forged_path = stage/'wrong-final-target-hash.copy-literal.gz'
    codec.reserve_scratch(plan,1048576)
    with forged_path.open('xb') as file:
        with gzip.GzipFile(fileobj=file,mode='wb',filename='',mtime=0,compresslevel=6) as z:
            z.write(forged_raw)
    forged_plan = replace(plan,target_identity=portable.RawIdentity(6629112,'0'*64))
    forged_pin = replace(patch,gzip_file=codec.FilePin(str(forged_path),forged_path.stat().st_size,
                                                      hash_file(forged_path)),
                         raw_sha256=hashlib.sha256(forged_raw).hexdigest(),target_raw_sha256='0'*64)
    write_json(codec,stage,'WRONG-FINAL-TARGET-PLAN.json',forged_plan.encode())
    write_json(codec,stage,'WRONG-FINAL-TARGET-PIN.json',forged_pin.encode())
    provisional_bytes = 0
    provisional_hash = hashlib.sha256()
    def provisional(piece):
        nonlocal provisional_bytes
        provisional_bytes += len(piece)
        provisional_hash.update(piece)
    try:
        portable.restore(forged_plan,forged_pin,on_piece=provisional)
    except ValueError as error:
        require(getattr(error,'reason',None) == 'TARGET_DECODED_HASH', 'wrong final identity refusal')
    else:
        raise AssertionError('forged target identity received successful result')
    require(provisional_bytes == 6629112 and provisional_hash.hexdigest() == TARGET_SHA,
            'final-refusal control did not stream the original target')
    tests.append({'name':'wrong-final-target-hash-after-provisional-stream',
                  'status':'PASS_EXPECTED_FINAL_IDENTITY_REFUSAL','reason':'TARGET_DECODED_HASH',
                  'provisional_callback_bytes':provisional_bytes,
                  'provisional_target_sha256':provisional_hash.hexdigest(),
                  'verified_result_returned':False,'output_created':False})

    # The base expected raw hash is also independently enforced, including
    # skipped bytes and its uncopied tail, not merely the copied fragments.
    base_offset = len(codec.MAGIC)
    bad_base_raw_patch = raw_patch[:base_offset]+bytes(32)+raw_patch[base_offset+32:]
    bad_base_path = stage/'wrong-final-base-hash.copy-literal.gz'
    codec.reserve_scratch(plan,1048576)
    with bad_base_path.open('xb') as file:
        with gzip.GzipFile(fileobj=file,mode='wb',filename='',mtime=0,compresslevel=6) as z:
            z.write(bad_base_raw_patch)
    bad_base_plan = replace(plan,base_identity=portable.RawIdentity(114300292,'0'*64))
    bad_base_pin = replace(patch,gzip_file=codec.FilePin(str(bad_base_path),bad_base_path.stat().st_size,
                                                       hash_file(bad_base_path)),
                          raw_sha256=hashlib.sha256(bad_base_raw_patch).hexdigest(),base_raw_sha256='0'*64)
    write_json(codec,stage,'WRONG-FINAL-BASE-PLAN.json',bad_base_plan.encode())
    write_json(codec,stage,'WRONG-FINAL-BASE-PIN.json',bad_base_pin.encode())
    provisional_bytes = 0
    provisional_hash = hashlib.sha256()
    try:
        portable.restore(bad_base_plan,bad_base_pin,on_piece=provisional)
    except ValueError as error:
        require(getattr(error,'reason',None) == 'BASE_GZIP_RAW_HASH', 'wrong final base identity refusal')
    else:
        raise AssertionError('forged base identity received successful result')
    require(provisional_bytes == 6629112 and provisional_hash.hexdigest() == TARGET_SHA,
            'base-final-refusal control did not stream the original target')
    tests.append({'name':'wrong-final-base-hash-after-provisional-stream',
                  'status':'PASS_EXPECTED_FINAL_IDENTITY_REFUSAL','reason':'BASE_GZIP_RAW_HASH',
                  'provisional_callback_bytes':provisional_bytes,
                  'provisional_target_sha256':provisional_hash.hexdigest(),
                  'verified_result_returned':False,'output_created':False})

    low_output = replace(plan,limits=replace(plan.limits,optional_output_bytes=6629111))
    write_json(codec,stage,'LOW-OPTIONAL-OUTPUT-PLAN.json',low_output.encode())
    tests.append({'name':'optional-output-size-before-output',
                  **pre_output_refusal(portable,low_output,patch,stage/'must-not-exist-budget.json',
                                       'OPTIONAL_OUTPUT_LIMIT')})
    marker = stage/'existing-output-must-stay.txt'
    with marker.open('xb') as f:
        f.write(b'keep original\n')
    before = hash_file(marker)
    count = 0
    def no_pieces(_piece):
        nonlocal count
        count += 1
    try:
        portable.restore(plan,patch,output=marker,on_piece=no_pieces)
    except ValueError as error:
        require(getattr(error,'reason',None) == 'OUTPUT_ALREADY_EXISTS', 'wrong existing-output refusal')
    else:
        raise AssertionError('existing output unexpectedly accepted')
    require(hash_file(marker) == before and count == 0, 'existing output changed')
    tests.append({'name':'no-overwrite','status':'PASS','existing_file_sha256':before,
                  'consumer_pieces':count,'existing_output_unchanged':True})

    require(len(tests) == 9, 'unexpected portable trial count')
    result={'schema':'audit_portable_restore_fixture_review_v1',
            'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'status':'PASS_FIXED_EXISTING_1504_TO_168_PORTABLE_RESTORE_ONLY',
            'passed':9,'total':9,'tests':tests,
            'source':{'path':str(SOURCE),'sha256':SOURCE_SHA,'bytes':len(raw_source)},
            'driver':{'path':str(Path(__file__).resolve()),'sha256':hash_file(__file__)},
            'codec_dependency_sha256':CODEC_SHA,'plan':plan.encode(),'patch_pin':patch.encode(),
            'raw_comparison_references_used_by_driver':[{'path':str(BASE_RAW),'bytes':114300292,'sha256':BASE_SHA},
                                                       {'path':str(TARGET_RAW),'bytes':6629112,'sha256':TARGET_SHA}],
            'resources':{'address_space_cap_bytes':memory_limit,
                         'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                         'scratch_bytes_before_receipt':codec.scratch_usage(plan),
                         'scratch_cap_bytes':plan.limits.scratch_bytes},
            'old_codec_producer_or_restore_called':False,'new_large_raw_files_created':0,
            'future_union_created':False,'mathematical_acceptance_claim':False,
            'compiler_native_reference_processes':0}
    receipt=write_json(codec,stage,'RECEIPT.json',result)
    print(json.dumps({'receipt':str(receipt),'sha256':hash_file(receipt),
                      'passed':9,'status':result['status'],
                      'max_rss_kib':result['resources']['max_rss_kib'],
                      'scratch_bytes':codec.scratch_usage(plan)},sort_keys=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        run(args.output)
    except BaseException as error:
        failure={'status':'PORTABLE_BYTE_TRIAL_FAILURE_PRESERVED','error':str(error),
                 'traceback':traceback.format_exc(),'future_union_created':False,
                 'mathematical_acceptance_claim':False}
        if args.output.is_dir() and not (args.output/'FAILURE.json').exists():
            with (args.output/'FAILURE.json').open('x') as f:
                f.write(json.dumps(failure,sort_keys=True,indent=2)+'\n')
        raise


if __name__=='__main__':
    main()
