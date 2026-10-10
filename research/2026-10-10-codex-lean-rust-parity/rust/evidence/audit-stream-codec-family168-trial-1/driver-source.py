"""Scheduler/root-approved byte-only trial; not a compiler or theorem audit.

This driver must not run before the separately frozen source review and root
approval. It exercises only the existing accepted family168/union1504 pair.
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
import struct
import sys
import traceback

sys.dont_write_bytecode = True
SOURCE = Path(__file__).with_name('audit_copy_literal_codec.py')
SOURCE_SHA = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'
BASE_RAW = '/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json'
BASE_GZIP = '/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean/evidence/proof-extensions/g7-survival-integration/rc-lean-g7-survival-integration-20261010T223510.923050Z/COHERENT-PASS-UNION1504-EXPORT-V5-20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json.gz'
TARGET_RAW = '/dev/shm/rc-lean-g7-family-normalization-20261010T230143.534018Z/.build/runs/20261010T230235.850157Z/attempts/00003-OwnedAudit/work/AUDIT-RESULT.json'
BASE_SHA = '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813'
BASE_GZIP_SHA = 'ee19e06b02138e891f71b90f16497f0439dd2db0b00e4b191811c8f8f8f1be40'
TARGET_SHA = '0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e'
LEGACY_PATCH_SHA = '050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f'


def hash_file(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as f:
        while piece := f.read(65536):
            digest.update(piece)
    return digest.hexdigest()


def assert_true(value, detail):
    if not value:
        raise AssertionError(detail)


def write_json(codec, stage, name, value):
    raw = codec.encode_json(value)
    assert_true(codec.scratch_usage(ACTIVE_PLAN)+len(raw) <= ACTIVE_PLAN.limits.scratch_bytes,
                'receipt scratch limit')
    path = stage/name
    with path.open('xb') as f:
        f.write(raw)
    return path


def compare_files(a, b):
    compared = 0
    with Path(a).open('rb') as x, Path(b).open('rb') as y:
        while piece := x.read(65536):
            assert_true(y.read(len(piece)) == piece, 'optional output differs from original saved target')
            compared += len(piece)
        assert_true(y.read(1) == b'', 'optional output ends early')
    return compared


def expected_refusal(codec, plan, patch, output, reason):
    pieces = 0

    def observe(_piece):
        nonlocal pieces
        pieces += 1

    try:
        codec.restore(plan, patch, output=output, on_piece=observe)
    except codec.CodecRefusal as error:
        assert_true(error.reason == reason, 'wrong refusal reason: '+str(error))
        assert_true(pieces == 0, 'refusal exposed decoded target pieces')
        assert_true(not output.exists(), 'refusal created an output file')
        return {'status': 'PASS_EXPECTED_PREFLIGHT_REFUSAL', 'reason': error.reason,
                'output_created': False, 'consumer_pieces': pieces}
    raise AssertionError('invalid patch/limit unexpectedly accepted')


def run(stage):
    global ACTIVE_PLAN
    raw_source = SOURCE.read_bytes()
    assert_true(hashlib.sha256(raw_source).hexdigest() == SOURCE_SHA, 'codec source pin drift')
    stage.mkdir(exist_ok=False)
    # These are source text captures, never executables or compiled companions.
    with (stage/'codec-source.py').open('xb') as f:
        f.write(raw_source)
    with (stage/'driver-source.py').open('xb') as f:
        f.write(Path(__file__).read_bytes())
    spec = importlib.util.spec_from_file_location('pinned_audit_stream_codec', SOURCE)
    codec = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = codec
    spec.loader.exec_module(codec)
    memory_limit = codec.enforce_address_space_limit()
    plan = codec.Plan(codec.FilePin(BASE_RAW, 114300292, BASE_SHA),
                      codec.FilePin(BASE_GZIP, 7868154, BASE_GZIP_SHA),
                      codec.FilePin(TARGET_RAW, 6629112, TARGET_SHA), str(stage), codec.Limits())
    ACTIVE_PLAN = plan
    plan.validate()
    write_json(codec, stage, 'PLAN.json', plan.encode())
    tests = []
    patch, counts = codec.produce(plan, stage/'family168-from1504.monotone.copy-literal.gz')
    pin_file = write_json(codec, stage, 'PATCH-PIN.json', patch.encode())
    assert_true((patch.raw_bytes, patch.raw_sha256, patch.operations, patch.copies, patch.literals) ==
                (388853, LEGACY_PATCH_SHA, 9759, 4879, 4880), 'stream producer differs from exact legacy patch')
    assert_true(counts == {'base_records':100985, 'target_records':4907, 'exact_copied_records':4879,
                           'changed_records':19, 'new_records':9, 'backward_exact_records_literal':0},
                'stream producer record correspondence')
    tests.append({'name':'stream-producer-exact-legacy-patch','status':'PASS','records':counts,
                  'raw_patch_sha256':patch.raw_sha256,'patch_pin_sha256':hash_file(pin_file)})

    observed_digest = hashlib.sha256()
    observed_bytes = 0

    def observe(piece):
        nonlocal observed_bytes
        observed_digest.update(piece)
        observed_bytes += len(piece)

    result = codec.restore(plan, patch, on_piece=observe)
    assert_true(observed_bytes == 6629112 and observed_digest.hexdigest() == TARGET_SHA,
                'stream-only observer binding')
    assert_true(result['base_gzip_decompression_passes'] == 1 and result['output_file'] is None,
                'stream-only restore allocation')
    write_json(codec, stage, 'STREAM-RESTORE.json', result)
    tests.append({'name':'restore-to-hash-and-byte-comparison','status':'PASS','result':result,
                  'independent_observer_sha256':observed_digest.hexdigest()})

    output = stage/'family168.optional-exclusive-restored.json'
    file_result = codec.restore(plan, patch, output=output)
    assert_true(output.stat().st_size == 6629112 and hash_file(output) == TARGET_SHA,
                'optional output pin')
    assert_true(compare_files(output, TARGET_RAW) == 6629112, 'optional whole-byte comparison')
    write_json(codec, stage, 'EXCLUSIVE-OUTPUT-RESTORE.json', file_result)
    tests.append({'name':'optional-exclusive-output','status':'PASS','result':file_result})
    before = hash_file(output)
    try:
        codec.restore(plan, patch, output=output)
    except codec.CodecRefusal as error:
        assert_true(error.reason == 'OUTPUT_ALREADY_EXISTS', 'wrong no-overwrite reason')
    else:
        raise AssertionError('existing optional output overwritten')
    assert_true(hash_file(output) == before, 'existing optional output changed')
    tests.append({'name':'no-overwrite','status':'PASS','existing_file_sha256':before})

    bad_compressed = replace(patch, gzip_file=replace(patch.gzip_file, sha256='0'*64))
    write_json(codec, stage, 'BAD-COMPRESSED-HASH-PIN.json', bad_compressed.encode())
    tests.append({'name':'bad-compressed-hash-before-output',
                  **expected_refusal(codec, plan, bad_compressed,
                                     stage/'must-not-exist-bad-compressed.json','PINNED_INPUT_HASH')})
    bad_raw = replace(patch, raw_sha256='0'*64)
    write_json(codec, stage, 'BAD-RAW-HASH-PIN.json', bad_raw.encode())
    tests.append({'name':'bad-raw-hash-before-output',
                  **expected_refusal(codec, plan, bad_raw,
                                     stage/'must-not-exist-bad-raw.json','PATCH_RAW_HASH')})

    # This deliberately malformed patch has correct raw/gzip digests and a
    # correct trusted target header. Its first L exceeds target length and
    # carries no payload. It must fail TARGET_RANGE before payload reads/writes.
    oversized = (codec.MAGIC+bytes.fromhex(BASE_SHA)+bytes.fromhex(TARGET_SHA)
                 +struct.pack('<Q',6629112)+b'L'+struct.pack('<Q',6629113))
    malformed_path = stage/'oversized-literal.copy-literal.gz'
    codec.reserve_scratch(plan, len(oversized)+1024)
    with malformed_path.open('xb') as f:
        with gzip.GzipFile(fileobj=f, mode='wb', filename='', mtime=0, compresslevel=6) as z:
            z.write(oversized)
    malformed = codec.PatchPin(codec.FilePin(str(malformed_path), malformed_path.stat().st_size,
                                             hash_file(malformed_path)),
                                len(oversized), hashlib.sha256(oversized).hexdigest(),
                                114300292, BASE_SHA, 6629112, TARGET_SHA, 1, 0, 1, 6629112, True)
    write_json(codec, stage, 'OVERSIZED-LITERAL-PIN.json', malformed.encode())
    tests.append({'name':'oversized-literal-before-output',
                  **expected_refusal(codec, plan, malformed,
                                     stage/'must-not-exist-oversized.json','TARGET_RANGE')})
    low_output = replace(plan, limits=replace(plan.limits, optional_output_bytes=6629111))
    write_json(codec, stage, 'LOW-OPTIONAL-OUTPUT-PLAN.json', low_output.encode())
    tests.append({'name':'optional-output-size-before-output',
                  **expected_refusal(codec, low_output, patch,
                                     stage/'must-not-exist-output-limit.json','OPTIONAL_OUTPUT_LIMIT')})

    result = {
        'schema':'audit_stream_codec_fixture_review_v1',
        'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status':'PASS_EXISTING_ACCEPTED_1504_TO_168_BYTE_EXERCISE_ONLY',
        'passed':len(tests), 'total':8, 'tests':tests,
        'codec_source':{'path':str(SOURCE),'bytes':len(raw_source),'sha256':SOURCE_SHA},
        'driver_source':{'path':str(Path(__file__).resolve()),'sha256':hash_file(__file__)},
        'plan':plan.encode(), 'patch_pin':patch.encode(),
        'resources':{'address_space_cap_bytes':memory_limit,
                     'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                     'scratch_bytes_before_receipt':codec.scratch_usage(plan),'scratch_cap_bytes':plan.limits.scratch_bytes},
        'target_mmap_used':False,'new_large_raw_base_created':False,
        'stream_only_second_target_created':False,
        'optional_output_bytes':output.stat().st_size,
        'existing_evidence_modified':False,'compiler_native_reference_processes':0,
        'prospective1505_audit_created':False,'prospective1506_audit_created':False,
        'prospective1570_audit_created':False,'mathematical_acceptance_claim':False,
    }
    assert_true(len(tests)==8,'unexpected trial count')
    receipt = write_json(codec, stage, 'RECEIPT.json', result)
    print(json.dumps({'receipt':str(receipt),'sha256':hash_file(receipt),'status':result['status'],
                      'passed':len(tests),'scratch_bytes':codec.scratch_usage(plan),
                      'max_rss_kib':result['resources']['max_rss_kib']},sort_keys=True))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        run(args.output)
    except BaseException as error:
        failure={'status':'BYTE_CODEC_TRIAL_FAILURE_PRESERVED','error':str(error),
                 'traceback':traceback.format_exc(),
                 'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 'prospective_union_created':False,'mathematical_acceptance_claim':False}
        if args.output.is_dir() and not (args.output/'FAILURE.json').exists():
            with (args.output/'FAILURE.json').open('x') as f:
                f.write(json.dumps(failure,sort_keys=True,indent=2)+'\n')
        raise


if __name__=='__main__':
    main()
