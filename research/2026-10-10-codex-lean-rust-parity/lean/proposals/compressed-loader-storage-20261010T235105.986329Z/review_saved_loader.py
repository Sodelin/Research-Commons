#!/usr/bin/env python3
"""Planned byte-only trial. Never invokes a compiler or other subprocess."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
WRAPPER_SHA = 'ac6033fb98e9d13d2910d0c95d0015540a3aa0472b25963a7b2dc27fe2bed751'
SAVED_RAW = Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z/.build/runs/20261010T232230.265801Z/attempts/00001-G6OriginalParallelArmTransport/NATIVE-LOADER.259880')
SAVED_RAW_SHA = '830f7c33aed836755cbe788f5f69343fa15b575c3267305c8ff249708de861f8'
SAVED_RECEIPT = SAVED_RAW.parent/'receipt.json'
SAVED_RECEIPT_SHA = '13f45e94ddd8e3e3721ac45600a7f4ab07dae5d976d9ea85de8e1fecd4102059'

def sha(p):
    h = hashlib.sha256()
    with Path(p).open('rb') as f:
        for data in iter(lambda:f.read(65536), b''):
            h.update(data)
    return h.hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    wrapper = HERE/'storage_wrapper.py'
    inputs = {str(wrapper):WRAPPER_SHA, str(SAVED_RAW):SAVED_RAW_SHA,
              str(SAVED_RECEIPT):SAVED_RECEIPT_SHA}
    assert all(sha(p)==s for p,s in inputs.items())
    spec = importlib.util.spec_from_file_location('frozen_storage_trial', wrapper)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    expected = json.loads(SAVED_RECEIPT.read_text())
    controls = []
    def accept(name, function):
        value = function()
        controls.append({'control':name,'status':'PASS','detail':value})
        return value
    def refuse(name, function, exception_types):
        try:
            function()
        except exception_types as error:
            controls.append({'control':name,'status':'PASS_EXPECTED_REFUSAL',
                             'exception_type':type(error).__name__,'reason':str(error)})
        else:
            raise AssertionError('required refusal missing: '+name)
    primary_path = args.output/'saved-native-loader.gz'
    primary = accept('saved_raw_lossless_capture',
                     lambda:module.capture_saved_file(SAVED_RAW, primary_path))
    assert primary['raw_sha256']==SAVED_RAW_SHA and primary['raw_bytes']==SAVED_RAW.stat().st_size
    assert primary['eof'] and primary['complete'] and not primary['truncated']
    accept('native_init_parser_exact_original_receipt',
           lambda: {'native_library_count':len(primary['native_used'])}
           if primary['native_used']==sorted(expected['native_initialized_libraries']) else
           (_ for _ in ()).throw(AssertionError('calling-init identities differ')))
    crossing = args.output/'cross-chunk-diagnostic.raw'
    crossing.write_bytes(b'x'*(module.READ_BYTES-3)+b'sorryAx\n')
    crossed_path = args.output/'cross-chunk-diagnostic.gz'
    crossed = module.capture_saved_file(crossing, crossed_path)
    accept('sorryAx_crosses_read_boundary',
           lambda:{'detected':True} if 'sorryAx' in module.inspect_capture(
               crossed_path,crossed['raw_sha256'],crossed['raw_bytes'])['text'] else
           (_ for _ in ()).throw(AssertionError('cross-chunk diagnostic missed')))
    unknown = args.output/'unknown-native.raw'
    unknown.write_bytes(b'calling init: /not/a/pinned/library.so\n')
    unknown_capture = module.capture_saved_file(unknown,args.output/'unknown-native.gz')
    accept('unbound_native_library_fails_original_known_predicate',
           lambda:{'native_known':False} if not all(p in expected['native_initialized_libraries']
               for p in unknown_capture['native_used']) else
           (_ for _ in ()).throw(AssertionError('unbound library accepted')))
    refuse('forged_raw_digest',lambda:module.inspect_capture(primary_path,'0'*64,primary['raw_bytes']),(ValueError,))
    refuse('forged_raw_count',lambda:module.inspect_capture(primary_path,primary['raw_sha256'],primary['raw_bytes']-1),(ValueError,))
    broken = args.output/'missing-gzip-eof.gz'
    broken.write_bytes(primary_path.read_bytes()[:-8])
    refuse('gzip_trailer_eof_required',lambda:module.inspect_capture(broken,primary['raw_sha256'],primary['raw_bytes']),(EOFError,OSError))
    refuse('decoded_byte_limit',lambda:module.capture_saved_file(SAVED_RAW,args.output/'raw-limit.gz',raw_limit=64),(module.CaptureLimit,))
    refuse('encoded_byte_limit',lambda:module.capture_saved_file(crossing,args.output/'gzip-limit.gz',gzip_limit=16),(module.CaptureLimit,))
    primary_before = sha(primary_path)
    refuse('refuse_destination_overwrite',lambda:module.capture_saved_file(SAVED_RAW,primary_path),(FileExistsError,))
    assert sha(primary_path)==primary_before
    assert all(sha(p)==s for p,s in inputs.items())
    report={'status':'PASS_ALL_SAVED_BYTE_CONTROLS','controls':controls,'control_count':len(controls),
            'script_sha256':sha(__file__),'inputs':inputs,'inputs_unchanged':True,
            'compiler_native_or_subprocess_calls':0,'source_wrapper_only':True,
            'positive_capture':primary,'logging_qualification':'Saved existing separated native log exercises lossless encoding and parser, not a fresh combined-stderr compiler invocation.',
            'runtime_capture_process_or_builder_exercised':False}
    (args.output/'RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'controls':len(controls),'receipt':str(args.output/'RECEIPT.json')}))

if __name__=='__main__':
    main()
