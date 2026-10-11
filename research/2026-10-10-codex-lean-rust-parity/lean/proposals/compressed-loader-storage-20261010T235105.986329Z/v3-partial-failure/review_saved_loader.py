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
WRAPPER_SHA = 'd774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810'
SAVED_RAW = Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z/.build/runs/20261010T232230.265801Z/attempts/00001-G6OriginalParallelArmTransport/NATIVE-LOADER.259880')
SAVED_RAW_SHA = '830f7c33aed836755cbe788f5f69343fa15b575c3267305c8ff249708de861f8'
SAVED_RECEIPT = SAVED_RAW.parent/'receipt.json'
SAVED_RECEIPT_SHA = '13f45e94ddd8e3e3721ac45600a7f4ab07dae5d976d9ea85de8e1fecd4102059'
CORE_PATH = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean/scripts/build_connected.py')
CORE_SHA = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'

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
              str(SAVED_RECEIPT):SAVED_RECEIPT_SHA, str(CORE_PATH):CORE_SHA}
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
           if primary['native_used']==sorted(expected['native_initialized_libraries']) and
           module.native_evidence_known(primary,primary['native_used'],expected['native_initialized_libraries']) else
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
           lambda:{'native_known':False} if not module.native_evidence_known(unknown_capture,unknown_capture['native_used'],
               expected['native_initialized_libraries']) else
           (_ for _ in ()).throw(AssertionError('unbound library accepted')))
    for label, raw_data in [('empty_native_evidence',b''),
                            ('diagnostic_without_native_init',b'Lean diagnostic only\n')]:
        raw_path = args.output/(label+'.raw')
        raw_path.write_bytes(raw_data)
        capture = module.capture_saved_file(raw_path,args.output/(label+'.gz'))
        accept(label+'_refused_by_invoke_helper',
               lambda capture=capture:{'native_known':False} if not module.native_evidence_known(
                   capture,capture['native_used'],expected['native_initialized_libraries']) else
               (_ for _ in ()).throw(AssertionError('missing native evidence accepted')))
    refuse('forged_raw_digest',lambda:module.inspect_capture(primary_path,'0'*64,primary['raw_bytes']),(ValueError,))
    refuse('forged_raw_count',lambda:module.inspect_capture(primary_path,primary['raw_sha256'],primary['raw_bytes']-1),(ValueError,))
    broken = args.output/'missing-gzip-eof.gz'
    broken.write_bytes(primary_path.read_bytes()[:-8])
    refuse('gzip_trailer_eof_required',lambda:module.inspect_capture(broken,primary['raw_sha256'],primary['raw_bytes']),(EOFError,OSError))
    refuse('decoded_byte_limit',lambda:module.capture_saved_file(SAVED_RAW,args.output/'raw-limit.gz',raw_limit=64),(module.CaptureLimit,))
    refuse('encoded_byte_limit',lambda:module.capture_saved_file(crossing,args.output/'gzip-limit.gz',gzip_limit=16),(module.CaptureLimit,))
    partials = []
    for label in ['raw-limit','gzip-limit']:
        prefix = args.output/(label+'.gz')
        sidecar = json.loads(prefix.with_name(prefix.name+'.FAILED-PARTIAL.json').read_text())
        assert sidecar['status']=='FAILED_PARTIAL_CAPTURE_NOT_VERIFIED'
        assert not sidecar['complete'] and sidecar['truncated'] and not sidecar['eof']
        assert not sidecar['gzip_integrity_verified'] and 'raw_sha256' not in sidecar
        assert sidecar['preserved_gzip_prefix_sha256']==sha(prefix)
        assert sidecar['preserved_gzip_prefix_bytes']==prefix.stat().st_size
        partials.append({'failure':label,'sidecar_status':sidecar['status'],
                         'prefix_bytes':prefix.stat().st_size,'prefix_sha256':sha(prefix)})
    accept('failed_cap_captures_preserve_explicit_partial_identities',lambda:partials)
    primary_before = sha(primary_path)
    refuse('refuse_destination_overwrite',lambda:module.capture_saved_file(SAVED_RAW,primary_path),(FileExistsError,))
    assert sha(primary_path)==primary_before
    # Inert byte-storage exercise only. Import definitions but never construct
    # canonical Builder: its constructor would inspect a toolchain/process.
    core_spec = importlib.util.spec_from_file_location('inert_core_storage_trial',CORE_PATH)
    core = importlib.util.module_from_spec(core_spec)
    core_spec.loader.exec_module(core)
    inert_parent = type('InertParent',(core.Builder,),{})
    storage = module.make_builder_class(inert_parent,core,{
        'raw_limit_bytes':module.RAW_LIMIT_BYTES,'gzip_limit_bytes':module.GZIP_LIMIT_BYTES,
        'runtime_authorized':False})
    builder = object.__new__(storage)
    builder.run, builder.cache = args.output/'inert-run', args.output/'inert-cache'
    builder.cache.mkdir()
    fresh = builder.run/'attempts'/'inert'/'fixture.olean'
    fresh.parent.mkdir(parents=True)
    fresh.write_bytes(b'INERT BYTES: not a checked Lean object\n')
    fresh.with_suffix('.ilean').write_bytes(b'INERT COMPANION BYTES\n')
    record = {'status':'INERT_STORAGE_CONTROL_ONLY','object_artifacts':core.artifact_bundle(fresh)}
    cached = builder.cache_result('a'*64,record,fresh)
    cached_object = Path(cached['cached_object'])
    aliases = []
    for suffix in record['object_artifacts']:
        a,b=core.companion(fresh,suffix),core.companion(cached_object,suffix)
        assert (a.stat().st_dev,a.stat().st_ino)==(b.stat().st_dev,b.stat().st_ino)
        assert sha(a)==sha(b)
        aliases.append({'suffix':suffix,'same_inode':True,'sha256':sha(a),'bytes':a.stat().st_size})
    accept('new_cache_aliases_are_single_copy',lambda:{'aliases':aliases,
           'bundle_exact':core.artifact_bundle(cached_object)==record['object_artifacts'],
           'kernel_or_builder_constructor_called':False})
    before = {str(p):sha(p) for p in (cached_object,cached_object.parent/'receipt.json')}
    refuse('completed_new_cache_key_overwrite',
           lambda:builder.cache_result('a'*64,record,fresh),(RuntimeError,))
    assert all(sha(p)==s for p,s in before.items())
    assert all(sha(p)==s for p,s in inputs.items())
    report={'status':'PASS_ALL_SAVED_BYTE_CONTROLS','controls':controls,'control_count':len(controls),
            'script_sha256':sha(__file__),'inputs':inputs,'inputs_unchanged':True,
            'compiler_native_or_subprocess_calls':0,'source_wrapper_only':True,
            'positive_capture':primary,'logging_qualification':'Saved existing separated native log exercises lossless encoding and parser, not a fresh combined-stderr compiler invocation.',
            'runtime_capture_process_or_builder_exercised':False,
            'inert_cache_result_method_exercised':True,'inert_artifacts_are_not_kernel_evidence':True}
    (args.output/'RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'controls':len(controls),'receipt':str(args.output/'RECEIPT.json')}))

if __name__=='__main__':
    main()
