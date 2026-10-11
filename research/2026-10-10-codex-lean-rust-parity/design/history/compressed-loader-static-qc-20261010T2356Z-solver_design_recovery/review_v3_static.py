#!/usr/bin/env python3
"""Independent text/AST and saved-pin reader; no target module is imported."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
B = P/'lean/proposals/compressed-loader-storage-20261010T235105.986329Z'
V = B/'v3-partial-failure'
SOURCE_SHA = 'd774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810'
DRIVER_SHA = 'f425ce06219db0245b6e5c936f501022552c74b6e584843749b06d300cc92de7'
PLAN_SHA = '55a4698de5b4a8723cf4e629da93535af1dd4da69de517a4babc4cfce0a84310'
CORE_SHA = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
FINDING = Path(__file__).with_name('NATIVE-LOADER-PRESENCE-STATIC-FINDING.json')

def require(value, description):
    if not value:
        raise AssertionError(description)

def pin(path, expected):
    path = Path(path)
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == expected, 'pin '+str(path))
    return {'path':str(path),'bytes':len(raw),'sha256':expected}

def ordered(body, parts, label):
    offset = -1
    for part in parts:
        offset = body.find(part, offset+1)
        require(offset >= 0, label+': '+part)

def definition(tree, name, owner=None):
    scope = tree if owner is None else next(n for n in ast.walk(tree) if isinstance(n,ast.ClassDef) and n.name == owner)
    matches = [n for n in scope.body if isinstance(n,ast.FunctionDef) and n.name == name]
    require(len(matches) == 1, 'unique function '+str(owner)+'.'+name)
    return matches[0]

def assignment(node, name):
    found = [n.value for n in ast.walk(node) if isinstance(n,ast.Assign) and
             any(isinstance(t,ast.Name) and t.id == name for t in n.targets)]
    require(len(found) == 1, 'unique assignment '+name)
    return found[0]

def c3_merge(sequences):
    sequences = [list(s) for s in sequences if s]
    result = []
    while sequences:
        candidate = next((s[0] for s in sequences if not any(s[0] in r[1:] for r in sequences)),None)
        require(candidate is not None, 'consistent static C3 composition')
        result.append(candidate)
        for s in sequences:
            if s and s[0] == candidate:
                s.pop(0)
        sequences = [s for s in sequences if s]
    return result

def check():
    pins = [pin(V/'storage_wrapper.py',SOURCE_SHA),pin(V/'review_saved_loader.py',DRIVER_SHA),pin(V/'SOURCE-ONLY-PLAN.json',PLAN_SHA)]
    plan = json.loads((V/'SOURCE-ONLY-PLAN.json').read_text())
    require(plan['status'] == 'SOURCE_ONLY_PENDING_DESIGN_QC_AND_SAVED_BYTE_TRIAL_APPROVAL' and
            not plan['runtime_authorized'] and plan['byte_trial_plan']['control_count'] == 15, 'unexecuted source-only 15-control scope')
    require(plan['raw_limit_bytes'] == 33554432 and plan['gzip_limit_bytes'] == 1048576 and
            plan['byte_trial_plan']['memory_as_bytes'] == 268435456 and
            plan['byte_trial_plan']['scratch_bytes'] == 33554432 and plan['byte_trial_plan']['timeout_seconds'] == 90,
            'unchanged raw/gzip and approved proposed outer byte caps')
    parent_pins = [pin(path,digest) for path,digest in plan['intended_parent_context'].items()]
    prior_plan = plan['supersedes']
    old_pins = [pin(prior_plan['plan'],prior_plan['sha256']),
                pin(B/'v2-native-presence/storage_wrapper.py',prior_plan['old_wrapper_sha256']),
                pin(B/'v2-native-presence/review_saved_loader.py',prior_plan['old_driver_sha256']),
                pin(B/'storage_wrapper.py','ac6033fb98e9d13d2910d0c95d0015540a3aa0472b25963a7b2dc27fe2bed751'),
                pin(B/'review_saved_loader.py','dffb183f7047dc5850256062805793ec7f5bde76eb8a7918f4587ae759c592f3'),
                pin(B/'SOURCE-ONLY-PLAN.json','1272de869b692695dfd31cfd057035ae8268b0a31a2cf0a9c6edbc128c76ae0e')]
    finding_pin = pin(FINDING,'4043803e493819946dd7bfbf705013447d0763a02396edd197be29e23db2a541')
    source,driver = (V/'storage_wrapper.py').read_text(),(V/'review_saved_loader.py').read_text()
    tree,dtree = ast.parse(source),ast.parse(driver)
    body = lambda name,owner=None: ast.get_source_segment(source,definition(tree,name,owner))
    core_path = next(Path(r['path']) for r in parent_pins if Path(r['path']).name == 'build_connected.py')
    core_source,ctree = core_path.read_text(),ast.parse(core_path.read_text())
    pin(P/'lean/scripts/build_connected.py',CORE_SHA)
    invocation,canonical = definition(tree,'invoke','StorageInvocation'),definition(ctree,'invoke','Builder')
    require(ast.dump(assignment(invocation,'cmd'),include_attributes=False) ==
            ast.dump(assignment(canonical,'cmd'),include_attributes=False), 'exact compiler argv flags/memory expression')
    require(ast.dump(assignment(invocation,'native_stable'),include_attributes=False) ==
            ast.dump(assignment(canonical,'native_stable'),include_attributes=False), 'exact native stat identity predicate')
    helper = body('native_evidence_known')
    require("captured['complete'] and not captured['truncated']" in helper and
            'bool(native_used) and all(p in native_runtime for p in native_used)' in helper, 'empty native evidence repaired by exact shared helper')
    require(ast.unparse(assignment(invocation,'native_known')) == 'native_evidence_known(captured, native_used, self.native_runtime)',
            'live invoke uses reviewed presence helper')
    invoke = body('invoke','StorageInvocation')
    ordered(invoke,["if not policy.get('runtime_authorized', False)", 'before = self.dependencies(context, imports)',
                    "LD_DEBUG='libs'", "env.pop('LD_DEBUG_OUTPUT', None)", 'capture_process(cmd, work, env, out,',
                    'after = self.dependencies(context, imports)', 'native_known = native_evidence_known(',
                    "before == after and core.sha(source) == core.sha(frozen) and native_stable and native_known",
                    "code == 0 and captured['reason'] is None and stable and 'sorryAx' not in log"], 'strict invocation checks and reason-free pass')
    factory = body('make_builder_class')
    require('file_sha(core.__file__) != CORE_SHA256' in factory and
            'class StorageBuilder(parent, StorageInvocation)' in factory, 'pinned explicit storage composition')
    mro = ['StorageBuilder']+c3_merge([
        ['AuthenticatedOverlayBuilder','NamespaceOverlayBuilder','CoreBuilder','object'],
        ['StorageInvocation','CoreBuilder','object'],['AuthenticatedOverlayBuilder','StorageInvocation']])
    require(mro == ['StorageBuilder','AuthenticatedOverlayBuilder','NamespaceOverlayBuilder','StorageInvocation','CoreBuilder','object'],
            'storage invoke remains beneath inherited inventory guard and above identical core')
    auth_path = next(Path(r['path']) for r in parent_pins if Path(r['path']).name == 'build_with_authenticated_overlay.py')
    auth_source,atree = auth_path.read_text(),ast.parse(auth_path.read_text())
    ordered(ast.get_source_segment(auth_source,definition(atree,'invoke','OverlayBuilder')),
            ['self.authenticate_inventory(context)','super().invoke(', 'self.authenticate_inventory(context)','return result'], 'parent inventory checks retained around storage invoke')
    require("same-FS" in plan['fresh_objects'] and 'core=authenticated.original.core' in plan['parent_composition'],
            'intended exact core object binding, not duplicate imported classes')
    ordered(body('write','LimitedEncodedWriter'),['self.count + len(data) > self.limit', 'self.out.write(data)', 'written != len(data)'], 'encoded bounds before physical writes')
    ordered(body('inspect_capture'),['path.stat().st_size > gzip_limit','encoded_before = file_sha(path)',
                "gzip.open(path, 'rb')", 'count + len(data) > raw_limit', 'count != expected_raw_bytes or h.hexdigest() != expected_raw_sha256',
                "b''.join(chunks).decode('utf-8', errors='replace')", 'file_sha(path) != encoded_before',
                "re.findall(r'calling init:\\s*(/[^\\s]+)', text)"], 'complete lossless EOF/raw digest and encoded identity before native interpretation')
    partial = body('preserve_partial_failure')
    for fragment in ["'status':'FAILED_PARTIAL_CAPTURE_NOT_VERIFIED'", "'complete':False", "'truncated':True", "'eof':False",
                     "'gzip_integrity_verified':False", 'preserved_gzip_prefix_sha256=file_sha(destination)', "sidecar.open('x')", 'error.add_note']:
        require(fragment in partial, 'qualified exclusive best-effort failure sidecar '+fragment)
    for function in ('capture_saved_file','capture_process'):
        require('preserve_partial_failure(' in body(function) and 'except BaseException' in body(function), 'capture exception sidecar '+function)
    process = body('capture_process')
    require('subprocess.Popen(command, cwd=cwd, env=env,' in process and 'stderr=subprocess.PIPE' in process and
            'selector.select(0.05)' in process and 'os.read(key.fd, READ_BYTES)' in process and
            'proc.wait()' in process and 'selector.close()' in process and 'raise' in process,
            'one selector reader, local leader kill/reap/close and exception rethrow')
    require(not any(isinstance(n,ast.keyword) and n.arg in {'start_new_session','preexec_fn'} for n in ast.walk(tree)), 'no new session/global process hook')
    cache = body('cache_result','StorageInvocation')
    ordered(cache,["is_relative_to((self.run/'attempts').resolve())", 'return super().cache_result(key, rec, obj)',
                   'os.link(source, folder/', "core.artifact_bundle(folder/'artifact.olean') == rec['object_artifacts']",
                   "(destination/'receipt.json').exists()", "Completed cache key already exists; refusing overwrite", 'folder.rename(destination)'],
            'old candidates unchanged, only new attempt aliases, exact bundle and overwrite refusal')
    require('shutil.copy' not in cache, 'no silent fresh EXDEV copy fallback')
    dmain = ast.get_source_segment(driver,definition(dtree,'main'))
    ordered(dmain,['all(sha(p)==s for p,s in inputs.items())','spec.loader.exec_module(module)',
                   "module.capture_saved_file(SAVED_RAW, primary_path)", 'core_spec.loader.exec_module(core)',
                   'builder = object.__new__(storage)', "builder.cache_result('a'*64,record,fresh)"], 'pinned byte-only target import and inert constructor-free cache call')
    require(not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in {'capture_process','invoke','Popen','run','Builder'}
                    for n in ast.walk(dtree)), 'trial invokes no process/compiler/live capture/Builder constructor')
    require('INERT BYTES: not a checked Lean object' in driver and 'INERT_STORAGE_CONTROL_ONLY' in driver and
            'sys.dont_write_bytecode = True' in driver, 'inert storage bytes, no checked-object/bytecode claim')
    for fragment in ['empty_native_evidence','diagnostic_without_native_init', 'module.native_evidence_known(',
                     "sidecar['preserved_gzip_prefix_sha256']==sha(prefix)", "not sidecar['gzip_integrity_verified']",
                     "(a.stat().st_dev,a.stat().st_ino)==(b.stat().st_dev,b.stat().st_ino)", 'all(sha(p)==s for p,s in before.items())']:
        require(fragment in driver, 'reviewed control '+fragment)
    names = [n.args[0].value for n in ast.walk(dtree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and
             n.func.id in {'accept','refuse'} and n.args and isinstance(n.args[0],ast.Constant)]
    require(len(names) == 13, '13 literal controls plus two looped presence controls')
    controls = ['saved_raw_lossless_capture','native_init_parser_exact_original_receipt','sorryAx_crosses_read_boundary',
                'unbound_native_library_fails_original_known_predicate','empty_native_evidence_refused_by_invoke_helper',
                'diagnostic_without_native_init_refused_by_invoke_helper','forged_raw_digest','forged_raw_count','gzip_trailer_eof_required',
                'decoded_byte_limit','encoded_byte_limit','failed_cap_captures_preserve_explicit_partial_identities',
                'refuse_destination_overwrite','new_cache_aliases_are_single_copy','completed_new_cache_key_overwrite']
    require(set(names) == set(controls)-{controls[4],controls[5]}, 'exact planned literal control set')
    raw_path = Path('/dev/shm/rc-lean-g6-parallel-arm-transport-20261010T231844.690779Z/.build/runs/20261010T232230.265801Z/attempts/00001-G6OriginalParallelArmTransport/NATIVE-LOADER.259880')
    saved = [pin(raw_path,'830f7c33aed836755cbe788f5f69343fa15b575c3267305c8ff249708de861f8'),
             pin(raw_path.parent/'receipt.json','13f45e94ddd8e3e3721ac45600a7f4ab07dae5d976d9ea85de8e1fecd4102059')]
    return {'status':'PASS_V3_SOURCE_ONLY_AND_PROPOSED_15_SAVED_BYTE_CONTROLS',
            'sources_and_plan':pins,'parent_context_pins':parent_pins,'preserved_predecessor_pins':old_pins,
            'resolved_previous_static_finding':finding_pin,'saved_log_and_actual_receipt':saved,
            'static_mro_if_exact_intended_core_object':mro,'expected_controls':controls,'expected_control_count':15,
            'runtime_authorized':False,'proposed_byte_trial_argv':plan['byte_trial_plan']['command_argv'],
            'resource_caps':{'raw_capture_bytes':33554432,'encoded_capture_bytes':1048576,'chunk_bytes':65536,
                             'proposed_outer_address_space_bytes':268435456,'proposed_outer_scratch_bytes':33554432,'proposed_outer_timeout_seconds':90},
            'checked_properties':['exact canonical compiler flags, memory/timeout parameters, source/import/native stat predicates and sorryAx refusal',
                'same inherited authenticated namespace/import/target guards conditional on exact core object identity',
                'shared complete/untruncated and nonempty all-pinned native-initialization helper closes v1 empty-evidence finding',
                'bounded complete gzip/raw byte identity and EOF before interpreting full decoded text',
                'exception sidecars explicitly FAILED_PARTIAL/incomplete/unverified; encoded prefix pinned, original error rethrown after leader cleanup',
                'fresh same-filesystem hardlink aliases only, unchanged prior-candidate method and completed-key overwrite refusal',
                '15 byte-only saved-log/parser/presence/failure-sidecar/inert alias controls'],
            'qualifications':['No source module, Builder, byte capture, subprocess, compiler or trial was executed by this reviewer.',
                'The factory MRO conclusion requires the exact core object authenticated.original.core and intended frozen 5406/3d613 context. A separately imported duplicate core class is outside this gate; the later runtime facade must bind the intended objects.',
                'The byte driver does not enforce address/scratch/timeout caps itself. Root must freeze a concrete outer capped worker and create-new scratch path before the trial.',
                'The planned trial checks existing separated loader bytes plus inert storage artifacts; it cannot establish live combined-stderr capture, fresh compilation, kernel or aggregate/audit acceptance.',
                'Partial failure sidecars are best effort under storage exhaustion; preserved prefixes never establish a complete raw/native identity.',
                'Future actual Lean invocation requires this byte trial, a reviewed concrete source/resource plan and root authorization. No prospective coherent union or source count is accepted here.']}

def main():
    result = {'schema':'compressed_loader_v3_independent_static_design_qc_v1','contributor':'Codex / solver_design_recovery',
              'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'target_modules_imported':False,'producer_compiler_native_adapter_reference_processes_started':0,
              'byte_capture_or_storage_trial_started':False,'mathematical_acceptance_modified':False}
    try:
        result.update(check())
    except Exception as error:
        result.update(status='FAIL_STATIC_QC',error_type=type(error).__name__,error=str(error))
    destination = Path(sys.argv[1])
    with destination.open('x') as handle:
        json.dump(result,handle,sort_keys=True,indent=2)
        handle.write('\n')
    print(json.dumps({'path':str(destination),'sha256':hashlib.sha256(destination.read_bytes()).hexdigest(),'status':result['status']}))

if __name__ == '__main__':
    main()
