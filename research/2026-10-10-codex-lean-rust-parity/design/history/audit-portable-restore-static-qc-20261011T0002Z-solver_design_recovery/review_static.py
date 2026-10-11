#!/usr/bin/env python3
"""Own AST/byte reader only; never imports or runs the proposed restorer."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
F = P/'rust/evidence/audit-portable-restore-source-freeze-1'
FREEZE_SHA = 'e63f775d7e5f36932ae4bda659fabe205fe7a72f46c70fd936a43b3dbb941193'
SOURCE_SHA = '39543d989895218cc91c088a36c747a2a287a32513d37cffb5d2f87ea62a5755'
DRIVER_SHA = '1c4aa22f7cb4fd3eed456aed7fbc41f4da4fd456afb15dd51b721d0a7c460b55'
CODEC_SHA = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'

def require(value, message):
    if not value:
        raise AssertionError(message)

def pin(path, digest, size=None):
    path = Path(path)
    actual = hashlib.sha256()
    length = 0
    with path.open('rb') as handle:
        while piece := handle.read(65536):
            actual.update(piece)
            length += len(piece)
    require(actual.hexdigest() == digest and (size is None or length == size), 'pin '+str(path))
    return {'path':str(path), 'bytes':length, 'sha256':digest}

def definition(tree, name, owner=None):
    nodes = tree.body
    if owner:
        nodes = next(n for n in nodes if isinstance(n,ast.ClassDef) and n.name == owner).body
    matches = [n for n in nodes if isinstance(n,ast.FunctionDef) and n.name == name]
    require(len(matches) == 1, 'unique definition '+str(owner)+'.'+name)
    return matches[0]

def ordered(body, pieces, label):
    offset = -1
    for piece in pieces:
        offset = body.find(piece, offset+1)
        require(offset >= 0, label+': '+piece)

def imports(tree):
    names = set()
    for n in ast.walk(tree):
        if isinstance(n,ast.Import):
            names.update(a.name for a in n.names)
        elif isinstance(n,ast.ImportFrom):
            names.add(n.module)
    return sorted(names)

def check():
    freeze_pin = pin(F/'SOURCE-FREEZE.json',FREEZE_SHA)
    freeze = json.loads((F/'SOURCE-FREEZE.json').read_text())
    require(freeze['status'] == 'SOURCE_STATIC_ONLY_TRIAL_PENDING' and
            not freeze['new_restore_or_driver_executed'] and
            freeze['raw_references_required_by_restorer'] == 0 and
            freeze['compiler_native_reference_processes'] == 0 and
            not freeze['mathematical_acceptance_claim'], 'source-only freeze scope')
    frozen = [pin(r['path'],r['sha256'],r['bytes']) for r in freeze['frozen_sources_and_plan']]
    current = [pin(r['path'],r['sha256'],r['bytes']) for r in freeze['current_sources']]
    require(len(frozen) == 5 and [r['sha256'] for r in current] == [SOURCE_SHA,DRIVER_SHA,CODEC_SHA], 'three frozen implementations')
    for name in ('audit_portable_restore.py','review_audit_portable_restore.py','audit_copy_literal_codec.py'):
        require((F/name).read_bytes() == (P/'rust'/name).read_bytes(), 'current/frozen byte equality '+name)
    unchanged_driver = pin(P/'rust/review_audit_copy_literal_codec.py',freeze['existing_edea_driver_sha256'])
    scenario = json.loads((F/'SCENARIO.json').read_text())
    require(scenario['required_raw_references_passed_to_standalone_restore'] == 0 and
            not scenario['existing_cdb_producer_or_restore_called'] and
            not scenario['old_edea_trial_reexecuted'] and
            not scenario['prospective_union_created'] and scenario['expected_large_raw_files_created'] == 0,
            'new fixed compressed-only scenario')
    require(scenario['address_space_cap_bytes'] == 268435456 and scenario['scratch_cap_bytes'] == 33554432 and
            scenario['outer_timeout_seconds'] == 90 and scenario['base_gzip_decompression_passes_per_restore'] == 1,
            'fixed outer caps and one-pass base')
    plan = scenario['plan']
    require(set(plan) == {'schema','base_gzip','base_identity','target_identity','scratch_root','limits'} and
            set(plan['base_identity']) == set(plan['target_identity']) == {'bytes','sha256'}, 'no required raw path in plan')
    inputs = [pin(r['path'],r['sha256'],r['bytes']) for r in
              [plan['base_gzip'], *scenario['driver_only_raw_comparison_references'], *scenario['existing_patch_origins']]]
    for r in scenario['source_pins']:
        pin(r['path'],r['sha256'],r['bytes'])
    source = (F/'audit_portable_restore.py').read_text()
    driver = (F/'review_audit_portable_restore.py').read_text()
    syntax, dtree = ast.parse(source), ast.parse(driver)
    allowed = {'__future__','argparse','contextlib','dataclasses','datetime','gzip','hashlib','json','pathlib','resource','sys','types'}
    require(set(imports(syntax)) <= allowed, 'restorer standard-library imports')
    require(set(imports(dtree)) <= (allowed|{'importlib.util','traceback'}), 'driver standard-library imports')
    body = lambda name,owner=None: ast.get_source_segment(source,definition(syntax,name,owner))
    codec_loader = body('pinned_codec')
    ordered(codec_loader,["source.read(CODEC_SOURCE_MAX_BYTES+1)", 'len(raw) > CODEC_SOURCE_MAX_BYTES',
                          'hashlib.sha256(raw).hexdigest() != CODEC_SHA256', "exec(compile(raw, str(CODEC_SOURCE), 'exec'), module.__dict__)",
                          '_CODEC = module'], 'bounded exact authenticated provider byte execution')
    exec_calls = [n for n in ast.walk(syntax) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id == 'exec']
    require(len(exec_calls) == 1 and exec_calls[0] in list(ast.walk(definition(syntax,'pinned_codec'))), 'one deliberate pinned provider exec')
    require(not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and
                    isinstance(n.func.value,ast.Name) and n.func.value.id == 'codec' and n.func.attr in {'produce','restore'}
                    for t in (syntax,dtree) for n in ast.walk(t)), 'no old codec producer or reference-required restore calls')
    require("return self.base_identity" in body('base_raw','PortablePlan') and
            "return self.target_identity" in body('target_raw','PortablePlan'), 'parser aliases expose pathless identities only')
    raw_fields = next(n for n in syntax.body if isinstance(n,ast.ClassDef) and n.name == 'RawIdentity')
    require([n.target.id for n in raw_fields.body if isinstance(n,ast.AnnAssign)] == ['bytes','sha256'], 'raw identity has no path field')
    ordered(body('optional_reference'),['if pin is None:', 'return None', "(pin.bytes, pin.sha256) == (identity.bytes, identity.sha256)",
                                       'return codec.authenticate_file(stack, pin)'], 'explicit optional reference only')
    restore = body('restore')
    ordered(restore,['plan.validate()', 'pin.validate(plan)', 'codec.reserve_scratch(plan, plan.target_identity.bytes)',
                     'codec.authenticate_file(stack, pin.gzip_file)', 'codec.authenticate_file(stack, plan.base_gzip)',
                     'codec.preflight_patch(patch_file, plan, pin)', 'optional_reference(codec, stack, compare_base_raw',
                     "output.open('xb')", 'codec.patch_operations(reader, plan, pin)', 'cursor.finish()', 'sink.finish()',
                     "'status': 'PASS_PINNED_PORTABLE_BYTE_RESTORATION'"], 'auth/whole patch preflight and final hashes before success')
    require('compare_base_raw=None, compare_target_raw=None' in restore and
            'aliases = [plan.base_gzip.path, pin.gzip_file.path]' in restore and
            "'required_raw_reference_files': 0" in restore, 'default interface compressed-only')
    ordered(body('read','PortableBaseCursor'),['self.position+length <= self.identity.bytes','self.compressed.read(length)',
                                            'if self.comparison is not None:', 'self.digest.update(piece)', 'self.position += length'], 'bounded base chunks hashed')
    ordered(body('finish','PortableBaseCursor'),['self.skip_to(self.identity.bytes)', "self.compressed.read(1) == b''",
                                              'self.digest.hexdigest() == self.identity.sha256'], 'full skipped/copied/tail base EOF and digest')
    ordered(body('consume','PortableTargetSink'),['self.position+len(piece) <= self.identity.bytes',
                                                'if self.comparison is not None:', 'self.output.write(piece)',
                                                'self.on_piece(piece)', 'self.digest.update(piece)'], 'bounded provisional target stream')
    ordered(body('finish','PortableTargetSink'),['self.position == self.identity.bytes',
                                               'self.digest.hexdigest() == self.identity.sha256'], 'complete target identity')
    ordered(body('main'),['codec.enforce_address_space_limit()', 'PortablePlan.decode', 'codec.PatchPin.decode',
                         'result = restore('], 'CLI cap before restoration')
    require('f.read(65537)' in body('read_small'), 'bounded plan/pin frames')
    run = ast.get_source_segment(driver,definition(dtree,'run'))
    ordered(run,['memory_limit = cap_address_space()', 'hashlib.sha256(raw_source).hexdigest() == SOURCE_SHA',
                 'stage.mkdir(exist_ok=False)', 'spec.loader.exec_module(portable)',
                 'standalone = portable.restore(plan,patch,on_piece=independent_observer)',
                 'compared = portable.restore(plan,patch,compare_base_raw=base_ref,compare_target_raw=target_ref)'], 'capped authenticated driver distinct default/optional modes')
    require('sys.dont_write_bytecode = True' in driver and 'target.read(len(piece)) == piece' in run and
            "standalone['required_raw_reference_files'] == 0" in run and 'digest.hexdigest() == TARGET_SHA' in run,
            'separate driver observer compares complete standalone output')
    case_names = [v.value for n in ast.walk(dtree) if isinstance(n,ast.Dict) for k,v in zip(n.keys,n.values)
                  if isinstance(k,ast.Constant) and k.value == 'name' and isinstance(v,ast.Constant)]
    require(case_names == scenario['expected_checks'] and len(case_names) == 9, 'exact nine-case frozen driver')
    refused = ast.get_source_segment(driver,definition(dtree,'pre_output_refusal'))
    require('pieces == 0 and not output.exists()' in refused, 'preflight controls require zero callbacks/no output')
    require("raw_patch[:offset]+bytes(32)+raw_patch[offset+32:]" in run and
            "raw_patch[:base_offset]+bytes(32)+raw_patch[base_offset+32:]" in run and
            "'TARGET_DECODED_HASH'" in run and "'BASE_GZIP_RAW_HASH'" in run and
            run.count('provisional_bytes == 6629112 and provisional_hash.hexdigest() == TARGET_SHA') == 2,
            'distinct authenticated final target/base identity controls preserve original stream')
    require('optional_output_bytes=6629111' in run and "hash_file(marker) == before and count == 0" in run,
            'output budget and no-overwrite controls')
    protocol = (F/'PROTOCOL.md').read_text()
    require('PROVISIONAL until the function returns successfully' in protocol and
            'No raw base/target file is required or opened by the default restorer' in protocol,
            'honest post-stream identity and noncircular interface documentation')
    return {'status':'PASS_SOURCE_ONLY_FIXED_EXISTING_1504_TO_168_PORTABLE_RESTORE_PLAN',
            'freeze':freeze_pin,'frozen_files':frozen,'current_sources':current,'unchanged_old_driver':unchanged_driver,
            'saved_input_and_fixture_pins':inputs,'source_ast_imports':imports(syntax),'driver_ast_imports':imports(dtree),
            'required_raw_reference_files':0,'expected_cases':case_names,'planned_argv':scenario['planned_argv'],
            'resource_caps':{'address_space_bytes':268435456,'scratch_bytes':33554432,'outer_timeout_seconds':90,
                             'base_chunk_bytes':65536,'default_patch_gzip_bytes':1048576,'optional_output_bytes':16777216},
            'checked_properties':['one bounded authenticated cdb parser/provider source execution; old produce/restore unused',
                'required compressed base and patch plus pathless base/target identities; explicit optional comparison mode',
                'complete compressed identities and raw patch header/range/count/hash preflight before callbacks/output',
                'monotone one-pass base gzip, hashing all skipped/copied/tail bytes and decoded EOF',
                'bounded target stream hashing; final base and target digests before success',
                'new exclusive optional output, input-alias refusal and storage precharge',
                'nine concrete controls, default restorer receives no raw reference; independent observer is outside restorer'],
            'qualifications':['Static source QC only; no driver, restorer, codec module, decompression or restore was executed by this reader.',
                'Callback chunks and partial create-new output are provisional until final raw base/target identity success; final refusals deliberately occur after streaming.',
                'The default restorer itself needs no raw reference. The fixed validation driver separately holds originals for independent observation and explicit optional-comparison case.',
                'CLI/driver enforce the address-space cap; direct library calls require an approved capped worker.',
                'Actual nine outcomes and resource use remain pending root approval and one execution by Rust.',
                'This is exact byte restoration of already accepted saved artifacts, with no theorem checking, new audit, future union, generic parser acceptance or future capacity claim.']}

def main():
    result = {'schema':'audit_portable_restore_independent_static_design_qc_v1','contributor':'Codex / solver_design_recovery',
              'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'target_modules_imported':False,'producer_compiler_adapter_native_reference_processes_started':0,
              'byte_codec_or_restore_processes_started':0,'new_target_artifact_created':False,'mathematical_acceptance_modified':False}
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
