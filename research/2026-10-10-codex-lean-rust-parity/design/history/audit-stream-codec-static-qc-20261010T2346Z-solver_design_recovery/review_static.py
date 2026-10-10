#!/usr/bin/env python3
"""Inspect frozen codec/driver text and saved pins; never import or run them."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
FREEZE = ROOT/'rust/evidence/audit-stream-codec-source-freeze-1'
FREEZE_SHA = '50d3940f17e58698fd99b3e00fa89ce44514bd71367f965c09ba6fde274b723c'
SOURCE_SHA = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'
DRIVER_SHA = 'edea7f912a357c2f64785ead9a15a481fad6993f668b36a3c33200407776eea4'
ORDER_QC = ROOT/'design/history/audit-byte-delta-static-qc-20261010T2340Z-solver_design_recovery/SAVED-COPY-ORDER-RECONCILIATION-ATTEMPT1.json'
ORDER_SHA = 'fcfae0bcaba8fa61cb5703401db56842bdc45a6a3aac0507f7459c531adbcc58'

def demand(condition, explanation):
    if not condition:
        raise AssertionError(explanation)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def pin(path, expected, size=None):
    path = Path(path)
    digest = hashlib.sha256()
    length = 0
    with path.open('rb') as handle:
        while piece := handle.read(65536):
            digest.update(piece)
            length += len(piece)
    demand(digest.hexdigest() == expected, 'SHA256 '+str(path))
    demand(size is None or length == size, 'size '+str(path))
    return {'path':str(path),'bytes':length,'sha256':expected}

def imports(tree):
    result = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            result.update(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            result.add(node.module)
    return sorted(result)

def definition(tree, name, owner=None):
    nodes = tree.body
    if owner is not None:
        matches = [n for n in nodes if isinstance(n, ast.ClassDef) and n.name == owner]
        demand(len(matches) == 1, 'unique class '+owner)
        nodes = matches[0].body
    matches = [n for n in nodes if isinstance(n, ast.FunctionDef) and n.name == name]
    demand(len(matches) == 1, 'unique function '+str(owner)+'.'+name)
    return matches[0]

def text_of(raw, node):
    return ast.get_source_segment(raw, node)

def ordered(body, fragments, description):
    cursor = -1
    for fragment in fragments:
        cursor = body.find(fragment, cursor+1)
        demand(cursor >= 0, description+': '+fragment)

def literal_constants(tree):
    result = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            try:
                result[node.targets[0].id] = ast.literal_eval(node.value)
            except (ValueError, TypeError):
                pass
    return result

def integer_expression(node, names):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.Name) and node.id in names:
        return names[node.id]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return integer_expression(node.left, names)*integer_expression(node.right, names)
    raise AssertionError('nonliteral integer limit')

def check():
    freeze_pin = pin(FREEZE/'SOURCE-FREEZE.json',FREEZE_SHA)
    freeze = json.loads((FREEZE/'SOURCE-FREEZE.json').read_text())
    demand(freeze['status'] == 'FROZEN_SOURCE_STATIC_REVIEW_PENDING' and not freeze['fresh_restoration_executed']
           and not freeze['mathematical_acceptance_claim'] and not freeze['prospective_union_created'], 'source-only freeze scope')
    frozen_pins = [pin(FREEZE/row['relative_path'],row['sha256'],row['bytes']) for row in freeze['files']]
    demand(len(frozen_pins) == 4, 'four frozen files')
    current_pins = [pin(row['path'],row['sha256'],row['bytes'])
                    for row in (freeze['current_codec'],freeze['current_driver'])]
    demand(current_pins[0]['sha256'] == SOURCE_SHA and current_pins[1]['sha256'] == DRIVER_SHA, 'exact current source/driver versions')
    for name, current in zip(('audit_copy_literal_codec.py','review_audit_copy_literal_codec.py'),current_pins):
        demand((FREEZE/name).read_bytes() == Path(current['path']).read_bytes(), 'frozen/current exact bytes '+name)
    correction_pin = pin(freeze['correction']['path'],freeze['correction']['sha256'])
    order_pin = pin(ORDER_QC,ORDER_SHA)
    demand(freeze['encoded_copy_order_independent_receipt_sha256'] == ORDER_SHA, 'prior independently verified encoded order')
    prototype_pin = pin(ROOT/'rust/evidence/audit-byte-delta-feasibility-1/probe.py',
                        '08f6c11cd2c7a211aa207785ab4097a2737190792decef94422713449305deef')
    scenario = json.loads((FREEZE/'SCENARIO.json').read_text())
    demand(scenario['phase'] == 'SOURCE_STATIC_ONLY_EXECUTION_PENDING_ROOT_APPROVAL', 'execution still pending')
    source = (FREEZE/'audit_copy_literal_codec.py').read_text()
    driver = (FREEZE/'review_audit_copy_literal_codec.py').read_text()
    syntax, driver_syntax = ast.parse(source), ast.parse(driver)
    source_imports, driver_imports = imports(syntax), imports(driver_syntax)
    demand(set(source_imports) <= {'__future__','argparse','contextlib','dataclasses','datetime','gzip','hashlib','json',
                                  'mmap','pathlib','re','resource','struct'}, 'codec standard-library imports')
    demand(set(driver_imports) <= {'argparse','dataclasses','datetime','gzip','hashlib','importlib.util','json',
                                  'pathlib','resource','struct','sys','traceback'}, 'driver standard-library imports')
    demand(not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id in
                   {'eval','exec','compile','__import__'} for t in (syntax,driver_syntax) for n in ast.walk(t)), 'no evaluator/compiler calls')
    constants = literal_constants(syntax)
    driver_constants = literal_constants(driver_syntax)
    demand(constants['MAGIC'] == b'RC-AUDIT-COPY-LITERAL-V1\x00' and len(constants['MAGIC']) == 25, '25-byte format magic')
    demand(constants['RECORD_FIELDS'] == {'type_references','name','module','kind','body_references','axioms'}, 'exact record field set')
    demand(constants['TOP_FIELDS'] == ('theorem_declaration_count','selected_modules','owned_axioms',
                                     'nonstandard_axiom_rows','missing_modules','declarations','declaration_count',
                                     'all_imported_module_names'), 'pinned serializer top-field order')
    integer_names = {}
    for n in syntax.body:
        if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in {'CHUNK','MAX_ADDRESS_SPACE','MAX_SCRATCH'}:
            integer_names[n.targets[0].id] = integer_expression(n.value,integer_names)
    demand(integer_names == {'CHUNK':65536,'MAX_ADDRESS_SPACE':268435456,'MAX_SCRATCH':33554432}, 'transfer/address/scratch limits')
    limit_class = next(n for n in syntax.body if isinstance(n,ast.ClassDef) and n.name == 'Limits')
    limits = {n.target.id:integer_expression(n.value,integer_names) for n in limit_class.body if isinstance(n,ast.AnnAssign)}
    demand(limits == scenario['plan']['limits'], 'scenario/default exact limits')
    input_pins = [pin(item['path'],item['sha256'],item['bytes'])
                  for item in (scenario['plan']['base_raw'],scenario['plan']['base_gzip'],scenario['plan']['target_raw'])]
    for name, source_name, digest_name, expected_bytes in (
        ('base_raw','BASE_RAW','BASE_SHA',114300292),('base_gzip','BASE_GZIP','BASE_GZIP_SHA',7868154),
        ('target_raw','TARGET_RAW','TARGET_SHA',6629112)):
        item = scenario['plan'][name]
        demand(item['path'] == driver_constants[source_name] and item['sha256'] == driver_constants[digest_name]
               and item['bytes'] == expected_bytes, 'driver/scenario actual saved input '+name)
    demand(driver_constants['SOURCE_SHA'] == SOURCE_SHA and driver_constants['LEGACY_PATCH_SHA'] ==
           '050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f', 'driver codec/legacy raw patch pins')
    demand(scenario['planned_argv'] == ['python3',str(ROOT/'rust/review_audit_copy_literal_codec.py'),'--output',
                                     '/dev/shm/rc-audit-stream-codec-family168-trial-1'], 'exact proposed argv')
    demand(scenario['plan']['scratch_root'] == scenario['planned_argv'][-1], 'exact proposed scratch root')
    demand(not Path(scenario['plan']['scratch_root']).exists(), 'trial output directory remains create-new')
    demand(scenario['address_space_cap_bytes'] == 268435456 and scenario['current_scratch_cap_bytes'] == 33554432,
           'trial hard resource caps')
    demand(scenario['expected_producer'] == {'backward_exact_records_literal':0,'base_records':100985,'changed_records':19,
           'copies':4879,'exact_copied_records':4879,'literals':4880,'new_records':9,'operations':9759,
           'raw_patch_bytes':388853,'raw_patch_sha256':driver_constants['LEGACY_PATCH_SHA'],'target_records':4907}, 'fixed producer expectations')
    body = lambda name, owner=None: text_of(source,definition(syntax,name,owner))
    ordered(body('produce'),['authenticate_file(stack, plan.base_raw)','authenticate_file(stack, plan.base_gzip)',
            'authenticate_file(stack, plan.target_raw)','verify_base_gzip','base_index','output_gzip.open(\'xb\')',
            'target_spans','original[2] == hashlib.sha256(piece).digest()',
            'base[original[0]:original[1]] == piece','original[0] >= builder.source_cursor','builder.copy_piece'], 'producer pin/reuse order')
    demand('counts[\'backward_exact_records_literal\'] += 1' in body('produce'), 'backward exact candidates literalized')
    maps = [n for n in ast.walk(syntax) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
            and isinstance(n.func.value,ast.Name) and n.func.value.id=='mmap' and n.func.attr=='mmap']
    demand(len(maps)==1 and ast.unparse(maps[0].args[0])=='raw_base.fileno()', 'only preserved raw base mapped')
    ordered(body('target_spans'),['handle.readline(limits.line_bytes+1)','len(line) <= limits.line_bytes',
            'scanner.end(piece)','len(buffer)+len(part) <= limits.record_bytes','buffer.extend(part)',"yield 'R', bytes(buffer)"], 'target scanner bounds')
    ordered(body('copy_piece','Builder'),['start >= self.source_cursor','start+length <= self.plan.base_raw.bytes',
            'self.decoded_position+length <= self.plan.target_raw.bytes','self.decoded_position += length',
            'self.source_cursor = start+length'], 'encoder copy bounds and monotonicity')
    ordered(body('patch_operations'),['start >= source_cursor','start+length <= plan.base_raw.bytes',
            'position+length <= plan.target_raw.bytes',"yield 'C'"], 'decoder copy checks before emit')
    literal_branch = body('patch_operations').split("elif tag == b'L':",1)[1]
    ordered(literal_branch,['length > 0 and position+length <= plan.target_raw.bytes','reader.position+length <= pin.raw_bytes',
            'literals <= pin.literals','reader.exact(min(CHUNK, remaining))',"yield 'L', piece"], 'decoder literal checks before payload/emit')
    ordered(body('restore'),['authenticate_file(stack, pin.gzip_file)','preflight_patch(patch_file, plan, pin)',
            'authenticate_file(stack, plan.base_raw)','authenticate_file(stack, plan.base_gzip)',
            'authenticate_file(stack, plan.target_raw)',"output.open('xb')",'patch_operations(reader, plan, pin)',
            'sink.finish()','base_cursor.finish()'], 'complete patch/input preflight before optional output')
    ordered(body('consume','TargetSink'),['self.position+len(piece) <= self.pin.bytes','self.reference.read(len(piece)) == piece',
            'self.output.write(piece)','self.on_piece(piece)','self.digest.update(piece)'], 'target reference comparison before output/callback')
    ordered(body('read','BaseCursor'),['self.position+length <= self.pin.bytes','self.compressed.read(length)',
            'self.raw.read(length) == piece','self.digest.update(piece)','return piece'], 'base comparison before target copy')
    ordered(body('finish','BaseCursor'),['self.skip_to(self.pin.bytes)','self.compressed.read(1)',
            'self.raw.read(1)','self.digest.hexdigest() == self.pin.sha256'], 'full uncopied base tail and SHA')
    ordered(body('finish','RawPatchReader'),['self.position == self.pin.raw_bytes','self.stream.read(1)',
            'self.digest.hexdigest() == self.pin.raw_sha256'], 'full raw patch length/SHA/trailing bytes')
    ordered(body('finish','TargetSink'),['self.position == self.pin.bytes','self.reference.read(1)',
            'self.digest.hexdigest() == self.pin.sha256'], 'full target length/SHA')
    run_body = text_of(driver,definition(driver_syntax,'run'))
    ordered(run_body,['hashlib.sha256(raw_source).hexdigest() == SOURCE_SHA','stage.mkdir(exist_ok=False)',
            'spec.loader.exec_module(codec)','codec.enforce_address_space_limit()',
            'codec.produce(','patch.raw_bytes, patch.raw_sha256, patch.operations, patch.copies, patch.literals',
            'codec.restore(plan, patch, on_piece=observe)'], 'driver source pin and enforced cap before byte operations')
    demand('sys.dont_write_bytecode = True' in driver, 'no imported bytecode artifact')
    names=[]
    for n in ast.walk(driver_syntax):
        if isinstance(n,ast.Dict):
            for k,v in zip(n.keys,n.values):
                if isinstance(k,ast.Constant) and k.value=='name' and isinstance(v,ast.Constant):
                    names.append(v.value)
    expected_names=['stream-producer-exact-legacy-patch','restore-to-hash-and-byte-comparison','optional-exclusive-output',
                    'no-overwrite','bad-compressed-hash-before-output','bad-raw-hash-before-output',
                    'oversized-literal-before-output','optional-output-size-before-output']
    demand(names == expected_names and len(scenario['expected_trial_checks'])==8, 'exact eight-case driver')
    refuse_body=text_of(driver,definition(driver_syntax,'expected_refusal'))
    demand('pieces == 0' in refuse_body and 'not output.exists()' in refuse_body, 'refusals require no target callback or output')
    demand("6629113" in run_body and "'TARGET_RANGE'" in run_body and "raw_sha256='0'*64" in run_body
           and "sha256='0'*64" in run_body and 'optional_output_bytes=6629111' in run_body, 'focused malformed/hash/output control values')
    protocol=(FREEZE/'PROTOCOL.md').read_text()
    demand('gzip-only portable replay without an existing pinned raw base/target is outside this interface' in protocol,
           'honest saved reference dependency')
    return {'status':'PASS_FROZEN_SOURCE_AND_EXACT_EIGHT_CASE_BYTE_PLAN; execution pending root approval',
            'source_freeze':freeze_pin,'frozen_files':frozen_pins,'current_source_and_driver':current_pins,
            'correction':correction_pin,'independent_copy_order_qc':order_pin,'unchanged_prior_prototype':prototype_pin,
            'saved_input_pins':input_pins,'source_ast_imports':source_imports,'driver_ast_imports':driver_imports,
            'wire_format':{'magic_bytes':25,'header_bytes':97,'copy_frame_bytes':17,'literal_frame_bytes':9,
                           'target_order':'encoded C/L operation order','source_copies':'monotone and nonoverlapping'},
            'trial_argv':scenario['planned_argv'],'expected_cases':expected_names,'expected_producer':scenario['expected_producer'],
            'resource_caps':{'address_space_bytes':268435456,'scratch_bytes':33554432,'gzip_output_bytes':1048576,
                             'transfer_chunk_bytes':65536,'literal_buffer_bytes':1048576,'line_bytes':1048576,
                             'record_bytes':2097152,'optional_saved_target_output_bytes':6629112},
            'checked_source_properties':['all known raw/gzip source identities authenticated before patch creation',
                'same record candidates require raw digest plus direct raw-byte equality; backward matches remain literal',
                'one base mmap/index and bounded target scanning; all serializer/context differences retained literally',
                'complete authenticated raw patch/header/op/range/count preflight before optional output/callback',
                'C/L position checks before payload/output; exact operation counts come from separately preserved patch pin',
                'target-order restoration from one portable-base-gzip pass with per-chunk authenticated raw reference comparison',
                'target byte comparison before callback/output; full target hash and uncopied base-tail hash before successful return',
                'exclusive create-new outputs and explicit scratch/optional-output precharges'],
            'qualifications':['This is source-only QC. Eight trial outcomes and actual resource use are not yet observed.',
                'Restoration requires the preserved raw base and actual raw target as authenticated comparison references. It is not a gzip-only replay API without those originals.',
                'Decoder/producer share configurable hard ceilings, while the concrete restoration pin fixes exact raw388853 bytes/9759 operations/4879 copies/4880 literals/6629112 target bytes.',
                'Full decoded base EOF/hash is finalized after target streaming. Each copied base chunk and each target chunk is compared before output; failures preserve partial attempt files.',
                'Address-space enforcement is performed by the frozen CLI/driver. Direct library calls require the approved capped worker context.',
                'Pinned serializer recognition is a byte reuse mechanism, not an arbitrary untrusted audit parser, mathematical checker, prospective audit, or future compression/capacity theorem.',
                'A future actual union needs independently produced/pinned inputs and a separately approved exact plan and output/storage budget.']}

def main():
    destination=Path(sys.argv[1])
    report={'schema':'audit_stream_codec_independent_static_design_qc_v1','contributor':'Codex / solver_design_recovery',
            'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
            'new_codec_or_restore_processes_started':0,'target_compiler_evaluator_native_reference_processes_started':0,
            'target_modules_imported':False,'restored_target_materialized':False,'mathematical_acceptance_modified':False}
    try:
        report.update(check())
    except Exception as error:
        report.update(status='FAIL_SOURCE_STATIC_QC',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,indent=2,sort_keys=True)
        handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':sha(destination.read_bytes())}))
    return 1 if report['status'].startswith('FAIL') else 0

if __name__=='__main__':
    raise SystemExit(main())
