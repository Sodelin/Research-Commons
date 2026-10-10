#!/usr/bin/env python3
"""Inspect a fixed saved copy/literal patch; never run producer or restore."""
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import json
import mmap
from pathlib import Path
import struct
import sys

PACKET = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
EVIDENCE = PACKET/'rust/evidence/audit-byte-delta-feasibility-1'
MAGIC = b'RC-AUDIT-COPY-LITERAL-V1\x00'
U64 = struct.Struct('<Q')
PUBLICATION_SHA = 'c51e2e7743e9b8582e6984fec1b24ca6f1e524f43c1927ccbe2850755192abcb'
SOURCE_SHA = '08f6c11cd2c7a211aa207785ab4097a2737190792decef94422713449305deef'
RECEIPT_SHA = '53613aec37dfda2f128f59ffc6469a7b0113139d254e8f762123e6a843139a5f'

def demand(condition, reason):
    if not condition:
        raise AssertionError(reason)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def hash_file(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as handle:
        while block := handle.read(1024*1024):
            h.update(block)
    return h.hexdigest()

def pin(path, expected=None, size=None):
    path = Path(path)
    digest = hash_file(path)
    if expected is not None:
        demand(digest == expected, 'byte digest '+str(path))
    if size is not None:
        demand(path.stat().st_size == size, 'byte size '+str(path))
    return {'path':str(path),'sha256':digest,'bytes':path.stat().st_size}

def check():
    publication_path = EVIDENCE/'PUBLICATION.json'
    publication_pin = pin(publication_path,PUBLICATION_SHA)
    publication = json.loads(publication_path.read_text())
    file_pins = []
    for item in publication['files']:
        path = EVIDENCE/item['relative_path']
        actual = pin(path,item['sha256'],item['bytes'])
        if 'scratch_origin' in item:
            demand(path.read_bytes() == Path(item['scratch_origin']).read_bytes(), 'exact scratch/publication bytes')
        file_pins.append(actual)
    demand(len(file_pins) == 9 and sum(p['bytes'] for p in file_pins) == publication['included_bytes_before_publication_receipt'],
           'portable publication file inventory')
    source_pin = pin(EVIDENCE/'probe.py',SOURCE_SHA)
    receipt_pin = pin(EVIDENCE/'RECEIPT.json',RECEIPT_SHA)
    receipt = json.loads((EVIDENCE/'RECEIPT.json').read_text())
    demand(receipt['status'] == 'PASS_EXISTING_FAMILY168_EXACT_RESTORATION_ONLY'
           and receipt['compiler_processes'] == receipt['native_or_reference_processes'] == 0
           and receipt['prospective1505_audit_created'] is False
           and receipt['mathematical_acceptance_claim'] is False, 'existing fixed-file prototype scope')
    source = (EVIDENCE/'probe.py').read_text()
    syntax = ast.parse(source)
    source_imports = sorted({node.names[0].name if isinstance(node,ast.Import) else node.module
                            for node in ast.walk(syntax) if isinstance(node,(ast.Import,ast.ImportFrom))})
    demand(set(source_imports) <= {'pathlib','datetime','gzip','hashlib','json','mmap','re','resource','struct','traceback'},
           'prototype imports standard library only')
    demand(not any(isinstance(node,ast.Call) and isinstance(node.func,ast.Name)
                   and node.func.id in {'eval','exec','compile','__import__'} for node in ast.walk(syntax)),
           'no dynamic or target evaluator call')
    demand('resource.setrlimit(resource.RLIMIT_AS, (MEMORY_CAP, MEMORY_CAP))' in source
           and 'SCRATCH_CAP = 32 * 1024 * 1024' in source and 'CHUNK = 1024 * 1024' in source,
           'fixed prototype resource contract')
    demand("base[original[0]:original[1]] == new[start:end]" in source
           and 'digest == expected' not in source, 'raw-byte equality in producer, not name-only reuse')
    base_pin = pin(receipt['base']['path'],receipt['base']['sha256'],receipt['base']['bytes'])
    target_pin = pin(receipt['target']['path'],receipt['target']['sha256'],receipt['target']['bytes'])
    portable_base_pin = pin(receipt['portable_base']['path'],receipt['portable_base']['sha256'],receipt['portable_base']['bytes'])
    saved_restored_pin = pin(receipt['restore']['path'],receipt['target']['sha256'],receipt['target']['bytes'])
    target = Path(receipt['target']['path']).read_bytes()
    demand(Path(receipt['restore']['path']).read_bytes() == target, 'already saved prototype result equals saved target')
    patch = (EVIDENCE/'family168-from1504.copy-literal').read_bytes()
    compressed_patch = (EVIDENCE/'family168-from1504.copy-literal.gz').read_bytes()
    demand(sha(patch) == receipt['delta']['sha256'] and len(patch) == receipt['delta']['delta_bytes'], 'fixed raw patch binding')
    demand(sha(compressed_patch) == receipt['compressed_delta']['sha256'] and gzip.decompress(compressed_patch) == patch,
           'compressed patch restores exact raw patch bytes only')
    demand(patch.startswith(MAGIC) and len(MAGIC) == 25, 'exact25-byte magic')
    cursor = len(MAGIC)
    base_hash = patch[cursor:cursor+32].hex();cursor += 32
    target_hash = patch[cursor:cursor+32].hex();cursor += 32
    target_size = U64.unpack_from(patch,cursor)[0];cursor += 8
    demand(cursor == 97 and base_hash == base_pin['sha256'] and target_hash == target_pin['sha256']
           and target_size == target_pin['bytes'], 'header binds exact saved raw identities and target length')
    target_position = 0
    copies, literals, copied_names = [], [], set()
    copied_bytes = literal_bytes = 0
    with Path(receipt['base']['path']).open('rb') as handle:
        with mmap.mmap(handle.fileno(),0,access=mmap.ACCESS_READ) as base:
            while cursor < len(patch):
                tag = patch[cursor:cursor+1];cursor += 1
                if tag == b'C':
                    demand(cursor+16 <= len(patch), 'complete copy framing')
                    start = U64.unpack_from(patch,cursor)[0]
                    length = U64.unpack_from(patch,cursor+8)[0];cursor += 16
                    demand(length > 0 and start+length <= len(base) and target_position+length <= target_size,
                           'fixed copy span and target bounds')
                    piece = base[start:start+length]
                    demand(piece == target[target_position:target_position+length], 'copy op exact saved target bytes')
                    declaration = json.loads(piece)
                    demand(set(declaration) == {'type_references','name','module','kind','body_references','axioms'},
                           'copied item is one complete saved declaration object')
                    demand(declaration['name'] not in copied_names, 'unique copied declaration')
                    copied_names.add(declaration['name'])
                    copies.append((start,length,target_position))
                    copied_bytes += length
                elif tag == b'L':
                    demand(cursor+8 <= len(patch), 'complete literal framing')
                    length = U64.unpack_from(patch,cursor)[0];cursor += 8
                    demand(length > 0 and cursor+length <= len(patch) and target_position+length <= target_size,
                           'fixed literal and target bounds BEFORE examining payload')
                    demand(patch[cursor:cursor+length] == target[target_position:target_position+length],
                           'literal op exact saved target bytes')
                    literals.append((target_position,length))
                    literal_bytes += length
                    cursor += length
                else:
                    raise AssertionError('unknown fixed patch opcode')
                target_position += length
    demand(cursor == len(patch) and target_position == target_size, 'patch and target partitions complete')
    ordered = sorted(copies)
    demand(all(a[0]+a[1] <= b[0] for a,b in zip(ordered,ordered[1:])), 'unique nonoverlapping sorted base ranges')
    demand((len(copies),len(literals),len(copies)+len(literals)) == (4879,4880,9759), 'exact fixed operation counts')
    demand(copied_bytes == receipt['delta']['copied_bytes'] == 6367219
           and literal_bytes == receipt['delta']['literal_bytes'] == 261893
           and 97 + len(copies)*17 + len(literals)*9 + literal_bytes == len(patch) == 388853,
           'exact byte accounting including framing')
    target_json = json.loads(target)
    target_names = {d['name'] for d in target_json['declarations']}
    demand(len(target_names) == target_json['declaration_count'] == 4907, 'saved family4907 declaration names')
    literal_record_names = target_names-copied_names
    demand(literal_record_names == set(receipt['delta']['changed_names']) | set(receipt['delta']['new_names'])
           and len(receipt['delta']['changed_names']) == 19 and len(receipt['delta']['new_names']) == 9,
           'all19 changed and9 new records excluded from copy candidates')
    earlier_delta_path = PACKET/'design/history/g7-family-normalization-saved-qc-20261010T2308Z-solver_design_recovery/EXACT19-CONTEXT-DELTA-QC-ATTEMPT1.json'
    earlier_delta_pin = pin(earlier_delta_path,'edfb331c9897032f4debb9ef26f80dc6e45b45061a966ff2dbf16af102f02cac')
    earlier_delta = json.loads(earlier_delta_path.read_text())
    old_changed = {d['name'] for d in earlier_delta['generated_owner_module_only_differences']}
    old_changed.add(earlier_delta['private_splitter_alias_only_difference']['name'])
    demand(old_changed == set(receipt['delta']['changed_names']), 'matches independently qualified saved19 context differences')
    return {
        'status':'PASS_FIXED_PATCH_SOURCE_FORMAT_AND_SAVED_BYTE_BINDINGS; no fresh restoration performed',
        'publication':publication_pin,'publication_files':file_pins,'source':source_pin,'prototype_receipt':receipt_pin,
        'source_ast_imports':source_imports,'base_raw':base_pin,'portable_base_gzip':portable_base_pin,
        'target_existing_raw':target_pin,'already_saved_prototype_restore':saved_restored_pin,
        'earlier_independent_exact19_qc':earlier_delta_pin,
        'fixed_patch_counts':{'header_bytes':97,'copy_ops':4879,'literal_ops':4880,'total_ops':9759,
                              'copy_framing_bytes':82943,'literal_framing_bytes':43920,
                              'copied_bytes':copied_bytes,'literal_bytes':literal_bytes,
                              'raw_patch_bytes':388853,'gzip_patch_bytes':72532,
                              'copied_declaration_records':4879,'changed_records_preserved_as_literals':19,
                              'new_records_preserved_as_literals':9,'target_bytes':6629112},
        'fixed_patch_nonoverlapping_base_spans':True,
        'every_fixed_operation_compared_to_already_saved_original_target_bytes':True,
        'new_audit_or_new_restore_output_materialized':False,
        'prototype_observations_only':{'max_rss_kib':receipt['resources']['max_rss_kib'],
                                       'rlimit_as_bytes':268435456,'scratch_cap_bytes':33554432,
                                       'scratch_bytes_before_receipt':receipt['scratch']['bytes_before_receipt']},
        'source_scope_qualifications':[
            'Producer is deliberately bound to these exact saved hashes and Lean serializer. Name indexing chooses a candidate; both raw SHA and direct raw-byte equality decide reuse.',
            'Headers, separators, nineteen changed inherited records and nine new records remain exact literals; no ownership or private-alias metadata is normalized.',
            'Source prototype checks target overflow after writing a literal. Its fixed authenticated patch bounds the preserved example; this is not a general untrusted decoder guarantee.',
            'Operation-count and arbitrary-base budgets are not implemented or accepted by the prototype.',
            'Recorded168 restoration used one portable-base decompression pass, but this reviewer did not launch that restoration or reproduce its resource observations.',
            'The storage result is not a theorem audit, synthesized1505/1506 union, scientific acceptance, or proof of a future codec resource bound.',
        ],
        'requirements_for_separately_approved_fresh_restore_plan':[
            'Authenticate raw and gzip patch SHA/length, immutable portable base gzip SHA/length, and trusted exact raw base/target SHA/length before allocating output.',
            'Fix max9759 operations, max4879 copies and exact388853 decoded-patch bytes for this saved example; bound decompression and parser buffers.',
            'Reject copy and literal target_position+length overflow BEFORE writes, as well as truncation, zero spans, unknown opcodes and nonoverlapping-range violations.',
            'Stream the portable base exactly once, hash all114300292 decompressed bytes including uncopied tails, and write only the fixed6629112-byte target in a new owned attempt directory.',
            'Enforce concrete memory/scratch headroom and preserve exact input bytes and any failure; verify final full target SHA and compare to the existing target when available.',
            'No producer/compiler/reference/native run, no old acceptance mutation and no prospective audit construction.',
        ],
    }

def main():
    destination = Path(sys.argv[1])
    report = {'schema':'audit_fixed_copy_literal_static_design_qc_v1','contributor':'Codex / solver_design_recovery',
              'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':sha(Path(__file__).read_bytes()),
              'target_producer_compiler_helper_adapter_native_reference_processes_started':0,
              'fresh_restore_processes_started':0,'accepted_union_modified':False}
    try:
        report.update(check())
    except Exception as error:
        report.update(status='FAIL_STATIC_REVIEW',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,indent=2,sort_keys=True,ensure_ascii=False)
        handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':sha(destination.read_bytes())}))
    return 1 if report['status'] == 'FAIL_STATIC_REVIEW' else 0

if __name__ == '__main__':
    raise SystemExit(main())
