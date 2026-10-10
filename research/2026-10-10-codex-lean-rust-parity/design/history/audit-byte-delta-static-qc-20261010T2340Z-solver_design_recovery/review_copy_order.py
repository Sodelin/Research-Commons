#!/usr/bin/env python3
"""Read encoded copy order in a fixed saved patch; produce no restored bytes."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import struct
import sys

ROOT = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
PATCH = ROOT/'rust/evidence/audit-byte-delta-feasibility-1/family168-from1504.copy-literal'
PATCH_SHA = '050bcdda12538f74ed1a401eb51a59f9052141ef6dfe61613d4e11230c99dd8f'
PREVIOUS = ROOT/'design/history/audit-byte-delta-static-qc-20261010T2340Z-solver_design_recovery/AUDIT-BYTE-DELTA-STATIC-QC-ATTEMPT1.json'
PREVIOUS_SHA = '37656364dd932f92e2e32b7c33b573b79f1ae7ee9371d282cb9a2c42406f1d54'
MAGIC = b'RC-AUDIT-COPY-LITERAL-V1\x00'
U64 = struct.Struct('<Q')

def digest(data):
    return hashlib.sha256(data).hexdigest()

def demand(condition, explanation):
    if not condition:
        raise AssertionError(explanation)

def check():
    previous = PREVIOUS.read_bytes()
    patch = PATCH.read_bytes()
    demand(digest(previous) == PREVIOUS_SHA, 'previous immutable QC')
    demand(digest(patch) == PATCH_SHA and len(patch) == 388853, 'immutable patch identity')
    demand(patch[:25] == MAGIC, 'format magic')
    demand(patch[25:57].hex() == '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813', 'base identity')
    demand(patch[57:89].hex() == '0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e', 'target identity')
    target_size = U64.unpack_from(patch, 89)[0]
    demand(target_size == 6629112, 'fixed target size')
    cursor, target_position = 97, 0
    copies, literals = [], 0
    literal_bytes, copied_bytes = 0, 0
    while cursor < len(patch):
        opcode = patch[cursor:cursor+1]
        cursor += 1
        if opcode == b'C':
            demand(cursor+16 <= len(patch), 'copy frame')
            start, length = struct.unpack_from('<QQ', patch, cursor)
            cursor += 16
            demand(length > 0 and start+length <= 114300292 and target_position+length <= target_size, 'copy bounds')
            copies.append((start, length, target_position))
            copied_bytes += length
        elif opcode == b'L':
            demand(cursor+8 <= len(patch), 'literal frame')
            length = U64.unpack_from(patch, cursor)[0]
            cursor += 8
            demand(length > 0 and cursor+length <= len(patch) and target_position+length <= target_size, 'literal bounds')
            cursor += length
            literals += 1
            literal_bytes += length
        else:
            raise AssertionError('unknown opcode')
        target_position += length
    demand(cursor == len(patch) and target_position == target_size, 'complete byte partitions')
    backwards = [index for index, (previous, current) in enumerate(zip(copies, copies[1:]), 1)
                 if current[0] < previous[0]]
    overlaps_in_encoded_order = [index for index, (previous, current) in enumerate(zip(copies, copies[1:]), 1)
                                if current[0] < previous[0]+previous[1]]
    demand(not backwards and not overlaps_in_encoded_order, 'encoded copy order monotone and nonoverlapping')
    demand((len(copies), literals, copied_bytes, literal_bytes) == (4879, 4880, 6367219, 261893), 'exact counts')
    return {
        'status':'PASS_SAVED_PATCH_ENCODED_COPY_ORDER',
        'previous_qc':{'path':str(PREVIOUS),'sha256':PREVIOUS_SHA},
        'fixed_patch':{'path':str(PATCH),'sha256':PATCH_SHA,'bytes':len(patch)},
        'copy_operations':len(copies),'literal_operations':literals,'all_operations':len(copies)+literals,
        'encoded_copy_source_order_backsteps':len(backwards),
        'encoded_copy_source_order_overlap_violations':len(overlaps_in_encoded_order),
        'encoded_copy_ranges_monotone_and_nonoverlapping':True,
        'ordered_copy_spans_canonical_sha256':digest(json.dumps(copies,separators=(',',':')).encode()),
        'first_copy_range':copies[0],'last_copy_range':copies[-1],
        'copied_bytes':copied_bytes,'literal_bytes':literal_bytes,'target_bytes':target_position,
        'reconciliation':[
            'Previous immutable QC proved nonoverlap only after sorting copy ranges. This receipt separately proves encoded operation order is already monotone and nonoverlapping.',
            'The saved prototype sorting was unnecessary for this exact patch. No conclusion about arbitrary old or future patches follows.',
            'A derivative enforcing each copy start at or beyond the previous copy end can restore from one portable-base-gzip pass in encoded target order; backward candidates must become literal bytes.',
            'The new derivative source and future trial still require separate source QC and root approval. This inspection restores no output and launches no codec.'
        ],
        'checkpoint_scope_clarification':'Our own review scripts, receipts, preserved script versions and checkpoints were written. Existing mathematical/runtime producer source and shared/public files were not modified.'
    }

def main():
    destination = Path(sys.argv[1])
    report = {'schema':'saved_copy_order_independent_reconciliation_v1','contributor':'Codex / solver_design_recovery',
              'observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':digest(Path(__file__).read_bytes()),
              'target_producer_processes_started':0,'fresh_codec_or_restoration_processes_started':0,
              'restored_bytes_materialized':False,'scientific_acceptance_modified':False}
    try:
        report.update(check())
    except Exception as error:
        report.update(status='FAIL_SAVED_COPY_ORDER_QC',error_type=type(error).__name__,error=str(error))
    with destination.open('x') as handle:
        json.dump(report,handle,indent=2,sort_keys=True)
        handle.write('\n')
    print(json.dumps({'status':report['status'],'receipt':str(destination),'sha256':digest(destination.read_bytes())}))
    return 1 if report['status'].startswith('FAIL') else 0

if __name__ == '__main__':
    raise SystemExit(main())
