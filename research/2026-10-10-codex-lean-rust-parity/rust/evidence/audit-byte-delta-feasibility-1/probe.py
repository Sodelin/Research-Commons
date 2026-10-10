"""Storage-only, exact-byte delta experiment on two already saved Lean audits.

No theorem/provider execution and no prospective 1505 audit is synthesized.
The record recognizer is deliberately bound to these input hashes/serializer.
"""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import mmap
import re
import resource
import struct
import traceback

SCRATCH = Path(__file__).resolve().parent
SCRATCH_CAP = 32 * 1024 * 1024
MEMORY_CAP = 256 * 1024 * 1024
CHUNK = 1024 * 1024
resource.setrlimit(resource.RLIMIT_AS, (MEMORY_CAP, MEMORY_CAP))
BASE = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json')
NEW = Path('/dev/shm/rc-lean-g7-family-normalization-20261010T230143.534018Z/.build/runs/20261010T230235.850157Z/attempts/00003-OwnedAudit/work/AUDIT-RESULT.json')
BASE_GZ = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean/evidence/proof-extensions/g7-survival-integration/rc-lean-g7-survival-integration-20261010T223510.923050Z/COHERENT-PASS-UNION1504-EXPORT-V5-20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json.gz')
EXPECTED_BASE = '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813'
EXPECTED_NEW = '0433bdbbe2b4c2b5ee4d48aa5963de57dd33fd9b658840e1e4c4a53fdc141a8e'
MAGIC = b'RC-AUDIT-COPY-LITERAL-V1\x00'
TOP = re.compile(rb'(?:^\{|^ )"([^"\n]+)":', re.M)
RECORD_START = re.compile(rb'^ {1,2}(?:\[)?\{', re.M)
U64 = struct.Struct('<Q')


def hash_file(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        while block := f.read(CHUNK):
            h.update(block)
    return h.hexdigest()


def usage():
    return sum(p.stat().st_size for p in SCRATCH.iterdir() if p.is_file())


def reserve(extra):
    if usage() + extra > SCRATCH_CAP:
        raise ValueError('scratch precheck exceeds 32 MiB')


def span_fields(mm):
    hits = list(TOP.finditer(mm))
    names = [h.group(1).decode('ascii') for h in hits]
    expected = ['theorem_declaration_count', 'selected_modules', 'owned_axioms',
                'nonstandard_axiom_rows', 'missing_modules', 'declarations',
                'declaration_count', 'all_imported_module_names']
    if names != expected:
        raise ValueError('unexpected pinned serializer shape')
    return {h.group(1).decode(): (h.start(), h.end(), hits[i+1].start() if i+1<len(hits) else len(mm))
            for i,h in enumerate(hits)}


def records(mm, fields):
    _, field_end, block_end = fields['declarations']
    starts = [mm.find(b'{', m.start(), m.end()) for m in RECORD_START.finditer(mm, field_end, block_end)]
    if not starts:
        raise ValueError('no declaration records')
    for i,start in enumerate(starts):
        limit = starts[i+1] if i+1<len(starts) else block_end
        end = mm.rfind(b'}', start, limit) + 1
        if end <= start:
            raise ValueError('invalid record span')
        raw = mm[start:end]
        obj = json.loads(raw)
        if set(obj) != {'type_references','name','module','kind','body_references','axioms'}:
            raise ValueError('unexpected declaration object fields')
        if not isinstance(obj['name'], str):
            raise ValueError('invalid declaration name')
        yield obj['name'], start, end, hashlib.sha256(raw).digest(), obj['module']


def append_op(ops, kind, offset, length):
    if not length:
        return
    if ops and ops[-1][0] == kind and ops[-1][1] + ops[-1][2] == offset:
        old = ops[-1]
        ops[-1] = (kind, old[1], old[2] + length)
    else:
        ops.append((kind, offset, length))


def make_delta(base, new, base_fields, new_fields):
    index = {}
    for name,start,end,digest,module in records(base, base_fields):
        if name in index:
            raise ValueError('duplicate base declaration name')
        index[name] = (start,end,digest)
    base_count = len(index)
    ops = []
    cursor = 0
    exact = changed = fresh = 0
    changed_names = []
    fresh_names = []
    record_bytes = {'exact':0, 'changed':0, 'fresh':0}
    seen = set()
    for name,start,end,digest,module in records(new, new_fields):
        if name in seen:
            raise ValueError('duplicate new declaration name')
        seen.add(name)
        append_op(ops, 'L', cursor, start-cursor)
        original = index.get(name)
        if original and original[2] == digest and base[original[0]:original[1]] == new[start:end]:
            exact += 1
            record_bytes['exact'] += end-start
            append_op(ops, 'C', original[0], original[1]-original[0])
        else:
            if original:
                changed += 1
                changed_names.append(name)
                record_bytes['changed'] += end-start
            else:
                fresh += 1
                fresh_names.append(name)
                record_bytes['fresh'] += end-start
            append_op(ops, 'L', start, end-start)
        cursor = end
    append_op(ops, 'L', cursor, len(new)-cursor)
    # The worst case is literal target plus small op framing, still precharged.
    reserve(len(new) + len(ops)*17 + len(MAGIC) + 72)
    delta_path = SCRATCH/'family168-from1504.copy-literal'
    literal_bytes = copied_bytes = 0
    with delta_path.open('xb') as f:
        f.write(MAGIC)
        f.write(bytes.fromhex(EXPECTED_BASE))
        f.write(bytes.fromhex(EXPECTED_NEW))
        f.write(U64.pack(len(new)))
        for kind,offset,length in ops:
            f.write(kind.encode())
            if kind == 'C':
                f.write(U64.pack(offset)); f.write(U64.pack(length))
                copied_bytes += length
            else:
                f.write(U64.pack(length))
                for p in range(offset, offset+length, CHUNK):
                    f.write(new[p:min(offset+length,p+CHUNK)])
                literal_bytes += length
    if copied_bytes+literal_bytes != len(new):
        raise ValueError('delta does not partition new bytes')
    return delta_path, {
        'base_record_count':base_count, 'target_record_count':len(seen),
        'exact_copied_record_count':exact, 'changed_same_name_record_count':changed,
        'new_name_record_count':fresh, 'changed_names':changed_names, 'new_names':fresh_names,
        'record_bytes':record_bytes, 'ops':len(ops), 'literal_bytes':literal_bytes,
        'copied_bytes':copied_bytes, 'delta_bytes':delta_path.stat().st_size,
    }


def restore_from_portable_gzip(delta_path):
    reserve(NEW.stat().st_size)
    output = SCRATCH/'family168.restored.json'
    copies = []
    with delta_path.open('rb') as f, output.open('xb+') as out:
        if f.read(len(MAGIC)) != MAGIC:
            raise ValueError('wrong delta magic')
        base_hash = f.read(32).hex(); new_hash = f.read(32).hex()
        new_size = U64.unpack(f.read(8))[0]
        if base_hash != EXPECTED_BASE or new_hash != EXPECTED_NEW or new_size != NEW.stat().st_size:
            raise ValueError('wrong pinned delta identity')
        out.truncate(new_size)
        position = 0
        while tag := f.read(1):
            if tag == b'C':
                start = U64.unpack(f.read(8))[0]; length = U64.unpack(f.read(8))[0]
                if not length or start+length > BASE.stat().st_size:
                    raise ValueError('invalid copy span')
                copies.append((start,length,position))
                position += length
            elif tag == b'L':
                remaining = U64.unpack(f.read(8))[0]
                if not remaining:
                    raise ValueError('empty literal')
                out.seek(position)
                while remaining:
                    block = f.read(min(CHUNK,remaining))
                    if not block:
                        raise ValueError('truncated literal')
                    out.write(block); position += len(block); remaining -= len(block)
            else:
                raise ValueError('unknown opcode')
            if position > new_size:
                raise ValueError('target span overflow')
        if position != new_size:
            raise ValueError('target span incomplete')
        # Copy spans refer to distinct declaration objects. Sort by base offset
        # and decompress the base exactly once, writing their target offsets.
        digest = hashlib.sha256()
        raw_position = 0
        compressed_read_bytes = BASE_GZ.stat().st_size
        with gzip.open(BASE_GZ,'rb') as gz:
            for start,length,destination in sorted(copies):
                if start < raw_position:
                    raise ValueError('overlapping copy spans need another restore strategy')
                while raw_position < start:
                    block = gz.read(min(CHUNK,start-raw_position))
                    if not block: raise ValueError('truncated portable base')
                    digest.update(block); raw_position += len(block)
                out.seek(destination)
                remaining = length
                while remaining:
                    block = gz.read(min(CHUNK,remaining))
                    if not block: raise ValueError('truncated portable base copy')
                    digest.update(block); out.write(block)
                    raw_position += len(block); remaining -= len(block)
            while block := gz.read(CHUNK):
                digest.update(block); raw_position += len(block)
        if digest.hexdigest() != base_hash or raw_position != BASE.stat().st_size:
            raise ValueError('portable base raw identity mismatch')
    if hash_file(output) != EXPECTED_NEW:
        raise ValueError('restored target hash mismatch')
    compared = 0
    with output.open('rb') as a, NEW.open('rb') as b:
        while block := a.read(CHUNK):
            if block != b.read(len(block)):
                raise ValueError('restored target byte inequality')
            compared += len(block)
        if b.read(1): raise ValueError('restored target shorter than original')
    return output, {'portable_base_raw_sha256':digest.hexdigest(),
        'portable_base_raw_bytes':raw_position,'portable_base_compressed_bytes':compressed_read_bytes,
        'base_decompression_passes':1,'target_bytes_compared':compared,
        'target_sha256':hash_file(output),'byte_for_byte_equal':True}


def main():
    before = usage()
    for p,expected in [(BASE,EXPECTED_BASE),(NEW,EXPECTED_NEW)]:
        if hash_file(p) != expected: raise ValueError('raw audit identity mismatch')
    with BASE.open('rb') as bf, NEW.open('rb') as nf:
        with mmap.mmap(bf.fileno(),0,access=mmap.ACCESS_READ) as base:
            with mmap.mmap(nf.fileno(),0,access=mmap.ACCESS_READ) as new:
                base_fields = span_fields(base); new_fields = span_fields(new)
                delta,details = make_delta(base,new,base_fields,new_fields)
    restored,identity = restore_from_portable_gzip(delta)
    compressed = SCRATCH/(delta.name+'.gz')
    reserve(delta.stat().st_size+1024)
    with delta.open('rb') as src, compressed.open('xb') as dst:
        with gzip.GzipFile(fileobj=dst,mode='wb',mtime=0,filename='',compresslevel=6) as z:
            while block := src.read(CHUNK): z.write(block)
    result = {
        'schema':'audit_exact_byte_delta_feasibility_v1',
        'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status':'PASS_EXISTING_FAMILY168_EXACT_RESTORATION_ONLY',
        'base':{'path':str(BASE),'bytes':BASE.stat().st_size,'sha256':EXPECTED_BASE},
        'portable_base':{'path':str(BASE_GZ),'bytes':BASE_GZ.stat().st_size,'sha256':hash_file(BASE_GZ)},
        'target':{'path':str(NEW),'bytes':NEW.stat().st_size,'sha256':EXPECTED_NEW},
        'delta':{'path':str(delta),'sha256':hash_file(delta),**details},
        'compressed_delta':{'path':str(compressed),'bytes':compressed.stat().st_size,'sha256':hash_file(compressed)},
        'restore':{'path':str(restored),**identity},
        'json_span_shape':{'base':base_fields,'target':new_fields},
        'scratch':{'path':str(SCRATCH),'initial_bytes':before,'bytes_before_receipt':usage(),
                   'cap':SCRATCH_CAP},
        'resources':{'rlimit_as_bytes':MEMORY_CAP,'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
        'script':{'path':str(Path(__file__).resolve()),'sha256':hash_file(Path(__file__))},
        'prospective1505_audit_created':False,'compiler_processes':0,'native_or_reference_processes':0,
        'existing_evidence_modified':False,'mathematical_acceptance_claim':False,
    }
    rp=SCRATCH/'RECEIPT.json'
    with rp.open('x') as f: f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'receipt':str(rp),'sha256':hash_file(rp),
        'delta_bytes':details['delta_bytes'],'compressed_delta_bytes':compressed.stat().st_size,
        'copied_records':details['exact_copied_record_count'],
        'changed_records':details['changed_same_name_record_count'],'new_records':details['new_name_record_count'],
        'scratch_bytes':usage(),'max_rss_kib':result['resources']['max_rss_kib'],
        'restored_sha256':identity['target_sha256'],'byte_for_byte_equal':True},sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except BaseException as error:
        failure={'status':'PROTOTYPE_FAILURE_PRESERVED','error':str(error),'traceback':traceback.format_exc(),
            'scratch_bytes':usage(),'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'prospective1505_audit_created':False}
        with (SCRATCH/'FAILURE.json').open('x') as f: f.write(json.dumps(failure,indent=2)+'\n')
        raise
