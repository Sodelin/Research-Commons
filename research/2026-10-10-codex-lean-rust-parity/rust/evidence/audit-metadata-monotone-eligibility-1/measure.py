"""Read-only exact-byte monotone eligibility measurement of saved reports.

No restored report, delta file, mathematical provider, compiler or prospective
union is produced. The compressed delta stream is counted and hashed, then
discarded. This records eligibility, not an accepted restore implementation.
"""
from pathlib import Path
import bisect
import datetime
import hashlib
import json
import mmap
import resource
import struct
import traceback
import zlib

SCRATCH = Path(__file__).resolve().parent
MEMORY_CAP = 256 * 1024 * 1024
SCRATCH_CAP = 32 * 1024 * 1024
MAX_FILE = 20 * 1024 * 1024
MAX_LINE = 1024 * 1024
MAX_LINES = 500000
MIN_COPY_LINE = 32
CHUNK = 1024 * 1024
resource.setrlimit(resource.RLIMIT_AS, (MEMORY_CAP, MEMORY_CAP))
MAGIC = b'RC-AUDIT-COPY-LITERAL-V1\x00'
U64 = struct.Struct('<Q')
BASE_ROOT = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean/evidence/proof-extensions/history-accepted-union-1497/20261010T204542.182773Z/run-20261010T204745.833238Z')
TARGET_ROOT = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z')
TARGET_PORTABLE = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/lean/evidence/proof-extensions/g7-survival-integration/rc-lean-g7-survival-integration-20261010T223510.923050Z/COHERENT-PASS-UNION1504-EXPORT-V5-20261010T223805.816906Z')
PAIRS = [
 ('targets/current_connected/RESULT.json', 'd38edc651ca61980d0d00f2be5091b1e43cf9c84b3942e95c25ddb8dffa95099', '100f1fa547b2c8fdba09ea7011af6638c2f792b4eb7f45c74c5297e12d5b2c1a'),
 ('targets/current_connected/ACTUAL-IMPORTED-ARTIFACTS.json', 'b049a85c0d55850930d20b95d01faa362b3b23d6c14d8fe8dc11e16a04f0dea8', 'f9ba81430223f778c447a3b9287ab947fbb7c4c80ebd10a0af5daa88a4643172'),
 ('NAMESPACE-RESOLUTION-CHECKS.jsonl', '69a7c6f346f75b080edbfbddc7da02705c51e18fbd1f2a424268a10745bd4220', 'b1a09810f5e48ec4e41ae58e5e4bcc9f90b8cef71164153b479725082985cfd6'),
 ('CACHE-INSTALL-TRANSPORT-CHECKS.jsonl', '97ad54941cf376af01413f8861f63bb137855eb431f834876d45389d27ba3631', '3cfc9c149d5e99b4bd5b24126261f32ab0203dd50e864a44cd56207784c967f6'),
 ('CACHE-INSTALL-ALIASES.json', '4f3854703c73e540658676dc65dad872452357b8bf3a2288e6d10657f5740d5f', '739145972c6fdf14c641c5e72e7a22f62572408a56fb825c4278127c00c6cb80'),
 ('DEPENDENCY-GRAPH.json', 'b1cf28461bce4bfc2ba4adcf26e4eca4c76214783cf29e2557ce134db782838e', 'e05a87db2b34f42aada87a958f7ff9114c68a817458b5919f7ecac62386fbacd'),
]


def hash_file(path):
    digest = hashlib.sha256()
    with path.open('rb') as f:
        while raw := f.read(CHUNK):
            digest.update(raw)
    return digest.hexdigest()


class StreamCounter:
    def __init__(self):
        self.compressor = zlib.compressobj(6, zlib.DEFLATED, 31)
        self.raw_bytes = self.gzip_bytes = 0
        self.raw_digest = hashlib.sha256()
        self.gzip_digest = hashlib.sha256()

    def add(self, raw):
        self.raw_bytes += len(raw)
        self.raw_digest.update(raw)
        compressed = self.compressor.compress(raw)
        self.gzip_bytes += len(compressed)
        self.gzip_digest.update(compressed)

    def finish(self):
        tail = self.compressor.flush()
        self.gzip_bytes += len(tail)
        self.gzip_digest.update(tail)
        return {'raw_bytes':self.raw_bytes, 'gzip_counted_bytes':self.gzip_bytes,
                'raw_sha256':self.raw_digest.hexdigest(), 'gzip_sha256':self.gzip_digest.hexdigest()}


def measure(relative, expected_base, expected_target):
    base_path = BASE_ROOT/relative
    target_path = TARGET_ROOT/relative
    for path, expected in [(base_path,expected_base),(target_path,expected_target)]:
        if not path.is_file() or path.stat().st_size > MAX_FILE:
            raise ValueError('input file bound or availability: '+str(path))
        if hash_file(path) != expected:
            raise ValueError('input identity changed: '+str(path))
    index = {}
    base_lines = base_maxline = base_position = indexed_lines = 0
    with base_path.open('rb') as f:
        while raw := f.readline(MAX_LINE+1):
            if len(raw)>MAX_LINE:
                raise ValueError('base line exceeds explicit bound')
            base_lines += 1
            if base_lines>MAX_LINES:
                raise ValueError('base line count exceeds explicit bound')
            base_maxline=max(base_maxline,len(raw))
            if len(raw)>=MIN_COPY_LINE:
                index.setdefault(hashlib.sha256(raw).digest(),[]).append((base_position,len(raw)))
                indexed_lines+=1
            base_position+=len(raw)
    delta = StreamCounter()
    full_gzip = StreamCounter()
    delta.add(MAGIC+bytes.fromhex(expected_base)+bytes.fromhex(expected_target)+U64.pack(target_path.stat().st_size))
    literal = bytearray()
    pending_copy = None
    operations = copies = literals = copied_bytes = literal_bytes = 0
    copied_lines = target_lines = target_maxline = target_position = source_cursor = 0
    target_digest = hashlib.sha256()

    def flush_literal():
        nonlocal operations,literals,literal_bytes
        if literal:
            delta.add(b'L'+U64.pack(len(literal)))
            delta.add(literal)
            operations+=1; literals+=1; literal_bytes+=len(literal)
            literal.clear()

    def flush_copy():
        nonlocal pending_copy,operations,copies,copied_bytes
        if pending_copy is not None:
            start,length=pending_copy
            delta.add(b'C'+U64.pack(start)+U64.pack(length))
            operations+=1; copies+=1; copied_bytes+=length
            pending_copy=None

    with base_path.open('rb') as f, mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as base:
        with target_path.open('rb') as new:
            while raw := new.readline(MAX_LINE+1):
                if len(raw)>MAX_LINE:
                    raise ValueError('target line exceeds explicit bound')
                target_lines+=1
                if target_lines>MAX_LINES:
                    raise ValueError('target line count exceeds explicit bound')
                target_maxline=max(target_maxline,len(raw))
                target_position+=len(raw)
                target_digest.update(raw)
                full_gzip.add(raw)
                found=None
                if len(raw)>=MIN_COPY_LINE:
                    candidates=index.get(hashlib.sha256(raw).digest(),[])
                    i=bisect.bisect_left(candidates,(source_cursor,0))
                    for start,length in candidates[i:]:
                        if length==len(raw) and base[start:start+length]==raw:
                            found=(start,length)
                            break
                if found is not None:
                    start,length=found
                    if start<source_cursor:
                        raise ValueError('nonmonotone candidate')
                    flush_literal()
                    if pending_copy is not None and pending_copy[0]+pending_copy[1]==start:
                        pending_copy=(pending_copy[0],pending_copy[1]+length)
                    else:
                        flush_copy()
                        pending_copy=(start,length)
                    source_cursor=start+length
                    copied_lines+=1
                else:
                    flush_copy()
                    if len(literal)+len(raw)>MAX_LINE:
                        flush_literal()
                    literal.extend(raw)
            flush_copy();flush_literal()
    if target_digest.hexdigest()!=expected_target or target_position!=target_path.stat().st_size:
        raise ValueError('target stream identity mismatch')
    if copied_bytes+literal_bytes!=target_position:
        raise ValueError('bytes not completely partitioned')
    portable=TARGET_PORTABLE/(relative+'.gz')
    portable_identity=None
    if portable.is_file():
        portable_identity={'path':str(portable),'bytes':portable.stat().st_size,'sha256':hash_file(portable)}
    counted_delta=delta.finish(); counted_full=full_gzip.finish()
    return {
        'relative':relative,
        'base':{'path':str(base_path),'bytes':base_path.stat().st_size,'sha256':expected_base,
                'lines':base_lines,'max_line_bytes':base_maxline},
        'target':{'path':str(target_path),'bytes':target_position,'sha256':expected_target,
                  'lines':target_lines,'max_line_bytes':target_maxline},
        'indexed_base_lines':indexed_lines,'index_keys':len(index),
        'copied_target_lines':copied_lines,'copied_bytes':copied_bytes,'literal_bytes':literal_bytes,
        'operations':operations,'copy_operations':copies,'literal_operations':literals,
        'all_copy_ranges_monotone_nonoverlapping':True,'all_copies_direct_byte_equal':True,
        'counted_delta':counted_delta,'counted_full_same_gzip6':counted_full,
        'existing_target_portable_gzip':portable_identity,
        'restoration_executed':False,'delta_file_created':False,'new_report_created':False,
    }


def main():
    if sum(p.stat().st_size for p in SCRATCH.iterdir() if p.is_file())>SCRATCH_CAP-131072:
        raise ValueError('insufficient precharged receipt/log scratch')
    rows=[]
    for relative,base,target in PAIRS:
        row=measure(relative,base,target)
        rows.append(row)
        print(json.dumps({'relative':relative,'copied_bytes':row['copied_bytes'],
                         'literal_bytes':row['literal_bytes'],'delta_gzip_counted_bytes':row['counted_delta']['gzip_counted_bytes'],
                         'full_gzip6_counted_bytes':row['counted_full_same_gzip6']['gzip_counted_bytes']},sort_keys=True),flush=True)
    result={
        'schema':'saved_metadata_monotone_eligibility_v1',
        'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status':'MEASURED_EXISTING_1497_TO_EXISTING_1504_ONLY',
        'rows':rows,
        'scope':'byte-storage eligibility count; no restore acceptance and no prospective union audit',
        'limits':{'memory_address_space_bytes':MEMORY_CAP,'scratch_bytes':SCRATCH_CAP,
                  'file_bytes':MAX_FILE,'line_bytes':MAX_LINE,'line_count':MAX_LINES,'min_copied_line_bytes':MIN_COPY_LINE},
        'resources':{'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                     'scratch_bytes_before_receipt':sum(p.stat().st_size for p in SCRATCH.iterdir() if p.is_file())},
        'script':{'path':str(Path(__file__).resolve()),'sha256':hash_file(Path(__file__))},
        'compression':{'level':6,'wbits':31,'zlib_runtime':zlib.ZLIB_RUNTIME_VERSION,'output_counted_hashed_discarded':True},
        'copied_bytes_total':sum(row['copied_bytes'] for row in rows),
        'literal_bytes_total':sum(row['literal_bytes'] for row in rows),
        'delta_gzip_counted_bytes_total':sum(row['counted_delta']['gzip_counted_bytes'] for row in rows),
        'existing_evidence_modified':False,'compiler_native_reference_processes':0,
        'prospective1505_audit_created':False,'prospective1506_audit_created':False,
        'mathematical_acceptance_claim':False,
    }
    with (SCRATCH/'RECEIPT.json').open('x') as f:
        f.write(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'receipt_sha256':hash_file(SCRATCH/'RECEIPT.json'),
                     'max_rss_kib':result['resources']['max_rss_kib'],
                     'delta_gzip_counted_bytes_total':result['delta_gzip_counted_bytes_total']},sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except BaseException as error:
        with (SCRATCH/'FAILURE.json').open('x') as f:
            f.write(json.dumps({'status':'ELIGIBILITY_FAILURE_PRESERVED','error':str(error),
                                'traceback':traceback.format_exc(),'prospective_audit_created':False},indent=2)+'\n')
        raise
