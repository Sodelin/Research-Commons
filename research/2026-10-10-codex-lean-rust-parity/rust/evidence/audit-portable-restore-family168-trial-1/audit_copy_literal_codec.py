"""Bounded exact-byte storage codec for independently pinned saved Lean audits.

This is not a theorem auditor, JSON normalizer, general source validator, or
compiler. Plans must bind already saved input bytes. Copies are monotone and
literal bytes retain every changed record/header/context. No target mmap is
used. A restore may compare/hash without producing any restored file.
"""
from __future__ import annotations

import argparse
from contextlib import ExitStack
from dataclasses import asdict, dataclass
import datetime
import gzip
import hashlib
import json
import mmap
from pathlib import Path
import re
import resource
import struct

MAGIC = b'RC-AUDIT-COPY-LITERAL-V1\x00'
U64 = struct.Struct('<Q')
CHUNK = 64 * 1024
MAX_ADDRESS_SPACE = 256 * 1024 * 1024
MAX_SCRATCH = 32 * 1024 * 1024
TOP = re.compile(rb'(?:^\{|^ )"([^"\n]+)":', re.M)
RECORD_START = re.compile(rb'^ {1,2}(?:\[)?\{', re.M)
TOP_FIELDS = ('theorem_declaration_count', 'selected_modules', 'owned_axioms',
              'nonstandard_axiom_rows', 'missing_modules', 'declarations',
              'declaration_count', 'all_imported_module_names')
RECORD_FIELDS = {'type_references', 'name', 'module', 'kind', 'body_references', 'axioms'}


class CodecRefusal(ValueError):
    """Export/restoration refusal; never mathematical infeasibility."""

    def __init__(self, reason, detail=''):
        self.reason = reason
        self.detail = detail
        super().__init__(reason + (': ' + detail if detail else ''))


def require(condition, reason, detail=''):
    if not condition:
        raise CodecRefusal(reason, detail)


def natural(value):
    return type(value) is int and 0 <= value < 2**64


def digest_shape(value):
    return isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'DUPLICATE_JSON_KEY', key)
        result[key] = value
    return result


def no_float(value):
    raise CodecRefusal('NONINTEGER_METADATA', value)


def parse_small_json(raw):
    require(len(raw) <= 65536, 'PLAN_FRAME_LIMIT')
    try:
        return json.loads(raw, object_pairs_hook=unique_object,
                          parse_float=no_float, parse_constant=no_float)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CodecRefusal('INVALID_PLAN_JSON', str(error)) from error


@dataclass(frozen=True)
class FilePin:
    path: str
    bytes: int
    sha256: str

    def validate(self):
        require(isinstance(self.path, str) and self.path != '', 'INVALID_FILE_PATH')
        require(natural(self.bytes), 'INVALID_PIN_LENGTH')
        require(digest_shape(self.sha256), 'INVALID_PIN_DIGEST')

    @classmethod
    def decode(cls, value):
        require(isinstance(value, dict) and set(value) == {'path', 'bytes', 'sha256'},
                'INVALID_FILE_PIN_FIELDS')
        result = cls(**value)
        result.validate()
        return result


@dataclass(frozen=True)
class Limits:
    raw_file_bytes: int = 128 * 1024 * 1024
    line_bytes: int = 1024 * 1024
    record_bytes: int = 2 * 1024 * 1024
    record_count: int = 200000
    operation_count: int = 500000
    patch_raw_bytes: int = 192 * 1024 * 1024
    patch_gzip_bytes: int = 1024 * 1024
    literal_buffer_bytes: int = 1024 * 1024
    optional_output_bytes: int = 16 * 1024 * 1024
    scratch_bytes: int = MAX_SCRATCH

    def validate(self):
        ceilings = asdict(Limits(patch_gzip_bytes=MAX_SCRATCH,
                                 optional_output_bytes=MAX_SCRATCH))
        for name, value in asdict(self).items():
            require(natural(value) and 0 < value <= ceilings[name], 'INVALID_LIMIT', name)
        require(self.line_bytes <= self.record_bytes, 'INCOMPATIBLE_LINE_RECORD_LIMIT')
        require(self.literal_buffer_bytes >= CHUNK, 'LITERAL_BUFFER_TOO_SMALL')
        require(self.patch_gzip_bytes <= self.scratch_bytes, 'PATCH_SCRATCH_LIMIT')
        require(self.optional_output_bytes <= self.scratch_bytes, 'OUTPUT_SCRATCH_LIMIT')


@dataclass(frozen=True)
class Plan:
    base_raw: FilePin
    base_gzip: FilePin
    target_raw: FilePin
    scratch_root: str
    limits: Limits

    def validate(self):
        for pin in (self.base_raw, self.base_gzip, self.target_raw):
            pin.validate()
        self.limits.validate()
        require(0 < self.base_raw.bytes <= self.limits.raw_file_bytes, 'BASE_RAW_SIZE_LIMIT')
        require(0 < self.target_raw.bytes <= self.limits.raw_file_bytes, 'TARGET_RAW_SIZE_LIMIT')
        require(0 < self.base_gzip.bytes <= self.limits.raw_file_bytes, 'BASE_GZIP_SIZE_LIMIT')
        require(isinstance(self.scratch_root, str) and self.scratch_root != '', 'INVALID_SCRATCH_ROOT')
        require(Path(self.scratch_root).is_dir(), 'SCRATCH_ROOT_NOT_PRESENT')

    def encode(self):
        return {'schema': 'audit_copy_literal_plan_v1', **asdict(self)}

    @classmethod
    def decode(cls, value):
        fields = {'schema', 'base_raw', 'base_gzip', 'target_raw', 'scratch_root', 'limits'}
        require(isinstance(value, dict) and set(value) == fields, 'INVALID_PLAN_FIELDS')
        require(value['schema'] == 'audit_copy_literal_plan_v1', 'INVALID_PLAN_SCHEMA')
        require(isinstance(value['limits'], dict) and set(value['limits']) == set(asdict(Limits())),
                'INVALID_LIMIT_FIELDS')
        result = cls(FilePin.decode(value['base_raw']), FilePin.decode(value['base_gzip']),
                     FilePin.decode(value['target_raw']), value['scratch_root'], Limits(**value['limits']))
        result.validate()
        return result


@dataclass(frozen=True)
class PatchPin:
    gzip_file: FilePin
    raw_bytes: int
    raw_sha256: str
    base_raw_bytes: int
    base_raw_sha256: str
    target_raw_bytes: int
    target_raw_sha256: str
    operations: int
    copies: int
    literals: int
    decoded_bytes: int
    source_copies_monotone: bool

    def validate(self, plan):
        self.gzip_file.validate()
        require(self.gzip_file.bytes <= plan.limits.patch_gzip_bytes, 'PATCH_GZIP_LIMIT')
        require(natural(self.raw_bytes) and len(MAGIC)+72 <= self.raw_bytes <= plan.limits.patch_raw_bytes,
                'PATCH_RAW_LIMIT')
        require(digest_shape(self.raw_sha256), 'INVALID_RAW_PATCH_DIGEST')
        require((self.base_raw_bytes, self.base_raw_sha256) == (plan.base_raw.bytes, plan.base_raw.sha256),
                'PATCH_BASE_BINDING')
        require((self.target_raw_bytes, self.target_raw_sha256, self.decoded_bytes) ==
                (plan.target_raw.bytes, plan.target_raw.sha256, plan.target_raw.bytes), 'PATCH_TARGET_BINDING')
        require(all(natural(x) for x in (self.base_raw_bytes, self.target_raw_bytes,
                                       self.operations, self.copies, self.literals, self.decoded_bytes)),
                'INVALID_PATCH_COUNTS')
        require(self.operations == self.copies+self.literals and self.operations <= plan.limits.operation_count,
                'PATCH_OPERATION_LIMIT')
        require(self.copies <= plan.limits.record_count, 'PATCH_COPY_LIMIT')
        require(self.source_copies_monotone is True, 'NONMONOTONE_PATCH')

    def encode(self):
        return {'schema': 'audit_copy_literal_patch_pin_v1', **asdict(self)}

    @classmethod
    def decode(cls, value):
        fields = set(cls.__dataclass_fields__) | {'schema'}
        require(isinstance(value, dict) and set(value) == fields, 'INVALID_PATCH_PIN_FIELDS')
        require(value['schema'] == 'audit_copy_literal_patch_pin_v1', 'INVALID_PATCH_PIN_SCHEMA')
        args = {k: v for k, v in value.items() if k != 'schema'}
        args['gzip_file'] = FilePin.decode(args['gzip_file'])
        return cls(**args)


def enforce_address_space_limit():
    old_soft, old_hard = resource.getrlimit(resource.RLIMIT_AS)
    hard = MAX_ADDRESS_SPACE if old_hard == resource.RLIM_INFINITY else min(old_hard, MAX_ADDRESS_SPACE)
    soft = hard if old_soft == resource.RLIM_INFINITY else min(old_soft, hard)
    resource.setrlimit(resource.RLIMIT_AS, (soft, hard))
    return soft


def scratch_usage(plan):
    total = 0
    for path in Path(plan.scratch_root).rglob('*'):
        if path.is_file():
            total += path.stat().st_size
            require(total <= plan.limits.scratch_bytes, 'SCRATCH_LIMIT')
    return total


def reserve_scratch(plan, extra):
    require(natural(extra) and scratch_usage(plan)+extra <= plan.limits.scratch_bytes, 'SCRATCH_LIMIT')


def new_output_path(plan, output):
    output = Path(output)
    root = Path(plan.scratch_root).resolve()
    require(output.parent.is_dir() and output.parent.resolve() == root, 'OUTPUT_OUTSIDE_SCRATCH')
    require(not output.exists() and not output.is_symlink(), 'OUTPUT_ALREADY_EXISTS')
    return output


def authenticate_file(stack, pin):
    try:
        handle = stack.enter_context(Path(pin.path).open('rb'))
    except OSError as error:
        raise CodecRefusal('PINNED_INPUT_UNAVAILABLE', str(error)) from error
    require(handle.seek(0, 2) == pin.bytes, 'PINNED_INPUT_SIZE', pin.path)
    handle.seek(0)
    digest = hashlib.sha256()
    position = 0
    while raw := handle.read(CHUNK):
        require(position+len(raw) <= pin.bytes, 'PINNED_INPUT_SIZE', pin.path)
        digest.update(raw)
        position += len(raw)
    require(position == pin.bytes, 'PINNED_INPUT_SIZE', pin.path)
    require(digest.hexdigest() == pin.sha256, 'PINNED_INPUT_HASH', pin.path)
    handle.seek(0)
    return handle


def verify_base_gzip(raw_handle, gzip_handle, pin):
    """Producer preauthentication, with no target or patch output yet."""
    raw_handle.seek(0)
    gzip_handle.seek(0)
    digest = hashlib.sha256()
    position = 0
    with gzip.GzipFile(fileobj=gzip_handle, mode='rb') as stream:
        while piece := stream.read(CHUNK):
            require(position+len(piece) <= pin.bytes, 'BASE_GZIP_DECODED_SIZE')
            require(raw_handle.read(len(piece)) == piece, 'BASE_GZIP_RAW_BYTE_MISMATCH')
            digest.update(piece)
            position += len(piece)
    require(position == pin.bytes and digest.hexdigest() == pin.sha256, 'BASE_GZIP_RAW_HASH')
    require(raw_handle.read(1) == b'', 'BASE_RAW_TRAILING_BYTES')
    raw_handle.seek(0)
    gzip_handle.seek(0)


def bounded_record(raw, limits):
    require(0 < len(raw) <= limits.record_bytes, 'RECORD_BYTES_LIMIT')
    try:
        record = json.loads(raw, object_pairs_hook=unique_object)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise CodecRefusal('INVALID_PINNED_RECORD', str(error)) from error
    require(isinstance(record, dict) and set(record) == RECORD_FIELDS, 'RECORD_FIELD_SHAPE')
    require(isinstance(record['name'], str), 'RECORD_NAME_SHAPE')
    return record['name']


def base_index(base, limits):
    hits = list(TOP.finditer(base))
    require(tuple(h.group(1).decode('ascii') for h in hits) == TOP_FIELDS, 'BASE_TOP_FIELD_SHAPE')
    start = hits[5].end()
    stop = hits[6].start()
    starts = []
    for match in RECORD_START.finditer(base, start, stop):
        require(len(starts) < limits.record_count, 'BASE_RECORD_COUNT_LIMIT')
        starts.append(base.find(b'{', match.start(), match.end()))
    require(starts, 'BASE_NO_DECLARATION_RECORDS')
    index = {}
    for i, begin in enumerate(starts):
        limit = starts[i+1] if i+1 < len(starts) else stop
        end = base.rfind(b'}', begin, limit)+1
        require(end > begin and end-begin <= limits.record_bytes, 'BASE_RECORD_SPAN_LIMIT')
        raw = base[begin:end]
        name = bounded_record(raw, limits)
        require(name not in index, 'DUPLICATE_BASE_RECORD_NAME', name)
        index[name] = (begin, end, hashlib.sha256(raw).digest())
    return index


class ObjectScanner:
    def __init__(self):
        self.depth = 0
        self.string = False
        self.escape = False

    def end(self, piece):
        for i, byte in enumerate(piece):
            if self.string:
                if self.escape:
                    self.escape = False
                elif byte == 92:
                    self.escape = True
                elif byte == 34:
                    self.string = False
            elif byte == 34:
                self.string = True
            elif byte == 123:
                self.depth += 1
            elif byte == 125:
                self.depth -= 1
                require(self.depth >= 0, 'TARGET_RECORD_BRACE_SHAPE')
                if self.depth == 0:
                    return i+1
        return None


def target_spans(handle, limits):
    """Stream exact literal gaps and bounded object bytes; no target mmap."""
    top_names = []
    in_declarations = False
    scanner = None
    buffer = bytearray()
    for_line_count = 0
    while line := handle.readline(limits.line_bytes+1):
        require(len(line) <= limits.line_bytes, 'TARGET_LINE_LIMIT')
        for_line_count += 1
        if scanner is None:
            top = TOP.match(line)
            if top:
                name = top.group(1).decode('ascii')
                require(len(top_names) < len(TOP_FIELDS) and name == TOP_FIELDS[len(top_names)],
                        'TARGET_TOP_FIELD_SHAPE')
                top_names.append(name)
                in_declarations = name == 'declarations'
            match = RECORD_START.match(line) if in_declarations else None
            if match:
                begin = line.find(b'{', match.start(), match.end())
                yield 'L', line[:begin]
                scanner = ObjectScanner()
                piece = line[begin:]
            else:
                yield 'L', line
                continue
        else:
            piece = line
        end = scanner.end(piece)
        part = piece if end is None else piece[:end]
        require(len(buffer)+len(part) <= limits.record_bytes, 'TARGET_RECORD_BYTES_LIMIT')
        buffer.extend(part)
        if end is not None:
            yield 'R', bytes(buffer)
            buffer.clear()
            scanner = None
            yield 'L', piece[end:]
    require(scanner is None and not buffer, 'TARGET_UNFINISHED_RECORD')
    require(tuple(top_names) == TOP_FIELDS, 'TARGET_TOP_FIELD_SHAPE')


class CappedGzipSink:
    def __init__(self, file, plan):
        self.file = file
        self.plan = plan
        self.position = 0
        self.digest = hashlib.sha256()

    def write(self, raw):
        require(self.position+len(raw) <= self.plan.limits.patch_gzip_bytes, 'PATCH_GZIP_LIMIT')
        reserve_scratch(self.plan, len(raw))
        written = self.file.write(raw)
        require(written == len(raw), 'SHORT_PATCH_WRITE')
        self.position += len(raw)
        self.digest.update(raw)
        return written

    def flush(self):
        self.file.flush()


class Builder:
    def __init__(self, stream, plan):
        self.stream = stream
        self.plan = plan
        self.raw_position = self.decoded_position = 0
        self.raw_digest = hashlib.sha256()
        self.operations = self.copies = self.literals = 0
        self.literal = bytearray()
        self.copy_pending = None
        self.source_cursor = 0
        self.emit(MAGIC+bytes.fromhex(plan.base_raw.sha256)+bytes.fromhex(plan.target_raw.sha256)
                  +U64.pack(plan.target_raw.bytes))

    def emit(self, piece):
        require(self.raw_position+len(piece) <= self.plan.limits.patch_raw_bytes, 'PATCH_RAW_LIMIT')
        self.stream.write(piece)
        self.raw_digest.update(piece)
        self.raw_position += len(piece)

    def operation(self):
        require(self.operations < self.plan.limits.operation_count, 'PATCH_OPERATION_LIMIT')
        self.operations += 1

    def flush_literal(self):
        if self.literal:
            self.operation()
            self.emit(b'L'+U64.pack(len(self.literal)))
            for i in range(0, len(self.literal), CHUNK):
                self.emit(self.literal[i:i+CHUNK])
            self.literals += 1
            self.literal.clear()

    def flush_copy(self):
        if self.copy_pending is not None:
            self.operation()
            start, length = self.copy_pending
            self.emit(b'C'+U64.pack(start)+U64.pack(length))
            self.copies += 1
            self.copy_pending = None

    def literal_piece(self, piece):
        require(self.decoded_position+len(piece) <= self.plan.target_raw.bytes, 'TARGET_RANGE')
        self.decoded_position += len(piece)
        self.flush_copy()
        view = memoryview(piece)
        offset = 0
        while offset < len(piece):
            room = self.plan.limits.literal_buffer_bytes-len(self.literal)
            if not room:
                self.flush_literal()
                room = self.plan.limits.literal_buffer_bytes
            length = min(room, len(piece)-offset)
            self.literal.extend(view[offset:offset+length])
            offset += length

    def copy_piece(self, start, length):
        require(length > 0 and start >= self.source_cursor and start+length <= self.plan.base_raw.bytes,
                'COPY_RANGE')
        require(self.decoded_position+length <= self.plan.target_raw.bytes, 'TARGET_RANGE')
        self.decoded_position += length
        self.flush_literal()
        if self.copy_pending is not None and sum(self.copy_pending) == start:
            self.copy_pending = (self.copy_pending[0], self.copy_pending[1]+length)
        else:
            self.flush_copy()
            self.copy_pending = (start, length)
        self.source_cursor = start+length

    def finish(self):
        self.flush_copy()
        self.flush_literal()
        require(self.decoded_position == self.plan.target_raw.bytes, 'TARGET_PARTITION_SIZE')


def produce(plan, output_gzip):
    plan.validate()
    output_gzip = new_output_path(plan, output_gzip)
    require(Path(output_gzip).resolve() not in {Path(p.path).resolve() for p in
            (plan.base_raw, plan.base_gzip, plan.target_raw)}, 'OUTPUT_INPUT_ALIAS')
    reserve_scratch(plan, plan.limits.patch_gzip_bytes)
    counts = {'base_records': 0, 'target_records': 0, 'exact_copied_records': 0,
              'changed_records': 0, 'new_records': 0, 'backward_exact_records_literal': 0}
    target_digest = hashlib.sha256()
    seen = set()
    with ExitStack() as stack:
        raw_base = authenticate_file(stack, plan.base_raw)
        base_gzip = authenticate_file(stack, plan.base_gzip)
        target = authenticate_file(stack, plan.target_raw)
        verify_base_gzip(raw_base, base_gzip, plan.base_raw)
        base = stack.enter_context(mmap.mmap(raw_base.fileno(), 0, access=mmap.ACCESS_READ))
        index = base_index(base, plan.limits)
        counts['base_records'] = len(index)
        output = stack.enter_context(output_gzip.open('xb'))
        sink = CappedGzipSink(output, plan)
        compressed = stack.enter_context(gzip.GzipFile(fileobj=sink, mode='wb',
                                                       filename='', mtime=0, compresslevel=6))
        builder = Builder(compressed, plan)
        for kind, piece in target_spans(target, plan.limits):
            target_digest.update(piece)
            if kind == 'L':
                builder.literal_piece(piece)
                continue
            require(counts['target_records'] < plan.limits.record_count, 'TARGET_RECORD_COUNT_LIMIT')
            name = bounded_record(piece, plan.limits)
            require(name not in seen, 'DUPLICATE_TARGET_RECORD_NAME', name)
            seen.add(name)
            counts['target_records'] += 1
            original = index.get(name)
            exact = original is not None and original[2] == hashlib.sha256(piece).digest() and \
                base[original[0]:original[1]] == piece
            if exact and original[0] >= builder.source_cursor:
                builder.copy_piece(original[0], original[1]-original[0])
                counts['exact_copied_records'] += 1
            else:
                builder.literal_piece(piece)
                if exact:
                    counts['backward_exact_records_literal'] += 1
                elif original is not None:
                    counts['changed_records'] += 1
                else:
                    counts['new_records'] += 1
        require(target_digest.hexdigest() == plan.target_raw.sha256, 'TARGET_STREAM_HASH')
        builder.finish()
        compressed.close()
        output.flush()
        patch = PatchPin(FilePin(str(output_gzip), sink.position, sink.digest.hexdigest()),
                         builder.raw_position, builder.raw_digest.hexdigest(),
                         plan.base_raw.bytes, plan.base_raw.sha256,
                         plan.target_raw.bytes, plan.target_raw.sha256,
                         builder.operations, builder.copies, builder.literals,
                         builder.decoded_position, True)
        patch.validate(plan)
    return patch, counts


class RawPatchReader:
    def __init__(self, compressed, pin):
        self.stream = compressed
        self.pin = pin
        self.position = 0
        self.digest = hashlib.sha256()

    def exact(self, length):
        require(0 <= length <= CHUNK and self.position+length <= self.pin.raw_bytes, 'PATCH_READ_RANGE')
        piece = self.stream.read(length)
        require(len(piece) == length, 'PATCH_TRUNCATED')
        self.position += length
        self.digest.update(piece)
        return piece

    def finish(self):
        require(self.position == self.pin.raw_bytes, 'PATCH_RAW_SIZE')
        require(self.stream.read(1) == b'', 'PATCH_RAW_TRAILING_BYTES')
        require(self.digest.hexdigest() == self.pin.raw_sha256, 'PATCH_RAW_HASH')


def patch_operations(reader, plan, pin):
    require(reader.exact(len(MAGIC)) == MAGIC, 'PATCH_MAGIC')
    require(reader.exact(32).hex() == plan.base_raw.sha256, 'PATCH_HEADER_BASE_HASH')
    require(reader.exact(32).hex() == plan.target_raw.sha256, 'PATCH_HEADER_TARGET_HASH')
    require(U64.unpack(reader.exact(8))[0] == plan.target_raw.bytes, 'PATCH_HEADER_TARGET_SIZE')
    position = source_cursor = operations = copies = literals = 0
    while reader.position < pin.raw_bytes:
        require(operations < pin.operations and operations < plan.limits.operation_count, 'PATCH_OPERATION_COUNT')
        tag = reader.exact(1)
        operations += 1
        if tag == b'C':
            start = U64.unpack(reader.exact(8))[0]
            length = U64.unpack(reader.exact(8))[0]
            require(length > 0 and start >= source_cursor and start+length <= plan.base_raw.bytes, 'COPY_RANGE')
            require(position+length <= plan.target_raw.bytes, 'TARGET_RANGE')
            copies += 1
            require(copies <= pin.copies and copies <= plan.limits.record_count, 'PATCH_COPY_COUNT')
            source_cursor = start+length
            position += length
            yield 'C', (start, length)
        elif tag == b'L':
            length = U64.unpack(reader.exact(8))[0]
            # This target range check occurs before reading, allocating, or
            # emitting any literal payload and before any restore output.
            require(length > 0 and position+length <= plan.target_raw.bytes, 'TARGET_RANGE')
            require(reader.position+length <= pin.raw_bytes, 'LITERAL_PAYLOAD_RANGE')
            literals += 1
            require(literals <= pin.literals, 'PATCH_LITERAL_COUNT')
            position += length
            remaining = length
            while remaining:
                piece = reader.exact(min(CHUNK, remaining))
                remaining -= len(piece)
                yield 'L', piece
        else:
            raise CodecRefusal('UNKNOWN_PATCH_OPCODE')
    require((operations, copies, literals, position) ==
            (pin.operations, pin.copies, pin.literals, pin.decoded_bytes), 'PATCH_PIN_COUNT_MISMATCH')
    reader.finish()


def preflight_patch(handle, plan, pin):
    handle.seek(0)
    with gzip.GzipFile(fileobj=handle, mode='rb') as compressed:
        reader = RawPatchReader(compressed, pin)
        for _kind, _piece in patch_operations(reader, plan, pin):
            pass
    handle.seek(0)


class BaseCursor:
    def __init__(self, compressed, raw, pin):
        self.compressed = compressed
        self.raw = raw
        self.pin = pin
        self.position = 0
        self.digest = hashlib.sha256()

    def read(self, length):
        require(0 < length <= CHUNK and self.position+length <= self.pin.bytes, 'BASE_DECODE_RANGE')
        piece = self.compressed.read(length)
        require(len(piece) == length, 'BASE_GZIP_TRUNCATED')
        # Each decompressed base piece is compared with its authenticated raw
        # counterpart before any copied bytes can reach the target sink.
        require(self.raw.read(length) == piece, 'BASE_GZIP_RAW_BYTE_MISMATCH')
        self.digest.update(piece)
        self.position += length
        return piece

    def skip_to(self, start):
        require(self.position <= start <= self.pin.bytes, 'BASE_CURSOR_NONMONOTONE')
        while self.position < start:
            self.read(min(CHUNK, start-self.position))

    def finish(self):
        self.skip_to(self.pin.bytes)
        require(self.compressed.read(1) == b'', 'BASE_GZIP_DECODED_SIZE')
        require(self.raw.read(1) == b'', 'BASE_RAW_TRAILING_BYTES')
        require(self.digest.hexdigest() == self.pin.sha256, 'BASE_GZIP_RAW_HASH')


class TargetSink:
    def __init__(self, reference, pin, output=None, on_piece=None):
        self.reference = reference
        self.pin = pin
        self.output = output
        self.on_piece = on_piece
        self.position = 0
        self.digest = hashlib.sha256()
        self.pieces = 0

    def consume(self, piece):
        require(self.position+len(piece) <= self.pin.bytes, 'TARGET_RANGE')
        # Compare before callback/output, so a wrong decoded piece is never
        # written to the optional output or exposed as a matching target.
        require(self.reference.read(len(piece)) == piece, 'TARGET_BYTE_COMPARISON')
        if self.output is not None:
            require(self.output.write(piece) == len(piece), 'SHORT_RESTORE_WRITE')
        if self.on_piece is not None:
            self.on_piece(piece)
        self.digest.update(piece)
        self.position += len(piece)
        self.pieces += 1

    def finish(self):
        require(self.position == self.pin.bytes and self.reference.read(1) == b'', 'TARGET_DECODED_SIZE')
        require(self.digest.hexdigest() == self.pin.sha256, 'TARGET_DECODED_HASH')


def restore(plan, pin, output=None, on_piece=None):
    plan.validate()
    pin.validate(plan)
    if output is not None:
        output = new_output_path(plan, output)
        require(plan.target_raw.bytes <= plan.limits.optional_output_bytes, 'OPTIONAL_OUTPUT_LIMIT')
        reserve_scratch(plan, plan.target_raw.bytes)
    with ExitStack() as stack:
        # Authenticate compressed patch and complete raw/header/op/range pins
        # before even opening an optional output or invoking any callback.
        patch_file = authenticate_file(stack, pin.gzip_file)
        preflight_patch(patch_file, plan, pin)
        raw_base = authenticate_file(stack, plan.base_raw)
        base_gzip_file = authenticate_file(stack, plan.base_gzip)
        target = authenticate_file(stack, plan.target_raw)
        restored = stack.enter_context(output.open('xb')) if output is not None else None
        base_gzip = stack.enter_context(gzip.GzipFile(fileobj=base_gzip_file, mode='rb'))
        base_cursor = BaseCursor(base_gzip, raw_base, plan.base_raw)
        sink = TargetSink(target, plan.target_raw, restored, on_piece)
        with gzip.GzipFile(fileobj=patch_file, mode='rb') as compressed:
            reader = RawPatchReader(compressed, pin)
            for kind, piece in patch_operations(reader, plan, pin):
                if kind == 'L':
                    sink.consume(piece)
                else:
                    start, remaining = piece
                    base_cursor.skip_to(start)
                    while remaining:
                        copied = base_cursor.read(min(CHUNK, remaining))
                        sink.consume(copied)
                        remaining -= len(copied)
        sink.finish()
        base_cursor.finish()
        if restored is not None:
            restored.flush()
    return {
        'schema': 'audit_copy_literal_restore_result_v1',
        'status': 'PASS_PINNED_SAVED_BYTE_RESTORATION',
        'base_raw_sha256': plan.base_raw.sha256, 'base_raw_bytes_hashed': base_cursor.position,
        'base_gzip_decompression_passes': 1,
        'target_sha256': sink.digest.hexdigest(), 'target_bytes_compared': sink.position,
        'byte_for_byte_equal': True, 'decoded_pieces': sink.pieces,
        'patch_preflight_completed_before_output': True, 'output_file': str(output) if output else None,
        'new_large_raw_base_created': False, 'second_target_artifact_created': output is not None,
        'mathematical_acceptance_claim': False, 'prospective_union_created': False,
    }


def encode_json(value):
    return (json.dumps(value, sort_keys=True, indent=2)+'\n').encode('ascii')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='operation', required=True)
    make = sub.add_parser('produce')
    make.add_argument('--plan', type=Path, required=True)
    make.add_argument('--gzip-output', type=Path, required=True)
    make.add_argument('--pin-output', type=Path, required=True)
    check = sub.add_parser('restore')
    check.add_argument('--plan', type=Path, required=True)
    check.add_argument('--patch-pin', type=Path, required=True)
    check.add_argument('--output', type=Path)
    args = parser.parse_args()
    enforce_address_space_limit()
    with args.plan.open('rb') as f:
        plan = Plan.decode(parse_small_json(f.read(65537)))
    if args.operation == 'produce':
        pin_output = new_output_path(plan, args.pin_output)
        require(pin_output.resolve() != args.gzip_output.resolve(), 'PATCH_PIN_OUTPUT_ALIAS')
        patch, counts = produce(plan, args.gzip_output)
        body = encode_json(patch.encode())
        reserve_scratch(plan, len(body))
        with pin_output.open('xb') as f:
            f.write(body)
        result = {'status': 'PINNED_PATCH_CREATED', 'patch_pin': patch.encode(), 'records': counts,
                  'mathematical_acceptance_claim': False, 'prospective_union_created': False}
    else:
        with args.patch_pin.open('rb') as f:
            pin = PatchPin.decode(parse_small_json(f.read(65537)))
        result = restore(plan, pin, args.output)
    result['max_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result['created_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (CodecRefusal, OSError, EOFError, gzip.BadGzipFile, MemoryError) as error:
        print(json.dumps({'status': 'CODEC_REFUSED_OR_EXECUTION_FAILED',
                          'error': str(error), 'mathematical_acceptance_claim': False,
                          'prospective_union_created': False}, sort_keys=True))
        raise SystemExit(1)
