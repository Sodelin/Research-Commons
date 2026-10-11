"""Portable streaming restoration of a pinned saved-audit C/L patch.

Required byte inputs are only the compressed base and compressed patch. Raw
base/target identities are pathless expected lengths/hashes. Optional raw
comparison references are explicit and never needed by the restorer. Streamed
pieces and a partial optional output are provisional until both final raw
hashes pass. This is byte storage, not a mathematical audit or compiler.
"""
from __future__ import annotations

import argparse
from contextlib import ExitStack
from dataclasses import asdict, dataclass
import datetime
import gzip
import hashlib
from pathlib import Path
import resource
import sys
import types

CODEC_SOURCE = Path(__file__).with_name('audit_copy_literal_codec.py')
CODEC_SHA256 = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'
CODEC_SOURCE_MAX_BYTES = 1024 * 1024
_CODEC = None


class PortableRefusal(ValueError):
    def __init__(self, reason, detail=''):
        self.reason = reason
        self.detail = detail
        super().__init__(reason + (': ' + detail if detail else ''))


def pinned_codec():
    """Authenticate, then execute the exact captured parser/provider bytes.

    The accepted codec is unchanged. Its old restore/producer are never called
    here. Executing authenticated bytes avoids a mutable-path import reread.
    """
    global _CODEC
    try:
        with CODEC_SOURCE.open('rb') as source:
            raw = source.read(CODEC_SOURCE_MAX_BYTES+1)
    except OSError as error:
        raise PortableRefusal('PINNED_CODEC_UNAVAILABLE', str(error)) from error
    if len(raw) > CODEC_SOURCE_MAX_BYTES:
        raise PortableRefusal('PINNED_CODEC_SIZE_LIMIT')
    if hashlib.sha256(raw).hexdigest() != CODEC_SHA256:
        raise PortableRefusal('PINNED_CODEC_HASH')
    if _CODEC is None:
        name = 'authenticated_audit_copy_literal_'+CODEC_SHA256
        module = types.ModuleType(name)
        module.__file__ = str(CODEC_SOURCE)
        sys.modules[name] = module
        exec(compile(raw, str(CODEC_SOURCE), 'exec'), module.__dict__)
        _CODEC = module
    return _CODEC


@dataclass(frozen=True)
class RawIdentity:
    bytes: int
    sha256: str

    def validate(self, cap):
        codec = pinned_codec()
        codec.require(codec.natural(self.bytes) and 0 < self.bytes <= cap,
                      'RAW_IDENTITY_SIZE_LIMIT')
        codec.require(codec.digest_shape(self.sha256), 'INVALID_RAW_IDENTITY_DIGEST')

    @classmethod
    def decode(cls, value):
        codec = pinned_codec()
        codec.require(isinstance(value, dict) and set(value) == {'bytes', 'sha256'},
                      'INVALID_RAW_IDENTITY_FIELDS')
        return cls(**value)


@dataclass(frozen=True)
class PortablePlan:
    base_gzip: object
    base_identity: RawIdentity
    target_identity: RawIdentity
    scratch_root: str
    limits: object

    # These pathless aliases supply only the identities required by the frozen
    # patch parser. No fake raw filename or original Plan/restore is involved.
    @property
    def base_raw(self):
        return self.base_identity

    @property
    def target_raw(self):
        return self.target_identity

    def validate(self):
        codec = pinned_codec()
        codec.require(isinstance(self.base_gzip, codec.FilePin), 'INVALID_BASE_GZIP_PIN_TYPE')
        codec.require(isinstance(self.limits, codec.Limits), 'INVALID_LIMIT_TYPE')
        self.base_gzip.validate()
        self.limits.validate()
        self.base_identity.validate(self.limits.raw_file_bytes)
        self.target_identity.validate(self.limits.raw_file_bytes)
        codec.require(0 < self.base_gzip.bytes <= self.limits.raw_file_bytes,
                      'BASE_GZIP_SIZE_LIMIT')
        codec.require(isinstance(self.scratch_root, str) and self.scratch_root != '',
                      'INVALID_SCRATCH_ROOT')
        codec.require(Path(self.scratch_root).is_dir(), 'SCRATCH_ROOT_NOT_PRESENT')

    def encode(self):
        return {'schema': 'audit_portable_restore_plan_v1', **asdict(self)}

    @classmethod
    def decode(cls, value):
        codec = pinned_codec()
        fields = {'schema', 'base_gzip', 'base_identity', 'target_identity',
                  'scratch_root', 'limits'}
        codec.require(isinstance(value, dict) and set(value) == fields,
                      'INVALID_PORTABLE_PLAN_FIELDS')
        codec.require(value['schema'] == 'audit_portable_restore_plan_v1',
                      'INVALID_PORTABLE_PLAN_SCHEMA')
        codec.require(isinstance(value['limits'], dict) and
                      set(value['limits']) == set(asdict(codec.Limits())),
                      'INVALID_LIMIT_FIELDS')
        result = cls(codec.FilePin.decode(value['base_gzip']),
                     RawIdentity.decode(value['base_identity']),
                     RawIdentity.decode(value['target_identity']),
                     value['scratch_root'], codec.Limits(**value['limits']))
        result.validate()
        return result


def optional_reference(codec, stack, pin, identity):
    if pin is None:
        return None
    codec.require(isinstance(pin, codec.FilePin), 'INVALID_COMPARISON_PIN_TYPE')
    pin.validate()
    codec.require((pin.bytes, pin.sha256) == (identity.bytes, identity.sha256),
                  'COMPARISON_REFERENCE_BINDING')
    return codec.authenticate_file(stack, pin)


class PortableBaseCursor:
    def __init__(self, codec, compressed, identity, comparison=None):
        self.codec = codec
        self.compressed = compressed
        self.identity = identity
        self.comparison = comparison
        self.position = 0
        self.digest = hashlib.sha256()

    def read(self, length):
        self.codec.require(0 < length <= self.codec.CHUNK and
                           self.position+length <= self.identity.bytes,
                           'BASE_DECODE_RANGE')
        piece = self.compressed.read(length)
        self.codec.require(len(piece) == length, 'BASE_GZIP_TRUNCATED')
        if self.comparison is not None:
            self.codec.require(self.comparison.read(length) == piece,
                               'BASE_OPTIONAL_BYTE_COMPARISON')
        self.digest.update(piece)
        self.position += length
        return piece

    def skip_to(self, start):
        self.codec.require(self.position <= start <= self.identity.bytes,
                           'BASE_CURSOR_NONMONOTONE')
        while self.position < start:
            self.read(min(self.codec.CHUNK, start-self.position))

    def finish(self):
        self.skip_to(self.identity.bytes)
        self.codec.require(self.compressed.read(1) == b'', 'BASE_GZIP_DECODED_SIZE')
        if self.comparison is not None:
            self.codec.require(self.comparison.read(1) == b'', 'BASE_COMPARISON_TRAILING_BYTES')
        self.codec.require(self.digest.hexdigest() == self.identity.sha256,
                           'BASE_GZIP_RAW_HASH')


class PortableTargetSink:
    def __init__(self, codec, identity, comparison=None, output=None, on_piece=None):
        self.codec = codec
        self.identity = identity
        self.comparison = comparison
        self.output = output
        self.on_piece = on_piece
        self.position = 0
        self.digest = hashlib.sha256()
        self.pieces = 0

    def consume(self, piece):
        self.codec.require(0 < len(piece) <= self.codec.CHUNK and
                           self.position+len(piece) <= self.identity.bytes, 'TARGET_RANGE')
        if self.comparison is not None:
            self.codec.require(self.comparison.read(len(piece)) == piece,
                               'TARGET_OPTIONAL_BYTE_COMPARISON')
        if self.output is not None:
            self.codec.require(self.output.write(piece) == len(piece), 'SHORT_RESTORE_WRITE')
        if self.on_piece is not None:
            self.on_piece(piece)
        self.digest.update(piece)
        self.position += len(piece)
        self.pieces += 1

    def finish(self):
        self.codec.require(self.position == self.identity.bytes, 'TARGET_DECODED_SIZE')
        if self.comparison is not None:
            self.codec.require(self.comparison.read(1) == b'', 'TARGET_COMPARISON_TRAILING_BYTES')
        self.codec.require(self.digest.hexdigest() == self.identity.sha256, 'TARGET_DECODED_HASH')


def restore(plan, pin, *, output=None, on_piece=None,
            compare_base_raw=None, compare_target_raw=None):
    """Restore only pinned compressed inputs; compare references are optional.

    Callback chunks are bounded but provisional until this function returns
    success. Any partial create-new file is preserved on failure, never labeled
    verified. Direct library callers must run in the approved capped worker.
    """
    codec = pinned_codec()
    plan.validate()
    codec.require(isinstance(pin, codec.PatchPin), 'INVALID_PATCH_PIN_TYPE')
    pin.validate(plan)
    if output is not None:
        output = codec.new_output_path(plan, output)
        aliases = [plan.base_gzip.path, pin.gzip_file.path]
        aliases += [p.path for p in (compare_base_raw, compare_target_raw) if p is not None]
        codec.require(output.resolve() not in {Path(p).resolve() for p in aliases}, 'OUTPUT_INPUT_ALIAS')
        codec.require(plan.target_identity.bytes <= plan.limits.optional_output_bytes,
                      'OPTIONAL_OUTPUT_LIMIT')
        codec.reserve_scratch(plan, plan.target_identity.bytes)
    with ExitStack() as stack:
        # Both complete compressed identities and the complete decoded patch
        # header/op/count/range/hash preflight pass before output or callbacks.
        patch_file = codec.authenticate_file(stack, pin.gzip_file)
        base_file = codec.authenticate_file(stack, plan.base_gzip)
        codec.preflight_patch(patch_file, plan, pin)
        base_comparison = optional_reference(codec, stack, compare_base_raw, plan.base_identity)
        target_comparison = optional_reference(codec, stack, compare_target_raw, plan.target_identity)
        restored = stack.enter_context(output.open('xb')) if output is not None else None
        base_stream = stack.enter_context(gzip.GzipFile(fileobj=base_file, mode='rb'))
        cursor = PortableBaseCursor(codec, base_stream, plan.base_identity, base_comparison)
        sink = PortableTargetSink(codec, plan.target_identity, target_comparison, restored, on_piece)
        with gzip.GzipFile(fileobj=patch_file, mode='rb') as compressed:
            reader = codec.RawPatchReader(compressed, pin)
            for kind, piece in codec.patch_operations(reader, plan, pin):
                if kind == 'L':
                    sink.consume(piece)
                else:
                    start, remaining = piece
                    cursor.skip_to(start)
                    while remaining:
                        copied = cursor.read(min(codec.CHUNK, remaining))
                        sink.consume(copied)
                        remaining -= len(copied)
        # Includes all uncopied base bytes, not just copy spans. No successful
        # return can occur before BOTH expected uncompressed identities pass.
        cursor.finish()
        sink.finish()
        if restored is not None:
            restored.flush()
    return {
        'schema': 'audit_portable_restore_result_v1',
        'status': 'PASS_PINNED_PORTABLE_BYTE_RESTORATION',
        'codec_source_sha256': CODEC_SHA256,
        'base_gzip_sha256': plan.base_gzip.sha256,
        'base_raw_sha256': cursor.digest.hexdigest(),
        'base_raw_bytes_hashed': cursor.position,
        'base_gzip_decompression_passes': 1,
        'target_sha256': sink.digest.hexdigest(),
        'target_bytes_hashed': sink.position,
        'decoded_pieces': sink.pieces,
        'compressed_inputs_authenticated_before_output': True,
        'patch_preflight_completed_before_output': True,
        'final_base_and_target_hashes_checked': True,
        'required_raw_reference_files': 0,
        'optional_base_reference_checked': compare_base_raw is not None,
        'optional_target_reference_checked': compare_target_raw is not None,
        'output_file': str(output) if output is not None else None,
        'new_large_raw_base_created': False,
        'second_target_artifact_created': output is not None,
        'mathematical_acceptance_claim': False,
        'prospective_union_created': False,
    }


def read_small(codec, path):
    with path.open('rb') as f:
        return codec.parse_small_json(f.read(65537))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--patch-pin', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--compare-base-pin', type=Path)
    parser.add_argument('--compare-target-pin', type=Path)
    args = parser.parse_args()
    codec = pinned_codec()
    codec.enforce_address_space_limit()
    plan = PortablePlan.decode(read_small(codec, args.plan))
    patch = codec.PatchPin.decode(read_small(codec, args.patch_pin))
    base_compare = codec.FilePin.decode(read_small(codec, args.compare_base_pin)) \
        if args.compare_base_pin is not None else None
    target_compare = codec.FilePin.decode(read_small(codec, args.compare_target_pin)) \
        if args.compare_target_pin is not None else None
    result = restore(plan, patch, output=args.output,
                     compare_base_raw=base_compare, compare_target_raw=target_compare)
    result['max_rss_kib'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    result['created_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(codec.encode_json(result).decode('ascii'), end='')


if __name__ == '__main__':
    try:
        main()
    except (PortableRefusal, ValueError, OSError, EOFError, gzip.BadGzipFile, MemoryError) as error:
        import json
        print(json.dumps({'schema': 'audit_portable_restore_result_v1',
                          'status': 'PORTABLE_RESTORE_REFUSED_OR_FAILED',
                          'error': str(error), 'mathematical_acceptance_claim': False,
                          'prospective_union_created': False}, sort_keys=True))
        raise SystemExit(1)
