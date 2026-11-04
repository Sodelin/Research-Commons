"""Shared RAM capture and existing-codec recovery for the two public runners.

This is a client launcher, not a Linux compiler/controller admission layer.
It creates no identity and provides no plaintext fallback or automatic retry.
"""
import base64
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zlib

CODEC_INPUT_BOUND = 900000
ORIGINAL_RECORD_BOUND = 12 * 1024 * 1024
PASS = 'PASS_REMOTE_LEAN_CHECK'
REJECTED = 'REJECTED_REMOTE_LEAN_CHECK'
MEMORY_SOURCE_BOUND = 1048576
MEMORY_AUDIT_BOUND = 65536
DOCUMENT_SENTINEL = 'LEAN_E2E_DOCUMENT_FINISHED_20261021'


class CaptureRefused(Exception):
    """Fixed public reason; never contains a runtime payload."""


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def strict_json(raw):
    def reject_constant(_):
        raise ValueError('NONFINITE_JSON')
    return json.loads(raw, parse_constant=reject_constant)


def verify_codec(codec, expected):
    if (not codec.is_absolute() or codec.is_symlink() or not codec.is_file()
            or sha256(codec.read_bytes()) != expected):
        raise CaptureRefused('VERIFIED_EXISTING_RECORD_CODEC_REQUIRED')


def packet_snapshot(root, required):
    """Verify every listed body and retain the manifest itself for the after gate."""
    if (root / 'SOURCE-FILES.json').is_symlink():
        raise CaptureRefused('PUBLIC_SOURCE_SYMLINK_REFUSED')
    manifest = (root / 'SOURCE-FILES.json').read_bytes()
    rows = strict_json(manifest)['files']
    identities = {}
    for row in rows:
        rel = PurePosixPath(row['path'])
        if (rel.is_absolute() or '..' in rel.parts or str(rel) != row['path']
                or not rel.parts or row['path'] in identities):
            raise CaptureRefused('INVALID_SOURCE_INVENTORY')
        path = root.joinpath(*rel.parts)
        if any(root.joinpath(*rel.parts[:i]).is_symlink()
               for i in range(1, len(rel.parts) + 1)):
            raise CaptureRefused('PUBLIC_SOURCE_SYMLINK_REFUSED')
        raw = path.read_bytes()
        identity = {'bytes': len(raw), 'sha256': sha256(raw)}
        if identity != {'bytes': row['bytes'], 'sha256': row['sha256']}:
            raise CaptureRefused('PUBLIC_SOURCE_CHANGED')
        identities[row['path']] = identity
    if not set(required).issubset(identities):
        raise CaptureRefused('REQUIRED_SOURCE_NOT_IN_INVENTORY')
    return {'manifest_sha256': sha256(manifest), 'files': identities}


def capture_process(command, timeout=130, *, input_bytes=None):
    """Keep even timeout partial pipes in RAM; never restart the child."""
    try:
        arguments = dict(stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         timeout=timeout, check=False)
        if input_bytes is not None:
            arguments['input'] = input_bytes
        process = subprocess.run(command, **arguments)
        return {'stdout': process.stdout, 'stderr': process.stderr,
                'exit': process.returncode, 'failure': None}
    except subprocess.TimeoutExpired as error:
        return {'stdout': error.stdout or b'', 'stderr': error.stderr or b'',
                'exit': None, 'failure': 'PARENT_CAPTURE_TIMEOUT'}
    except OSError:
        return {'stdout': b'', 'stderr': b'', 'exit': None,
                'failure': 'CLIENT_PROCESS_UNAVAILABLE'}


def disposition(capture, source_identity, audits, unchanged):
    """A status word alone never establishes an accepted check or control."""
    if capture['failure']:
        return 'UNVERIFIED', capture['failure']
    if not unchanged:
        return 'UNVERIFIED', 'PUBLIC_SOURCE_CHANGED_DURING_CAPTURE'
    try:
        result = strict_json(capture['stdout'])
        if not isinstance(result, dict):
            raise ValueError('NOT_OBJECT')
        status = result.get('status')
        if status not in (PASS, REJECTED):
            return 'UNVERIFIED', 'CLIENT_UNVERIFIED'
        wanted_exit = 0 if status == PASS else 2
        if capture['exit'] != wanted_exit:
            return 'UNVERIFIED', 'CLIENT_EXIT_STATUS_MISMATCH'
        if (result.get('source_sha256') != source_identity['sha256']
                or result.get('source_bytes') != source_identity['bytes']
                or result.get('audits') != audits):
            return 'UNVERIFIED', 'CLIENT_SOURCE_OR_AUDIT_BINDING_MISMATCH'
        if (not isinstance(result.get('before'), dict) or not result['before']
                or result.get('after') != result['before']):
            return 'UNVERIFIED', 'HOST_VERSION_BINDING_MISMATCH'
        audit_rows = result.get('audit_rows')
        if (not isinstance(audit_rows, list)
                or [r.get('name') for r in audit_rows] != audits):
            return 'UNVERIFIED', 'CLIENT_AUDIT_ROWS_MISMATCH'
        if status == PASS and (result.get('errors') != []
                or not all(r.get('clean') is True for r in audit_rows)):
            return 'UNVERIFIED', 'CLIENT_PASS_EVIDENCE_MISMATCH'
        return status, None
    except (ValueError, UnicodeError, TypeError, AttributeError, KeyError, RecursionError):
        return 'UNVERIFIED', 'CLIENT_RESULT_UNREADABLE'


def pack_record(value):
    raw = json.dumps(value, sort_keys=True, allow_nan=False).encode()
    if len(raw) > ORIGINAL_RECORD_BOUND:
        raise CaptureRefused('ORIGINAL_RECORD_RAM_BOUND')
    if len(raw) <= CODEC_INPUT_BOUND:
        return raw
    compressed = zlib.compress(raw, 6)
    if zlib.decompress(compressed) != raw:
        raise CaptureRefused('RECORD_PACKING_ROUNDTRIP_FAILED')
    packed = json.dumps({'record_encoding': 'zlib-json-v1',
        'uncompressed_bytes': len(raw), 'uncompressed_sha256': sha256(raw),
        'zlib_base64': base64.b64encode(compressed).decode()},
        sort_keys=True).encode()
    if len(packed) > CODEC_INPUT_BOUND:
        raise CaptureRefused('PACKED_RECORD_CODEC_BOUND')
    return packed


def seal_record(codec, expected, payload):
    verify_codec(codec, expected)
    try:
        sealed = subprocess.run([str(codec), 'seal-stdin'], input=payload,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=40,
            check=False)
    except (OSError, subprocess.TimeoutExpired):
        raise CaptureRefused('RECORD_ENCRYPTION_UNCONFIRMED_NO_RETRY') from None
    if sealed.returncode:
        raise CaptureRefused('RECORD_ENCRYPTION_REFUSED_NO_PLAINTEXT_FALLBACK')
    try:
        receipt = strict_json(sealed.stdout)
        path = Path(receipt['record'])
        if (receipt.get('state') != 'ENCRYPTED_AND_READ_BACK'
                or not path.is_absolute() or path.is_symlink() or not path.is_file()):
            raise ValueError('RECEIPT')
        ciphertext = path.read_bytes()
        if (len(ciphertext) != receipt['ciphertext_bytes']
                or sha256(ciphertext) != receipt['ciphertext_sha256']):
            raise ValueError('READBACK')
        verify_codec(codec, expected)
        return {k: receipt[k] for k in
                ('state', 'record', 'ciphertext_bytes', 'ciphertext_sha256')}
    except (ValueError, UnicodeError, TypeError, KeyError, OSError):
        raise CaptureRefused('ENCRYPTED_READBACK_UNCONFIRMED') from None


def seal_with_tombstone(value, tombstone, codec, codec_sha256):
    """Reuse the exact codec/packing policy for request and result recovery."""
    complete, reason = True, None
    try:
        payload = pack_record(value)
    except CaptureRefused as error:
        complete, reason = False, str(error)
        payload = pack_record(dict(tombstone, status='UNVERIFIED', reason=reason))
    return complete, reason, seal_record(codec, codec_sha256, payload)


def run_case(root, case, source, audits, entry, core, codec, codec_sha256, runner,
             *, process_timeout=130):
    """Seal original bytes before emitting a small, fixed-field projection."""
    try:
        if type(process_timeout) is not int or not 1 <= process_timeout <= 370:
            raise CaptureRefused('PARENT_CAPTURE_BUDGET_REFUSED')
        verify_codec(codec, codec_sha256)
        required = [source, entry, core, runner, 'online_capture.py']
        before = packet_snapshot(root, required)
        capture = capture_process(['node', str(root / entry), str(root / source), *audits],
                                  timeout=process_timeout)
        try:
            after = packet_snapshot(root, required)
        except Exception:
            after = None
        unchanged = before == after
        status, reason = disposition(capture, before['files'][source], audits, unchanged)
        value = {'schema': 'public-online-capture.v1', 'case': case,
            'entry': entry, 'core': core, 'source': source, 'audits': audits,
            'source_inventory_before': before, 'source_inventory_after': after,
            'identity_unchanged': unchanged, 'client_exit': capture['exit'],
            'capture_failure': capture['failure'], 'status': status, 'reason': reason,
            'process_timeout_seconds': process_timeout,
            'original_stdout_base64': base64.b64encode(capture['stdout']).decode(),
            'original_stderr_base64': base64.b64encode(capture['stderr']).decode()}
        complete, packing_reason, receipt = seal_with_tombstone(value, {
            'schema': 'public-online-capture-tombstone.v1', 'case': case,
            'client_exit': capture['exit'], 'capture_failure': capture['failure'],
            'manifest_sha256': before['manifest_sha256'],
            'source_identity': before['files'][source],
            'stdout_bytes': len(capture['stdout']), 'stdout_sha256': sha256(capture['stdout']),
            'stderr_bytes': len(capture['stderr']), 'stderr_sha256': sha256(capture['stderr'])
        }, codec, codec_sha256)
        if not complete:
            status, reason = 'UNVERIFIED', packing_reason
        print(json.dumps({'case': case, 'status': status, 'reason': reason,
            'recovery_complete': complete, 'receipt': receipt,
            'source_sha256': before['files'][source]['sha256'],
            'local_compiler': False, 'native_Lake': False}, sort_keys=True))
        wanted = REJECTED if case.startswith('reject-') else PASS
        return 0 if complete and status == wanted else 2
    except CaptureRefused as error:
        reason = str(error)
    except Exception:
        reason = 'RUNNER_FAILURE_NO_PLAINTEXT_FALLBACK'
    print(json.dumps({'case': case, 'status': 'UNVERIFIED', 'reason': reason,
        'recovery_complete': False, 'local_compiler': False, 'native_Lake': False},
        sort_keys=True))
    return 2


def memory_source_identity(source, expected_sha256, audits):
    """Validate byte-exact input; Node's UTF-8 read must not replace bytes."""
    if type(source) is not bytes or len(source) > MEMORY_SOURCE_BOUND:
        raise CaptureRefused('MEMORY_SOURCE_BOUND_OR_TYPE')
    try:
        if source.decode('utf-8').encode('utf-8') != source:
            raise UnicodeError
    except UnicodeError:
        raise CaptureRefused('MEMORY_SOURCE_UTF8_REQUIRED') from None
    if (not isinstance(expected_sha256, str)
            or re.fullmatch(r'[0-9a-f]{64}', expected_sha256) is None
            or sha256(source) != expected_sha256):
        raise CaptureRefused('MEMORY_SOURCE_DIGEST_MISMATCH')
    if (not isinstance(audits, (list, tuple)) or not audits
            or any(not isinstance(n, str)
                   or re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", n) is None
                   for n in audits)
            or sum(len(n) + 1 for n in audits) > MEMORY_AUDIT_BOUND):
        raise CaptureRefused('MEMORY_AUDIT_SCOPE')
    # Exact independently computed identity of the unchanged client's wrapper.
    # This is an identity check, not a second proof/source renderer.
    suffix = '\n'.join(
        'set_option pp.universes true in\nset_option pp.explicit true in\n'
        f'#check {n}\n#print axioms {n}' for n in audits)
    submitted = source + b'\n' + suffix.encode() + (
        f'\n#eval "{DOCUMENT_SENTINEL}"\n').encode()
    return {'bytes': len(source), 'sha256': expected_sha256}, sha256(submitted)


def run_memory_case(root, source, expected_sha256, audits, codec, codec_sha256,
                    *, process_timeout=370, runner='check_online_memory.py'):
    """Seal caller-owned source, then pipe it to the unchanged hosted client.

    No source path, plaintext source file, raw-source argv, new client, compiler,
    native-origin assertion, identity or automatic retry is introduced.
    """
    case, entry, core = ('memory-proof', 'online_lean_full_context_drain.mjs',
                         'online_lean_full_context.mjs')
    request_receipt = result_receipt = source_identity = None
    submitted_sha256 = None
    request_complete = result_complete = False
    status, reason = 'UNVERIFIED', None
    try:
        if type(process_timeout) is not int or not 1 <= process_timeout <= 370:
            raise CaptureRefused('PARENT_CAPTURE_BUDGET_REFUSED')
        source_identity, submitted_sha256 = memory_source_identity(
            source, expected_sha256, audits)
        audits = list(audits)
        verify_codec(codec, codec_sha256)
        required = [entry, core, runner, 'online_capture.py']
        before = packet_snapshot(root, required)
        request = {
            'schema': 'public-online-memory-request.v1', 'case': case,
            'source_identity': source_identity,
            'submitted_source_sha256': submitted_sha256, 'audits': audits,
            'source_base64': base64.b64encode(source).decode(),
            'entry': entry, 'core': core, 'source_inventory': before,
            'process_timeout_seconds': process_timeout,
            'input_route': 'pipe_to_existing_client_dev_stdin'}
        request_complete, packing_reason, request_receipt = seal_with_tombstone(
            request, {
                'schema': 'public-online-memory-request-tombstone.v1',
                'case': case, 'source_identity': source_identity,
                'submitted_source_sha256': submitted_sha256,
                'manifest_sha256': before['manifest_sha256'],
                'audits': audits, 'child_invoked': False
            }, codec, codec_sha256)
        if not request_complete:
            reason = packing_reason
        else:
            try:
                ready = packet_snapshot(root, required)
            except Exception:
                ready = None
            child_invoked = ready == before
            capture = (capture_process(
                ['node', str(root / entry), '/dev/stdin', *audits],
                timeout=process_timeout, input_bytes=source) if child_invoked else {
                    'stdout': b'', 'stderr': b'', 'exit': None,
                    'failure': 'PUBLIC_SOURCE_CHANGED_BEFORE_MEMORY_CHILD'})
            try:
                after = packet_snapshot(root, required)
            except Exception:
                after = None
            unchanged = child_invoked and before == after
            status, reason = disposition(capture, source_identity, audits, unchanged)
            if status in (PASS, REJECTED):
                result = strict_json(capture['stdout'])
                if result.get('submitted_source_sha256') != submitted_sha256:
                    status, reason = 'UNVERIFIED', 'CLIENT_SUBMISSION_BINDING_MISMATCH'
            value = {
                'schema': 'public-online-memory-capture.v1', 'case': case,
                'request_receipt': request_receipt,
                'source_identity': source_identity,
                'submitted_source_sha256': submitted_sha256, 'audits': audits,
                'entry': entry, 'core': core, 'child_invoked': child_invoked,
                'source_inventory_before': before, 'source_inventory_ready': ready,
                'source_inventory_after': after, 'identity_unchanged': unchanged,
                'client_exit': capture['exit'], 'capture_failure': capture['failure'],
                'status': status, 'reason': reason,
                'process_timeout_seconds': process_timeout,
                'original_stdout_base64': base64.b64encode(capture['stdout']).decode(),
                'original_stderr_base64': base64.b64encode(capture['stderr']).decode()}
            result_complete, packing_reason, result_receipt = seal_with_tombstone(
                value, {
                    'schema': 'public-online-memory-capture-tombstone.v1', 'case': case,
                    'request_receipt': request_receipt, 'source_identity': source_identity,
                    'submitted_source_sha256': submitted_sha256,
                    'client_exit': capture['exit'], 'capture_failure': capture['failure'],
                    'manifest_sha256': before['manifest_sha256'],
                    'stdout_bytes': len(capture['stdout']),
                    'stdout_sha256': sha256(capture['stdout']),
                    'stderr_bytes': len(capture['stderr']),
                    'stderr_sha256': sha256(capture['stderr'])
                }, codec, codec_sha256)
            if not result_complete:
                status, reason = 'UNVERIFIED', packing_reason
    except CaptureRefused as error:
        status, reason = 'UNVERIFIED', str(error)
    except Exception:
        status, reason = 'UNVERIFIED', 'MEMORY_RUNNER_FAILURE_NO_PLAINTEXT_FALLBACK'
    complete = request_complete and result_complete
    print(json.dumps({
        'case': case, 'status': status, 'reason': reason,
        'recovery_complete': complete, 'request_recovery_complete': request_complete,
        'result_recovery_complete': result_complete,
        'request_receipt': request_receipt, 'receipt': result_receipt,
        'source_identity': source_identity,
        'submitted_source_sha256': submitted_sha256,
        'local_compiler': False, 'native_Lake': False}, sort_keys=True))
    return 0 if complete and status == PASS else 2
