"""Offline regressions for capture failures and acceptance/recovery boundaries.

All child/codec interactions are mocked. No hosted/compiler/model request,
record writer, temporary file or key is used by this suite.
"""
import base64
import contextlib
import io
import json
from pathlib import Path
import subprocess
import unittest
from unittest.mock import Mock, patch
import zlib
import online_capture as capture

IDENTITY = {'bytes': 3, 'sha256': capture.sha256(b'abc')}
AUDITS = ['test.checked']
REPORT = {'status': capture.PASS, 'source_bytes': 3,
    'source_sha256': IDENTITY['sha256'], 'audits': AUDITS,
    'before': {'lean': 'test-version'}, 'after': {'lean': 'test-version'},
    'errors': [], 'audit_rows': [{'name': AUDITS[0], 'clean': True}]}
SNAPSHOT = {'manifest_sha256': 'test-manifest', 'files': {'source.lean': IDENTITY}}


def stream(report=REPORT, exit_code=0):
    return {'stdout': json.dumps(report).encode(), 'stderr': b'\xff\x00diagnostic',
            'exit': exit_code, 'failure': None}


class CaptureTests(unittest.TestCase):
    def run_case(self, raw=None, after=SNAPSHOT, seal_error=None, case='test',
                 process_timeout=130):
        records = []
        def seal(_codec, _digest, payload):
            records.append(capture.strict_json(payload))
            if seal_error:
                raise seal_error
            return {'state': 'ENCRYPTED_AND_READ_BACK', 'record': '/existing/encrypted',
                    'ciphertext_bytes': 1, 'ciphertext_sha256': 'test'}
        with patch.object(capture, 'verify_codec'), \
                patch.object(capture, 'packet_snapshot', side_effect=[SNAPSHOT, after]), \
                patch.object(capture, 'capture_process', return_value=raw or stream()) as child, \
                patch.object(capture, 'seal_record', side_effect=seal), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            code = capture.run_case(Path('/packet'), case, 'source.lean', AUDITS,
                'entry.mjs', 'core.mjs', Path('/existing/codec'), 'digest', 'runner.py',
                process_timeout=process_timeout)
            self.assertEqual(child.call_args.kwargs['timeout'], process_timeout)
        return code, capture.strict_json(out.getvalue()), records

    def test_explicit_full_context_parent_budget_is_retained(self):
        code, result, records = self.run_case(process_timeout=370)
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], capture.PASS)
        self.assertEqual(records[0]['process_timeout_seconds'], 370)

    def test_invalid_parent_budget_refuses_before_child_or_codec(self):
        for budget in [0, 371, True, float('inf'), '370']:
            with self.subTest(budget=budget), patch.object(capture, 'capture_process') as child, \
                    patch.object(capture, 'verify_codec') as codec, \
                    contextlib.redirect_stdout(io.StringIO()) as out:
                code = capture.run_case(Path('/packet'), 'test', 'source.lean', AUDITS,
                    'entry.mjs', 'core.mjs', Path('/existing/codec'), 'digest', 'runner.py',
                    process_timeout=budget)
                self.assertEqual(code, 2)
                self.assertEqual(capture.strict_json(out.getvalue())['reason'],
                                 'PARENT_CAPTURE_BUDGET_REFUSED')
                child.assert_not_called()
                codec.assert_not_called()

    def test_timeout_preserves_partial_pipes(self):
        error = subprocess.TimeoutExpired(['child'], 130,
            output=b'{"status":"PASS_REMOTE_LEAN_CHECK"}', stderr=b'\xffpartial')
        with patch.object(capture.subprocess, 'run', side_effect=error) as child:
            raw = capture.capture_process(['child'])
        self.assertEqual(raw['stdout'], error.stdout)
        self.assertEqual(raw['stderr'], error.stderr)
        self.assertEqual(raw['failure'], 'PARENT_CAPTURE_TIMEOUT')
        self.assertEqual(child.call_count, 1)
        code, result, records = self.run_case(raw)
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'UNVERIFIED')
        self.assertEqual(base64.b64decode(records[0]['original_stderr_base64']), error.stderr)

    def test_unavailable_child_is_unverified(self):
        with patch.object(capture.subprocess, 'run', side_effect=OSError()):
            raw = capture.capture_process(['missing'])
        self.assertEqual(capture.disposition(raw, IDENTITY, AUDITS, True),
            ('UNVERIFIED', 'CLIENT_PROCESS_UNAVAILABLE'))

    def test_exit_status_required_for_both_dispositions(self):
        for status, valid in [(capture.PASS, 0), (capture.REJECTED, 2)]:
            report = dict(REPORT, status=status)
            for code in [0, 1, 2, -9, None]:
                with self.subTest(status=status, code=code):
                    actual, _ = capture.disposition(stream(report, code), IDENTITY, AUDITS, True)
                    self.assertEqual(actual, status if code == valid else 'UNVERIFIED')

    def test_result_source_audit_and_version_binding(self):
        changes = [{'source_bytes': 4}, {'source_sha256': 'other'}, {'audits': []},
            {'after': {'lean': 'changed'}}, {'before': {}, 'after': {}},
            {'audit_rows': []}, {'audit_rows': [{'name': AUDITS[0], 'clean': False}]},
            {'errors': [{'message': 'error'}]}]
        for change in changes:
            report = dict(REPORT, **change)
            self.assertEqual(capture.disposition(stream(report), IDENTITY, AUDITS, True)[0], 'UNVERIFIED')
        for raw in [b'{', b'null', b'NaN', b'\xff']:
            self.assertEqual(capture.disposition(dict(stream(), stdout=raw), IDENTITY, AUDITS, True)[0], 'UNVERIFIED')

    def test_source_change_still_seals_exact_streams(self):
        code, result, records = self.run_case(after=capture.CaptureRefused('PUBLIC_SOURCE_CHANGED'))
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'PUBLIC_SOURCE_CHANGED_DURING_CAPTURE')
        self.assertFalse(records[0]['identity_unchanged'])
        self.assertEqual(base64.b64decode(records[0]['original_stdout_base64']), stream()['stdout'])

    def test_record_refusal_cannot_report_pass_or_retry(self):
        code, result, records = self.run_case(seal_error=capture.CaptureRefused('RECORD_ENCRYPTION_REFUSED_NO_PLAINTEXT_FALLBACK'))
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'UNVERIFIED')
        self.assertFalse(result['recovery_complete'])
        self.assertEqual(len(records), 1)

    def test_acceptance_follows_verified_recovery(self):
        code, result, records = self.run_case()
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], capture.PASS)
        self.assertTrue(result['recovery_complete'])
        self.assertEqual(base64.b64decode(records[0]['original_stderr_base64']), stream()['stderr'])

    def test_negative_control_requires_normal_rejection(self):
        rejected = dict(REPORT, status=capture.REJECTED)
        code, result, _ = self.run_case(stream(rejected, 2), case='reject-false')
        self.assertEqual(code, 0)
        self.assertEqual(result['status'], capture.REJECTED)
        code, result, _ = self.run_case(stream(rejected, -9), case='reject-false')
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'UNVERIFIED')

    def test_lossless_packing(self):
        original = {'large': '\u03b1' * 300000}
        envelope = capture.strict_json(capture.pack_record(original))
        raw = zlib.decompress(base64.b64decode(envelope['zlib_base64']))
        self.assertEqual(capture.strict_json(raw), original)
        self.assertEqual(capture.sha256(raw), envelope['uncompressed_sha256'])
        self.assertEqual(len(raw), envelope['uncompressed_bytes'])

    def test_incompressible_packed_bound_is_refused(self):
        with patch.object(capture, 'CODEC_INPUT_BOUND', 100):
            with self.assertRaisesRegex(capture.CaptureRefused, '^PACKED_RECORD_CODEC_BOUND$'):
                capture.pack_record({'unique': list(range(1000))})

    def test_oversize_capture_is_encrypted_unknown_tombstone(self):
        with patch.object(capture, 'ORIGINAL_RECORD_BOUND', 2000):
            code, result, records = self.run_case(raw=dict(stream(), stderr=b'x' * 5000))
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'ORIGINAL_RECORD_RAM_BOUND')
        self.assertFalse(result['recovery_complete'])
        self.assertEqual(records[0]['schema'], 'public-online-capture-tombstone.v1')
        self.assertEqual(records[0]['stderr_bytes'], 5000)
        self.assertEqual(records[0]['stderr_sha256'], capture.sha256(b'x' * 5000))

    def test_ciphertext_readback_mismatch_is_refused(self):
        path = Mock()
        path.is_absolute.return_value = True
        path.is_symlink.return_value = False
        path.is_file.return_value = True
        path.read_bytes.return_value = b'changed'
        receipt = {'state': 'ENCRYPTED_AND_READ_BACK', 'record': '/encrypted',
            'ciphertext_bytes': 7, 'ciphertext_sha256': capture.sha256(b'correct')}
        child = subprocess.CompletedProcess(['codec'], 0, json.dumps(receipt).encode(), b'')
        with patch.object(capture, 'verify_codec'), patch.object(capture, 'Path', return_value=path), \
                patch.object(capture.subprocess, 'run', return_value=child):
            with self.assertRaisesRegex(capture.CaptureRefused, '^ENCRYPTED_READBACK_UNCONFIRMED$'):
                capture.seal_record(Path('/codec'), 'digest', b'{}')


if __name__ == '__main__':
    unittest.main()
