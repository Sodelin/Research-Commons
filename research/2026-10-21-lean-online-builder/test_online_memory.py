"""Input/recovery/binding regressions; all children and codecs are mocked."""
import base64
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import Mock, patch

import online_capture as capture
import check_online_memory as cli

SOURCE = ('theorem checked : True := by trivial\n'
          '-- PRIVATE_INPUT_MARKER_FOR_TEST α\n').encode()
AUDITS = ['test.checked']
DIGEST = capture.sha256(SOURCE)
SUBMITTED = capture.sha256(SOURCE + b'\n'
    b'set_option pp.universes true in\nset_option pp.explicit true in\n'
    b'#check test.checked\n#print axioms test.checked\n'
    b'#eval "LEAN_E2E_DOCUMENT_FINISHED_20261021"\n')
SNAPSHOT = {'manifest_sha256': 'test-manifest', 'files': {}}
REPORT = {'status': capture.PASS, 'source_bytes': len(SOURCE),
    'source_sha256': DIGEST, 'submitted_source_sha256': SUBMITTED,
    'audits': AUDITS, 'before': {'lean': 'test-version'},
    'after': {'lean': 'test-version'}, 'errors': [],
    'audit_rows': [{'name': AUDITS[0], 'clean': True}]}


def stream(report=REPORT, exit_code=0):
    return {'stdout': json.dumps(report).encode(), 'stderr': b'\xffdiagnostic',
            'exit': exit_code, 'failure': None}


class MemoryTests(unittest.TestCase):
    def run_case(self, *, raw=None, ready=SNAPSHOT, after=SNAPSHOT,
                 source=SOURCE, digest=DIGEST, audits=None, fail_seal=None):
        records, events = [], []
        def seal(_codec, _sha, payload):
            record = capture.strict_json(payload)
            records.append(record)
            stage = 'request' if len(records) == 1 else 'result'
            events.append(stage)
            if stage == fail_seal:
                raise capture.CaptureRefused('RECORD_ENCRYPTION_UNCONFIRMED_NO_RETRY')
            return {'state': 'ENCRYPTED_AND_READ_BACK', 'record': '/encrypted/' + stage,
                    'ciphertext_bytes': len(payload), 'ciphertext_sha256': stage}
        def child(*_args, **_kwargs):
            events.append('child')
            return raw if raw is not None else stream()
        with patch.object(capture, 'verify_codec'), \
                patch.object(capture, 'packet_snapshot',
                             side_effect=[SNAPSHOT, ready, after]), \
                patch.object(capture, 'capture_process', side_effect=child) as call, \
                patch.object(capture, 'seal_record', side_effect=seal), \
                contextlib.redirect_stdout(io.StringIO()) as out:
            code = capture.run_memory_case(Path('/packet'), source, digest,
                AUDITS if audits is None else audits, Path('/existing/codec'), 'digest')
        printed = out.getvalue()
        self.assertNotIn('PRIVATE_INPUT_MARKER_FOR_TEST', printed)
        return code, capture.strict_json(printed), records, events, call

    def test_exact_input_is_sealed_before_pipe_and_result_links_request(self):
        code, result, records, events, call = self.run_case()
        self.assertEqual((code, result['status']), (0, capture.PASS))
        self.assertEqual(events, ['request', 'child', 'result'])
        self.assertEqual(base64.b64decode(records[0]['source_base64']), SOURCE)
        self.assertEqual(records[0]['submitted_source_sha256'], SUBMITTED)
        self.assertEqual(call.call_args.args[0],
            ['node', '/packet/online_lean_full_context_drain.mjs', '/dev/stdin', *AUDITS])
        self.assertEqual(call.call_args.kwargs, {'timeout': 370, 'input_bytes': SOURCE})
        self.assertEqual(records[1]['request_receipt'], result['request_receipt'])
        self.assertEqual(base64.b64decode(records[1]['original_stdout_base64']),
                         stream()['stdout'])
        self.assertTrue(result['recovery_complete'])

    def test_stdin_is_supplied_as_input_not_source_argv(self):
        completed = subprocess.CompletedProcess(['node'], 0, b'{}', b'')
        with patch.object(capture.subprocess, 'run', return_value=completed) as child:
            capture.capture_process(['node', '/dev/stdin'], input_bytes=SOURCE)
        self.assertEqual(child.call_args.kwargs['input'], SOURCE)
        self.assertEqual(child.call_args.args, (['node', '/dev/stdin'],))
        with patch.object(capture.subprocess, 'run', return_value=completed) as child:
            capture.capture_process(['old-file-client'])
        self.assertNotIn('input', child.call_args.kwargs)

    def test_invalid_input_never_invokes_child_or_writer(self):
        invalid = [
            {'digest': '0' * 64}, {'source': b'\xff', 'digest': capture.sha256(b'\xff')},
            {'source': b'x' * (capture.MEMORY_SOURCE_BOUND + 1)},
            {'source': bytearray(SOURCE)}, {'audits': []},
            {'audits': ['bad\n#eval 1']}, {'audits': ['a' * 65537]}]
        for options in invalid:
            with self.subTest(options=list(options)):
                code, result, records, events, child = self.run_case(**options)
                self.assertEqual(code, 2)
                self.assertEqual(result['status'], 'UNVERIFIED')
                self.assertEqual((records, events), ([], []))
                child.assert_not_called()

    def test_mutable_audit_list_is_copied_before_record_callback(self):
        audits = AUDITS.copy()
        observed = []
        def seal(_codec, _sha, payload):
            observed.append(capture.strict_json(payload))
            audits.append('caller.changed')
            return {'state': 'ENCRYPTED_AND_READ_BACK', 'record': '/encrypted',
                    'ciphertext_bytes': 1, 'ciphertext_sha256': 'digest'}
        with patch.object(capture, 'verify_codec'), \
                patch.object(capture, 'packet_snapshot', return_value=SNAPSHOT), \
                patch.object(capture, 'capture_process', return_value=stream()) as child, \
                patch.object(capture, 'seal_record', side_effect=seal), \
                contextlib.redirect_stdout(io.StringIO()):
            code = capture.run_memory_case(Path('/packet'), SOURCE, DIGEST, audits,
                                          Path('/codec'), 'digest')
        self.assertEqual(code, 0)
        self.assertEqual(observed[0]['audits'], AUDITS)
        self.assertEqual(child.call_args.args[0][-1], AUDITS[0])
        self.assertNotIn('caller.changed', child.call_args.args[0])

    def test_submitted_document_mismatch_cannot_pass(self):
        code, result, records, _, _ = self.run_case(
            raw=stream(dict(REPORT, submitted_source_sha256='different')))
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'CLIENT_SUBMISSION_BINDING_MISMATCH')
        self.assertEqual(records[1]['status'], 'UNVERIFIED')
        self.assertTrue(result['recovery_complete'])

    def test_rejection_remains_rejection_not_successful_proof_or_loss(self):
        code, result, _, _, _ = self.run_case(
            raw=stream(dict(REPORT, status=capture.REJECTED), 2))
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], capture.REJECTED)
        self.assertTrue(result['recovery_complete'])

    def test_request_encryption_refusal_prevents_child_without_retry(self):
        code, result, records, events, child = self.run_case(fail_seal='request')
        self.assertEqual(code, 2)
        self.assertFalse(result['recovery_complete'])
        self.assertEqual((len(records), events), (1, ['request']))
        child.assert_not_called()

    def test_result_encryption_refusal_cannot_report_pass_or_retry(self):
        code, result, records, events, child = self.run_case(fail_seal='result')
        self.assertEqual(code, 2)
        self.assertEqual(result['status'], 'UNVERIFIED')
        self.assertEqual((len(records), events), (2, ['request', 'child', 'result']))
        self.assertEqual(child.call_count, 1)
        self.assertTrue(result['request_recovery_complete'])
        self.assertFalse(result['result_recovery_complete'])

    def test_prelaunch_source_change_retains_request_and_never_invokes_child(self):
        code, result, records, events, child = self.run_case(ready=None)
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'PUBLIC_SOURCE_CHANGED_BEFORE_MEMORY_CHILD')
        self.assertEqual(events, ['request', 'result'])
        self.assertFalse(records[1]['child_invoked'])
        child.assert_not_called()

    def test_postlaunch_source_change_preserves_pipes_but_cannot_pass(self):
        code, result, records, _, _ = self.run_case(after=None)
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'PUBLIC_SOURCE_CHANGED_DURING_CAPTURE')
        self.assertEqual(base64.b64decode(records[1]['original_stderr_base64']),
                         stream()['stderr'])

    def test_timeout_keeps_exact_partial_pipes_without_restarting(self):
        error = subprocess.TimeoutExpired(['node'], 370, output=b'partial',
                                         stderr=b'\xffpartial')
        with patch.object(capture.subprocess, 'run', side_effect=error) as child:
            raw = capture.capture_process(['node'], timeout=370, input_bytes=SOURCE)
        self.assertEqual(child.call_count, 1)
        code, result, records, _, call = self.run_case(raw=raw)
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'PARENT_CAPTURE_TIMEOUT')
        self.assertEqual(base64.b64decode(records[1]['original_stdout_base64']), b'partial')
        self.assertEqual(base64.b64decode(records[1]['original_stderr_base64']), b'\xffpartial')
        self.assertEqual(call.call_count, 1)

    def test_request_packing_refusal_retains_tombstone_without_child(self):
        real_pack = capture.pack_record
        def bounded(value):
            if value['schema'] == 'public-online-memory-request.v1':
                raise capture.CaptureRefused('PACKED_RECORD_CODEC_BOUND')
            return real_pack(value)
        with patch.object(capture, 'pack_record', side_effect=bounded):
            code, result, records, events, child = self.run_case()
        self.assertEqual(code, 2)
        self.assertEqual(result['reason'], 'PACKED_RECORD_CODEC_BOUND')
        self.assertEqual(events, ['request'])
        self.assertEqual(records[0]['schema'], 'public-online-memory-request-tombstone.v1')
        self.assertFalse(records[0]['child_invoked'])
        child.assert_not_called()

    def test_result_tombstone_keeps_the_encrypted_request_link(self):
        real_pack = capture.pack_record
        def bounded(value):
            if value['schema'] == 'public-online-memory-capture.v1':
                raise capture.CaptureRefused('ORIGINAL_RECORD_RAM_BOUND')
            return real_pack(value)
        with patch.object(capture, 'pack_record', side_effect=bounded):
            code, result, records, _, _ = self.run_case()
        self.assertEqual(code, 2)
        self.assertFalse(result['recovery_complete'])
        self.assertEqual(records[1]['schema'], 'public-online-memory-capture-tombstone.v1')
        self.assertEqual(records[1]['request_receipt'], result['request_receipt'])
        self.assertEqual(records[1]['stdout_sha256'], capture.sha256(stream()['stdout']))

    def test_cli_reads_only_the_bounded_stdin_prefix(self):
        fake_stdin = Mock(buffer=io.BytesIO(b'x' * (capture.MEMORY_SOURCE_BOUND + 2)))
        args = ['check_online_memory.py', '--source-sha256', DIGEST,
                '--audit', AUDITS[0], '--record-codec', '/existing/codec',
                '--codec-sha256', 'digest']
        with patch.object(sys, 'argv', args), patch.object(sys, 'stdin', fake_stdin), \
                patch.object(cli, 'run_memory_case', return_value=2) as run:
            self.assertEqual(cli.main(), 2)
        self.assertEqual(len(run.call_args.args[1]), capture.MEMORY_SOURCE_BOUND + 1)
        self.assertEqual(fake_stdin.buffer.read(), b'x')


if __name__ == '__main__':
    unittest.main()
