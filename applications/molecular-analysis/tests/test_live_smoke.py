"""Deterministic subprocess doubles: no SDK imports, credentials or network."""
from contextlib import ExitStack
from dataclasses import replace
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from molecular_apps import live_smoke as smoke
from molecular_apps.contracts import identity_sha256, sequence_sha256


def digest(data):
    return hashlib.sha256(data).hexdigest()


def fixture():
    sequence = "ACGT" * 4096
    return {"context": {"window": {"assembly": "hg38", "chromosome": "chr1", "start0": 100,
                "sequence": sequence, "guard_sequence": "ACGT", "source": "synthetic offline fixture",
                "sha256": sequence_sha256(sequence + "ACGT")},
            "transcript": {"gene_id": "SYNTHETIC_GENE", "transcript_id": "SYNTHETIC_TX",
                "start0": 104, "end0": 160, "strand": "+", "source": "synthetic annotation",
                "version": "mock-v1", "exons": [[104, 120], [140, 160]]},
            "tissue": "UBERON:0002107", "model_version": "ALL_FOLDS", "output_types": ["RNA_SEQ"],
            "preprocessing": "forward_reference_fixed_left_v1"},
        "endpoints": [{"id": "expr", "family": "expression", "output_type": "RNA_SEQ",
            "aggregation": "mean", "scale": "linear", "start0": 104, "end0": 160}],
        "variants": [{"id": "A", "chromosome": "chr1", "position": 109, "ref": "A", "alt": "G"},
                     {"id": "B", "chromosome": "chr1", "position": 145, "ref": "A", "alt": "T"}],
        "phase": {"kind": "hypothetical", "evidence": "synthetic only"}}


class FakeStream:
    def __init__(self, fd):
        self.fd, self.closed = fd, False

    def fileno(self):
        return self.fd

    def close(self):
        self.closed = True


class FakeProcess:
    pid = 123456789

    def __init__(self, exit_code=0, running=False, reap_timeout=False):
        self.stdin, self.stdout, self.stderr = [FakeStream(fd) for fd in (101, 102, 103)]
        self.exit_code, self.running, self.reap_timeout = exit_code, running, reap_timeout
        self.returncode = None
        self.wait_calls = []

    def poll(self):
        if not self.running and self.stdout.closed and self.stderr.closed:
            self.returncode = self.exit_code
        return self.returncode

    def wait(self, timeout):
        self.wait_calls.append(timeout)
        if self.reap_timeout:
            raise subprocess.TimeoutExpired("synthetic-only", timeout)
        self.returncode = self.exit_code
        return self.returncode


class FakeIO:
    """A fake clock and pipe readiness make limits independent of scheduling."""
    def __init__(self, stdout=b"", stderr=b"", *, running=False, block_stdin=False,
                 broken_stdin=False, exit_code=0, reap_timeout=False):
        self.process = FakeProcess(exit_code, running, reap_timeout)
        self.buffers = {102: bytearray(stdout), 103: bytearray(stderr)}
        self.block_stdin, self.broken_stdin = block_stdin, broken_stdin
        self.now, self.written, self.mapping = 0.0, bytearray(), {}
        self.selector_closed = False
        self.read_sizes = []

    def register(self, stream, events, data):
        self.mapping[stream.fd] = SimpleNamespace(fileobj=stream, fd=stream.fd, events=events, data=data)

    def unregister(self, stream):
        self.mapping.pop(stream.fd)

    def get_map(self):
        return self.mapping

    def select(self, timeout):
        self.now += timeout
        if self.process.running:
            return []
        return [(key, key.events) for key in list(self.mapping.values())]

    def close(self):
        self.selector_closed = True

    def read(self, fd, length):
        self.read_sizes.append(length)
        result = bytes(self.buffers[fd][:length])
        del self.buffers[fd][:length]
        return result

    def write(self, fd, data):
        if self.broken_stdin:
            raise BrokenPipeError("synthetic secret marker")
        if self.block_stdin:
            raise BlockingIOError()
        self.written.extend(data)
        return len(data)

    def patches(self):
        stack = ExitStack()
        self.spawn = stack.enter_context(mock.patch.object(smoke.subprocess, "Popen", return_value=self.process))
        self.kill = stack.enter_context(mock.patch.object(smoke.os, "killpg"))
        stack.enter_context(mock.patch.object(smoke.selectors, "DefaultSelector", return_value=self))
        stack.enter_context(mock.patch.object(smoke.os, "set_blocking"))
        stack.enter_context(mock.patch.object(smoke.os, "read", side_effect=self.read))
        stack.enter_context(mock.patch.object(smoke.os, "write", side_effect=self.write))
        stack.enter_context(mock.patch.object(smoke.time, "monotonic", side_effect=lambda: self.now))
        return stack


class SmokeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in smoke.SOURCE_PATHS:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("synthetic source pin: " + name)
        self.value = fixture()
        self.request_path = self.root / "request.json"
        self.track_path = self.root / "tracks.json"
        self.binary = self.root / "mock-core"
        self.binary.write_bytes(b"not an executable; never launched")
        self.request_path.write_text(json.dumps(self.value))
        self.track_path.write_text(json.dumps({"RNA_SEQ": "SYNTHETIC_EXACT_TRACK"}))
        self.plan = smoke.SmokePlan(self.request_path, digest(self.request_path.read_bytes()),
            self.track_path, digest(self.track_path.read_bytes()),
            {name: digest((self.root / name).read_bytes()) for name in smoke.SOURCE_PATHS},
            self.binary, digest(self.binary.read_bytes()),
            smoke._file_digest(Path(sys.executable), 128 * 2**20), True, True,
            wall_seconds=1, stdout_max_bytes=65536, stderr_max_bytes=100)

    def refreeze_request(self):
        self.request_path.write_text(json.dumps(self.value))
        self.plan = replace(self.plan, request_sha256=digest(self.request_path.read_bytes()))

    def result(self):
        request = smoke._request(self.request_path.read_bytes(), self.track_path.read_bytes())
        return {"contract_version": smoke.CONTRACT_VERSION, "application": "haplotype",
            "status": "UNKNOWN" if request.phase.kind == "unknown" else "SUCCESS",
            "successful_computation": True, "prediction_only": True,
            "biological_conclusion_established": False, "evidence": "REAL_MODEL_PREDICTION",
            "settings_sha256": request.context.settings_sha256,
            "input_sha256": identity_sha256(request), "native_binary_sha256": self.plan.core_binary_sha256,
            "scenarios": {name: {} for name in ("REF", "A", "B", "AB")},
            "interactions": [{"id": "expr", "status": "SUCCESS"}]}

    def run_fake(self, result=None, *, stdout=None, stderr=b"", **kwargs):
        value = self.result() if result is None else result
        pipes = FakeIO(json.dumps(value).encode() if stdout is None else stdout, stderr, **kwargs)
        with pipes.patches():
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        return receipt, pipes

    def test_success_one_launch_stdin_and_safe_receipt(self):
        result = self.result()
        result["message"] = "SENSITIVE_RAW_CHILD_SECRET"
        receipt, pipes = self.run_fake(result, stderr=b"SENSITIVE_RAW_CHILD_SECRET")
        self.assertEqual(receipt["status"], "SUCCESS")
        self.assertTrue(receipt["source_and_inputs_unchanged"])
        self.assertEqual(pipes.spawn.call_count, 1)
        command = pipes.spawn.call_args.args[0]
        self.assertIn("--access-authorized", command)
        self.assertIn("alphagenome", command)
        self.assertEqual(bytes(pipes.written), self.request_path.read_bytes())
        self.assertIsNone(pipes.spawn.call_args.kwargs["env"])
        self.assertTrue(pipes.spawn.call_args.kwargs["start_new_session"])
        self.assertNotIn(self.value["context"]["window"]["sequence"], repr(command))
        self.assertNotIn("SENSITIVE_RAW_CHILD_SECRET", json.dumps(receipt))
        self.assertNotIn("stdout_sha256", receipt)
        self.assertFalse(receipt["server_cancellation_confirmed"])
        self.assertFalse(receipt["quota_consumption_known"])
        self.assertEqual(receipt["expected_method_calls"]["predict_sequence"], 4)
        self.assertEqual(receipt["expected_method_calls"]["output_metadata"], 4)

    def test_unknown_phase_is_not_promoted_to_success(self):
        self.value["phase"] = {"kind": "unknown", "evidence": ""}
        self.refreeze_request()
        receipt, _ = self.run_fake(exit_code=3)
        self.assertEqual(receipt["status"], "UNKNOWN")
        self.assertTrue(receipt["successful_computation"])

    def test_authorization_refusal_before_reads_or_spawn(self):
        self.plan = replace(self.plan, access_authorized=False)
        with mock.patch.object(smoke, "_snapshot") as snapshot, mock.patch.object(smoke.subprocess, "Popen") as spawn:
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["status"], "UNSUPPORTED")
        self.assertEqual(receipt["launch_count"], 0)
        snapshot.assert_not_called()
        spawn.assert_not_called()

    def test_public_reference_assertion_required(self):
        self.plan = replace(self.plan, public_reference_confirmed=False)
        receipt, pipes = self.run_fake()
        self.assertEqual(receipt["code"], "PUBLIC_REFERENCE_REQUIRED")
        pipes.spawn.assert_not_called()

    def test_hash_mismatch_refuses_before_launch(self):
        self.plan = replace(self.plan, request_sha256="0" * 64)
        receipt, pipes = self.run_fake()
        self.assertEqual(receipt["status"], "INVALID_INPUT")
        self.assertEqual(receipt["code"], "HASH_MISMATCH")
        pipes.spawn.assert_not_called()

    def test_unknown_source_path_refuses_before_read(self):
        self.plan = replace(self.plan, source_pins={**self.plan.source_pins, "secret": "0" * 64})
        with mock.patch.object(smoke, "_snapshot") as snapshot:
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "SOURCE_PINS")
        snapshot.assert_not_called()

    def test_unsupported_model_before_child(self):
        self.value["context"]["model_version"] = "synthetic-v1"
        self.refreeze_request()
        pipes = FakeIO()
        with pipes.patches():
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["status"], "UNSUPPORTED")
        self.assertEqual(receipt["code"], "MODEL")
        pipes.spawn.assert_not_called()

    def test_unsupported_endpoint_before_child(self):
        self.value["endpoints"][0]["aggregation"] = "max"
        self.refreeze_request()
        pipes = FakeIO()
        with pipes.patches():
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["status"], "UNSUPPORTED")
        pipes.spawn.assert_not_called()

    def test_extra_track_refused_before_child(self):
        self.track_path.write_text(json.dumps({"RNA_SEQ": "SYNTHETIC_EXACT_TRACK", "ATAC": "unused"}))
        self.plan = replace(self.plan, track_names_sha256=digest(self.track_path.read_bytes()))
        pipes = FakeIO()
        with pipes.patches():
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "TRACK_SELECTION")
        pipes.spawn.assert_not_called()

    def test_request_snapshot_race_is_detected_before_child(self):
        original = smoke._read_bounded
        def read(path, limit):
            data = original(path, limit)
            return data + b" " if path == self.request_path else data
        with mock.patch.object(smoke, "_read_bounded", side_effect=read), mock.patch.object(smoke.subprocess, "Popen") as spawn:
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "HASH_MISMATCH")
        spawn.assert_not_called()

    def test_wall_deadline_kills_and_reaps_once_no_retry(self):
        receipt, pipes = self.run_fake(running=True)
        self.assertEqual(receipt["status"], "RESOURCE_LIMIT")
        self.assertEqual(receipt["code"], "WALL_TIME")
        self.assertEqual(pipes.spawn.call_count, 1)
        self.assertEqual(pipes.kill.call_count, 1)
        self.assertEqual(pipes.process.wait_calls, [1.0])
        self.assertTrue(receipt["source_and_inputs_unchanged"])

    def test_stdout_cap_is_enforced_during_reads(self):
        self.plan = replace(self.plan, stdout_max_bytes=10)
        receipt, pipes = self.run_fake(stdout=b"X" * 1000)
        self.assertEqual(receipt["code"], "STDOUT_BYTES")
        self.assertEqual(receipt["stdout_bytes"], 11)
        self.assertLessEqual(max(pipes.read_sizes), 101)
        self.assertNotIn("XXXX", json.dumps(receipt))

    def test_stderr_cap_is_enforced_and_not_retained(self):
        receipt, pipes = self.run_fake(stderr=b"secret" * 100)
        self.assertEqual(receipt["code"], "STDERR_BYTES")
        self.assertEqual(receipt["stderr_bytes"], 101)
        self.assertNotIn("secret", json.dumps(receipt))
        self.assertEqual(pipes.spawn.call_count, 1)

    def test_blocked_stdin_is_included_in_wall_deadline(self):
        receipt, pipes = self.run_fake(block_stdin=True)
        self.assertEqual(receipt["code"], "WALL_TIME")
        self.assertFalse(pipes.written)

    def test_broken_stdin_is_execution_failure(self):
        receipt, _ = self.run_fake(broken_stdin=True)
        self.assertEqual(receipt["code"], "STDIN_INCOMPLETE")
        self.assertEqual(receipt["status"], "EXECUTION_FAILURE")

    def test_reap_timeout_is_explicit_failure(self):
        receipt, _ = self.run_fake(running=True, reap_timeout=True)
        self.assertEqual(receipt["code"], "LOCAL_REAP_UNCONFIRMED")
        self.assertFalse(receipt["local_child_reaped"])

    def test_spawn_exception_never_returns_message_or_retries(self):
        with mock.patch.object(smoke.subprocess, "Popen", side_effect=OSError("SENSITIVE_RAW_CHILD_SECRET")) as spawn:
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "SUPERVISOR")
        self.assertEqual(spawn.call_count, 1)
        self.assertTrue(receipt["source_and_inputs_unchanged"])
        self.assertNotIn("SENSITIVE_RAW_CHILD_SECRET", json.dumps(receipt))

    def test_bad_exit_status_and_mock_evidence_are_not_live(self):
        for changes, exit_code in (({}, 6), ({"evidence": "MOCK_SYNTHETIC"}, 0),
                                   ({"settings_sha256": "0" * 64}, 0),
                                   ({"successful_computation": False}, 0),
                                   ({"biological_conclusion_established": True}, 0),
                                   ({"scenarios": {"REF": {}}}, 0),
                                   ({"interactions": []}, 0)):
            with self.subTest(changes=changes):
                value = self.result(); value.update(changes)
                receipt, _ = self.run_fake(value, exit_code=exit_code)
                self.assertEqual(receipt["status"], "EXECUTION_FAILURE")
                self.assertEqual(receipt["code"], "CHILD_PROTOCOL")
                self.assertNotIn("evidence", receipt)

    def test_invalid_json_duplicate_nonfinite_and_raw_traceback_not_echoed(self):
        for stdout in (b'{"status":"SUCCESS","status":"SUCCESS"}', b'{"x":NaN}',
                       b'raw traceback SENSITIVE_RAW_CHILD_SECRET', b'\xff', b'{}\n{}'):
            with self.subTest(stdout=stdout):
                receipt, _ = self.run_fake(stdout=stdout)
                self.assertEqual(receipt["code"], "CHILD_PROTOCOL")
                self.assertNotIn("SENSITIVE_RAW_CHILD_SECRET", json.dumps(receipt))

    def test_child_refusal_statuses_safe_allowlist(self):
        for status in ("INVALID_INPUT", "UNSUPPORTED", "RESOURCE_LIMIT", "EXECUTION_FAILURE"):
            value = {"status": status, "biological_conclusion_established": False,
                     "message": "SENSITIVE_RAW_CHILD_SECRET", "code": "SENSITIVE_RAW_CHILD_SECRET"}
            receipt, _ = self.run_fake(value, exit_code=smoke.EXIT_CODES[status])
            self.assertEqual(receipt["status"], status)
            self.assertEqual(receipt["code"], "CHILD_" + status)
            self.assertNotIn("SENSITIVE_RAW_CHILD_SECRET", json.dumps(receipt))

    def test_source_and_input_changes_after_child_invalidate_success(self):
        for path in (self.root / "molecular_apps/providers.py", self.request_path, self.track_path, self.binary):
            with self.subTest(path=path.name):
                original = path.read_bytes()
                outcome = smoke.ChildOutcome("SUCCESS", "CHILD_COMPLETED", 0,
                    json.dumps(self.result()).encode(), 100, 0, True, True)
                def changed(*args):
                    path.write_bytes(original + b" ")
                    return outcome
                with mock.patch.object(smoke, "_run_child", side_effect=changed):
                    receipt = smoke.run_smoke(self.plan, project_root=self.root)
                self.assertEqual(receipt["code"], "SOURCE_OR_INPUT_CHANGED")
                self.assertFalse(receipt["successful_computation"])
                self.assertNotIn("evidence", receipt)
                path.write_bytes(original)

    def test_staged_tracks_change_invalidates_success(self):
        outcome = smoke.ChildOutcome("SUCCESS", "CHILD_COMPLETED", 0, json.dumps(self.result()).encode(), 100, 0, True, True)
        def changed(command, *args):
            path = Path(command[command.index("--track-names") + 1])
            self.assertEqual(path.read_bytes(), self.track_path.read_bytes())
            self.assertEqual(path.stat().st_mode & 0o777, 0o600)
            path.write_bytes(b"{}")
            return outcome
        with mock.patch.object(smoke, "_run_child", side_effect=changed):
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "SOURCE_OR_INPUT_CHANGED")

    def test_bad_limits_platform_and_digest_refuse_before_launch(self):
        for changed in ({"wall_seconds": 0}, {"wall_seconds": float("nan")},
                        {"wall_seconds": 10**400}, {"wall_seconds": True},
                        {"stdout_max_bytes": 8 * 2**20 + 1}, {"stderr_max_bytes": 0},
                        {"python_sha256": "NOT_SHA"}):
            with self.subTest(changed=changed), mock.patch.object(smoke.subprocess, "Popen") as spawn:
                receipt = smoke.run_smoke(replace(self.plan, **changed), project_root=self.root)
                self.assertEqual(receipt["status"], "INVALID_INPUT")
                spawn.assert_not_called()
        with mock.patch.object(smoke.os, "name", "unsupported"):
            receipt = smoke.run_smoke(self.plan, project_root=self.root)
        self.assertEqual(receipt["code"], "PLATFORM")

    def test_cli_refuses_before_manifest_read_without_authorization(self):
        argv = ["unused", "unused", "unused", "--request-sha256", "0" * 64,
            "--track-names-sha256", "0" * 64, "--source-pins-sha256", "0" * 64,
            "--core-binary", "unused", "--core-binary-sha256", "0" * 64, "--python-sha256", "0" * 64]
        with mock.patch.object(smoke, "_read_bounded") as read, mock.patch("sys.stdout", new_callable=io.StringIO) as stdout:
            code = smoke.main(argv)
        self.assertEqual(code, 4)
        self.assertEqual(json.loads(stdout.getvalue())["launch_count"], 0)
        read.assert_not_called()

    def test_cli_source_manifest_is_hash_pinned_and_bounded(self):
        pins = self.root / "pins.json"; pins.write_text(json.dumps(self.plan.source_pins))
        argv = [str(self.request_path), str(self.track_path), str(pins),
            "--request-sha256", self.plan.request_sha256, "--track-names-sha256", self.plan.track_names_sha256,
            "--source-pins-sha256", digest(pins.read_bytes()), "--core-binary", str(self.binary),
            "--core-binary-sha256", self.plan.core_binary_sha256, "--python-sha256", self.plan.python_sha256,
            "--access-authorized", "--public-reference-confirmed"]
        with mock.patch.object(smoke, "run_smoke", return_value={"status": "UNSUPPORTED", "launch_count": 0}) as run, \
             mock.patch("sys.stdout", new_callable=io.StringIO):
            self.assertEqual(smoke.main(argv), 4)
        self.assertEqual(run.call_args.args[0].source_pins, self.plan.source_pins)
        pins.write_bytes(b"{}")
        with mock.patch.object(smoke, "run_smoke") as run, mock.patch("sys.stdout", new_callable=io.StringIO):
            self.assertEqual(smoke.main(argv), 2)
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
