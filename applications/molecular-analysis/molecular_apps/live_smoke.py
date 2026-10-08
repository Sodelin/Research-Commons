"""One explicitly authorized, bounded live CLI child; no SDK import here.

This supervisor does not establish server cancellation, quota, or biology.
Raw child output is bounded in memory and never included in its receipt.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import tempfile
import time

from .contracts import (CONTRACT_VERSION, HaplotypeRequest, MolecularError,
                        Phase, Variant, context_from_dict, endpoint_from_dict,
                        identity_sha256, parse_json, preflight_endpoints, require)

SMOKE_VERSION = "molecular-live-smoke-v1"
PROJECT_ROOT = Path(__file__).resolve().parents[1]
SOURCE_PATHS = (
    "molecular_apps/__init__.py", "molecular_apps/__main__.py",
    "molecular_apps/cli.py", "molecular_apps/contracts.py",
    "molecular_apps/providers.py", "molecular_apps/haplotype.py",
    "molecular_apps/rna_processing.py", "molecular_apps/live_smoke.py",
    "core/Cargo.toml", "core/Cargo.lock", "core/src/lib.rs", "core/src/main.rs",
)
EXIT_CODES = {"SUCCESS": 0, "INVALID_INPUT": 2, "UNKNOWN": 3,
              "UNSUPPORTED": 4, "RESOURCE_LIMIT": 5, "EXECUTION_FAILURE": 6}
MODELS = {"ALL_FOLDS", "FOLD_0", "FOLD_1", "FOLD_2", "FOLD_3"}
OUTPUTS = {"RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE"}
WINDOW_LENGTHS = {16384, 131072, 524288, 1048576}


@dataclass(frozen=True)
class SmokePlan:
    request_path: Path
    request_sha256: str
    track_names_path: Path
    track_names_sha256: str
    source_pins: dict[str, str]
    core_binary: Path
    core_binary_sha256: str
    python_sha256: str
    access_authorized: bool = False
    public_reference_confirmed: bool = False
    wall_seconds: float = 120.0
    stdout_max_bytes: int = 2**20
    stderr_max_bytes: int = 65536


@dataclass(frozen=True)
class ChildOutcome:
    status: str
    code: str
    returncode: int | None
    stdout: bytes
    stdout_bytes: int
    stderr_bytes: int
    termination_requested: bool
    reaped: bool


def _digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _is_digest(value) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def _read_bounded(path: Path, limit: int) -> bytes:
    try:
        with path.open("rb") as stream:
            data = stream.read(limit + 1)
    except OSError as error:
        raise MolecularError("INVALID_INPUT", "INPUT_FILE", "cannot read declared input") from error
    require(len(data) <= limit, "INPUT_SIZE", "declared input exceeds byte limit", "RESOURCE_LIMIT")
    return data


def _file_digest(path: Path, limit: int) -> str:
    # Streaming authentication does not allocate a binary-sized buffer.
    result = hashlib.sha256()
    count = 0
    try:
        with path.open("rb") as stream:
            while chunk := stream.read(65536):
                count += len(chunk)
                require(count <= limit, "INPUT_SIZE", "declared file exceeds byte limit", "RESOURCE_LIMIT")
                result.update(chunk)
    except OSError as error:
        raise MolecularError("INVALID_INPUT", "INPUT_FILE", "cannot authenticate declared file") from error
    return result.hexdigest()


def _snapshot(plan: SmokePlan, root: Path) -> dict[str, str]:
    result = {name: _file_digest(root / name, 2**21) for name in SOURCE_PATHS}
    result.update(request=_file_digest(plan.request_path, 8 * 2**20),
                  track_names=_file_digest(plan.track_names_path, 65536),
                  native_binary=_file_digest(plan.core_binary, 64 * 2**20),
                  python=_file_digest(Path(sys.executable), 128 * 2**20))
    return result


def _validate_plan(plan: SmokePlan) -> None:
    require(plan.access_authorized is True, "AUTHORIZATION_REQUIRED", "explicit access and terms assertion required", "UNSUPPORTED")
    require(plan.public_reference_confirmed is True, "PUBLIC_REFERENCE_REQUIRED", "operator must confirm reviewed public nonpersonal input", "UNSUPPORTED")
    require(type(plan.wall_seconds) in {int, float} and 1 <= plan.wall_seconds <= 600
            and math.isfinite(plan.wall_seconds), "LIMITS", "wall limit must be 1..600 seconds")
    for value, cap in ((plan.stdout_max_bytes, 8 * 2**20), (plan.stderr_max_bytes, 65536)):
        require(type(value) is int and 1 <= value <= cap, "LIMITS", "invalid stream byte limit")
    require(isinstance(plan.source_pins, dict) and set(plan.source_pins) == set(SOURCE_PATHS),
            "SOURCE_PINS", "complete exact source allowlist required")
    require(all(_is_digest(value) for value in (*plan.source_pins.values(), plan.request_sha256,
                plan.track_names_sha256, plan.core_binary_sha256, plan.python_sha256)),
            "HASH", "expected hashes must be lowercase SHA256")


def _decode(data: bytes) -> dict:
    try:
        return parse_json(data.decode("utf-8"))
    except UnicodeError as error:
        raise MolecularError("INVALID_INPUT", "JSON", "invalid UTF-8 JSON") from error


def _request(data: bytes, tracks_data: bytes) -> HaplotypeRequest:
    value, tracks = _decode(data), _decode(tracks_data)
    require(set(value) == {"context", "endpoints", "variants", "phase"}, "SCHEMA", "exact haplotype fields required")
    context = context_from_dict(value["context"])
    require(context.model_version in MODELS, "MODEL", "declare a supported official model", "UNSUPPORTED")
    require(len(context.window.sequence) in WINDOW_LENGTHS, "WINDOW", "unsupported official window length", "UNSUPPORTED")
    require(set(context.output_types) <= OUTPUTS, "OUTPUT", "unsupported live output", "UNSUPPORTED")
    require(set(tracks) == set(context.output_types) and all(isinstance(v, str) and 0 < len(v) <= 256
            and not any(ord(c) < 32 for c in v) for v in tracks.values()),
            "TRACK_SELECTION", "declare exactly one explicit track per requested modality", "UNSUPPORTED")
    require(isinstance(value["endpoints"], list) and bool(value["endpoints"]), "SCHEMA", "nonempty endpoint array required")
    endpoints = tuple(endpoint_from_dict(row, context) for row in value["endpoints"])
    require(isinstance(value["variants"], list) and len(value["variants"]) == 2, "SCHEMA", "two variants required")
    variants = []
    for row in value["variants"]:
        require(isinstance(row, dict) and set(row) == set(Variant.__dataclass_fields__), "SCHEMA", "exact variant fields required")
        variants.append(Variant(**row))
    phase = value["phase"]
    require(isinstance(phase, dict) and set(phase) == {"kind", "evidence"}, "SCHEMA", "exact phase fields required")
    request = HaplotypeRequest(context, tuple(variants), Phase(**phase), endpoints)
    request.validate()
    preflight_endpoints(context, endpoints)
    return request


def _kill_group(child) -> bool:
    try:
        os.killpg(child.pid, signal.SIGKILL)
        return True
    except ProcessLookupError:
        return False
    except OSError:
        # This is a best-effort local containment action, never a server claim.
        return False


def _run_child(command: list[str], payload: bytes, plan: SmokePlan, root: Path) -> ChildOutcome:
    """POSIX stream supervision; fixed-size reads and a single Popen call.

    The deadline includes stdin delivery and waiting for inherited pipe EOF.
    Cleanup can spend at most one further second waiting for the child reap.
    No raw stderr is retained, not even when it fits within the byte bound.
    """
    deadline = time.monotonic() + plan.wall_seconds
    child = None
    selector = selectors.DefaultSelector()
    stdout = bytearray()
    counts = {"stdout": 0, "stderr": 0}
    status, code = "SUCCESS", "CHILD_COMPLETED"
    written = 0
    reaped = False
    termination = False
    try:
        child = subprocess.Popen(command, cwd=root, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 env=None, start_new_session=True, bufsize=0)
        for stream, label, event in ((child.stdin, "stdin", selectors.EVENT_WRITE),
                                     (child.stdout, "stdout", selectors.EVENT_READ),
                                     (child.stderr, "stderr", selectors.EVENT_READ)):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, event, label)
        while selector.get_map() or child.poll() is None:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                status, code = "RESOURCE_LIMIT", "WALL_TIME"
                break
            events = selector.select(min(remaining, 0.05))
            for key, _ in events:
                if key.data == "stdin":
                    try:
                        written += os.write(key.fd, payload[written:written + 65536])
                    except BrokenPipeError:
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
                        continue
                    except BlockingIOError:
                        continue
                    if written == len(payload):
                        selector.unregister(key.fileobj)
                        key.fileobj.close()
                    continue
                cap = plan.stdout_max_bytes if key.data == "stdout" else plan.stderr_max_bytes
                try:
                    chunk = os.read(key.fd, min(65536, cap - counts[key.data] + 1))
                except BlockingIOError:
                    continue
                if not chunk:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    continue
                counts[key.data] += len(chunk)
                if counts[key.data] > cap:
                    status, code = "RESOURCE_LIMIT", key.data.upper() + "_BYTES"
                    break
                if key.data == "stdout":
                    stdout.extend(chunk)
            if status != "SUCCESS":
                break
        if status == "SUCCESS" and written != len(payload):
            status, code = "EXECUTION_FAILURE", "STDIN_INCOMPLETE"
    except Exception:
        # Exception text and OS paths may contain sensitive metadata.
        status, code = "EXECUTION_FAILURE", "SUPERVISOR"
    finally:
        selector.close()
        if child is not None:
            # Also stop descendants after a normally exited parent. EOF alone
            # does not prove there are no remaining group members.
            termination = _kill_group(child)
            for stream in (child.stdin, child.stdout, child.stderr):
                if stream is not None:
                    try:
                        stream.close()
                    except OSError:
                        pass
            try:
                child.wait(timeout=1.0)
                reaped = True
            except (subprocess.TimeoutExpired, OSError):
                status, code = "EXECUTION_FAILURE", "LOCAL_REAP_UNCONFIRMED"
    return ChildOutcome(status, code, child.returncode if child else None,
                        bytes(stdout) if status == "SUCCESS" else b"",
                        counts["stdout"], counts["stderr"], termination, reaped)


def _child_summary(outcome: ChildOutcome, request: HaplotypeRequest, plan: SmokePlan) -> dict:
    if outcome.status != "SUCCESS":
        return {"status": outcome.status, "code": outcome.code, "successful_computation": False}
    try:
        result = _decode(outcome.stdout)
        status = result.get("status")
        require(status in EXIT_CODES and type(outcome.returncode) is int
                and outcome.returncode == EXIT_CODES[status], "CHILD_PROTOCOL", "status/exit mismatch")
        require(result.get("biological_conclusion_established") is False,
                "CHILD_PROTOCOL", "child must disclaim biological conclusion")
        if status not in {"SUCCESS", "UNKNOWN"}:
            return {"status": status, "code": "CHILD_" + status, "successful_computation": False}
        require(result.get("contract_version") == CONTRACT_VERSION and result.get("application") == "haplotype"
                and result.get("successful_computation") is True and result.get("prediction_only") is True
                and result.get("evidence") == "REAL_MODEL_PREDICTION"
                and result.get("settings_sha256") == request.context.settings_sha256
                and result.get("input_sha256") == identity_sha256(request)
                and result.get("native_binary_sha256") == plan.core_binary_sha256,
                "CHILD_PROTOCOL", "matched live result identity required")
        require(status == ("UNKNOWN" if request.phase.kind == "unknown" else "SUCCESS"),
                "CHILD_PROTOCOL", "phase/status mismatch")
        scenarios = result.get("scenarios")
        require(isinstance(scenarios, dict) and set(scenarios) == {"REF", "A", "B", "AB"},
                "CHILD_PROTOCOL", "four matched scenarios required")
        rows = result.get("interactions")
        require(isinstance(rows, list) and len(rows) == len(request.endpoints)
                and all(isinstance(row, dict) and row.get("status") == "SUCCESS" for row in rows)
                and {row.get("id") for row in rows} == {endpoint.id for endpoint in request.endpoints},
                "CHILD_PROTOCOL", "declared endpoints must all succeed")
        return {"status": status, "code": "MATCHED_LIVE_CHILD_RESULT", "successful_computation": True,
                "evidence": "REAL_MODEL_PREDICTION", "scenario_count": 4, "endpoint_count": len(rows)}
    except Exception:
        return {"status": "EXECUTION_FAILURE", "code": "CHILD_PROTOCOL", "successful_computation": False}


def run_smoke(plan: SmokePlan, *, project_root: Path = PROJECT_ROOT) -> dict:
    """Return a safe receipt only, with no key inspection or automatic retry."""
    receipt = {"smoke_version": SMOKE_VERSION, "status": "EXECUTION_FAILURE", "code": "NOT_STARTED",
               "launch_count": 0, "launcher_retries": 0, "successful_computation": False,
               "biological_conclusion_established": False, "server_cancellation_confirmed": False,
               "quota_consumption_known": False, "sdk_internal_retry_policy_verified": False}
    before = None
    staged_tracks_unchanged = False
    try:
        require(os.name == "posix", "PLATFORM", "process-group supervision requires POSIX", "UNSUPPORTED")
        _validate_plan(plan)
        before = _snapshot(plan, project_root)
        expected = {**plan.source_pins, "request": plan.request_sha256,
                    "track_names": plan.track_names_sha256, "native_binary": plan.core_binary_sha256,
                    "python": plan.python_sha256}
        receipt["hashes_before"] = before
        require(before == expected, "HASH_MISMATCH", "declared source/input identity mismatch")
        payload = _read_bounded(plan.request_path, 8 * 2**20)
        tracks_data = _read_bounded(plan.track_names_path, 65536)
        require(_digest(payload) == plan.request_sha256 and _digest(tracks_data) == plan.track_names_sha256,
                "HASH_MISMATCH", "input changed during snapshot")
        request = _request(payload, tracks_data)
        receipt.update(limits={"wall_seconds": plan.wall_seconds, "cleanup_wait_seconds": 1,
                               "stdout_max_bytes": plan.stdout_max_bytes, "stderr_max_bytes": plan.stderr_max_bytes},
                       expected_method_calls={"predict_sequence": 4, "output_metadata": 4,
                                              "client_create": 1, "network_rpc_count": "unknown"},
                       model_version=request.context.model_version,
                       output_types=list(request.context.output_types),
                       public_reference_basis="operator assertion plus separately reviewed frozen request")
        # The CLI accepts tracks by path. Use a private immutable snapshot;
        # stdin uses the already authenticated request bytes, not a reread.
        with tempfile.TemporaryDirectory(prefix="molecular-smoke-") as directory:
            tracks_path = Path(directory) / "tracks.json"
            tracks_path.write_bytes(tracks_data)
            tracks_path.chmod(0o600)
            command = [sys.executable, "-m", "molecular_apps", "haplotype", "-",
                       "--provider", "alphagenome", "--access-authorized",
                       "--track-names", str(tracks_path), "--core-binary", str(plan.core_binary.resolve())]
            receipt["launch_count"] = 1
            outcome = _run_child(command, payload, plan, project_root)
            staged_tracks_unchanged = _file_digest(tracks_path, 65536) == plan.track_names_sha256
        receipt.update(stdout_bytes=outcome.stdout_bytes, stderr_bytes=outcome.stderr_bytes,
                       child_exit_code=outcome.returncode, local_termination_requested=outcome.termination_requested,
                       local_child_reaped=outcome.reaped)
        receipt.update(_child_summary(outcome, request, plan))
    except MolecularError as error:
        # Only our fixed code/status are safe; never include exception.message.
        receipt.update(status=error.status, code=error.code, successful_computation=False)
    except Exception:
        receipt.update(status="EXECUTION_FAILURE", code="SUPERVISOR", successful_computation=False)
    finally:
        if before is not None and receipt["launch_count"]:
            try:
                after = _snapshot(plan, project_root)
                receipt["hashes_after"] = after
                unchanged = before == after and staged_tracks_unchanged
            except Exception:
                unchanged = False
            receipt["source_and_inputs_unchanged"] = unchanged
            if not unchanged:
                receipt.update(status="EXECUTION_FAILURE", code="SOURCE_OR_INPUT_CHANGED", successful_computation=False)
                receipt.pop("evidence", None)
    return receipt


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="One bounded authorized AlphaGenome haplotype smoke child; emits a sanitized receipt only.")
    parser.add_argument("request", type=Path)
    parser.add_argument("track_names", type=Path)
    parser.add_argument("source_pins", type=Path, help="JSON object with exactly SOURCE_PATHS and reviewed SHA256 values")
    parser.add_argument("--request-sha256", required=True)
    parser.add_argument("--track-names-sha256", required=True)
    parser.add_argument("--source-pins-sha256", required=True)
    parser.add_argument("--core-binary", type=Path, required=True)
    parser.add_argument("--core-binary-sha256", required=True)
    parser.add_argument("--python-sha256", required=True)
    parser.add_argument("--access-authorized", action="store_true")
    parser.add_argument("--public-reference-confirmed", action="store_true")
    parser.add_argument("--wall-seconds", type=float, default=120)
    parser.add_argument("--stdout-max-bytes", type=int, default=2**20)
    parser.add_argument("--stderr-max-bytes", type=int, default=65536)
    args = parser.parse_args(argv)
    try:
        # Refuse before reading any inputs when authorization is absent.
        require(args.access_authorized, "AUTHORIZATION_REQUIRED", "explicit access assertion required", "UNSUPPORTED")
        require(args.public_reference_confirmed, "PUBLIC_REFERENCE_REQUIRED", "public reference assertion required", "UNSUPPORTED")
        pins_data = _read_bounded(args.source_pins, 65536)
        require(_is_digest(args.source_pins_sha256) and _digest(pins_data) == args.source_pins_sha256,
                "HASH_MISMATCH", "source manifest identity mismatch")
        plan = SmokePlan(args.request, args.request_sha256, args.track_names, args.track_names_sha256,
                         _decode(pins_data), args.core_binary, args.core_binary_sha256, args.python_sha256,
                         args.access_authorized, args.public_reference_confirmed, args.wall_seconds,
                         args.stdout_max_bytes, args.stderr_max_bytes)
        result = run_smoke(plan)
        result["source_pins_manifest_sha256"] = args.source_pins_sha256
    except MolecularError as error:
        result = {"smoke_version": SMOKE_VERSION, "status": error.status, "code": error.code,
                  "launch_count": 0, "successful_computation": False, "biological_conclusion_established": False}
    except Exception:
        result = {"smoke_version": SMOKE_VERSION, "status": "EXECUTION_FAILURE", "code": "SUPERVISOR",
                  "launch_count": 0, "successful_computation": False, "biological_conclusion_established": False}
    print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
    return EXIT_CODES[result["status"]]


if __name__ == "__main__":
    raise SystemExit(main())
