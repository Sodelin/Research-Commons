#!/usr/bin/env python3
"""Focused lifecycle/request controls and fresh application functional checks."""
import hashlib
import importlib.util
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
BASE = PACKET / "quality/evidence/application-calendar-integration-20261010T1505Z"
OUT = BASE / "launcher-final-controls-1"
LAUNCHER = ROOT / "applications/practical-solver/run.py"
BINARY = Path("/workspace/scratch/lean-rust-parity-native/runtime/calendar-cli-artifact-1/calendar-solver")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def dead(pid):
    try:
        stat = (Path("/proc") / str(pid) / "stat").read_text()
    except FileNotFoundError:
        return True
    return stat[stat.rfind(")") + 2:].split()[0] in ("Z", "X")


def wait_file(path):
    until = time.monotonic() + 2
    while not path.exists():
        assert time.monotonic() < until, str(path)
        time.sleep(0.01)


def main():
    OUT.mkdir(exist_ok=False)
    spec = importlib.util.spec_from_file_location("practical_solver_launcher", LAUNCHER)
    launcher = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(launcher)
    observations = []
    real_popen = subprocess.Popen

    class ShortWaitPopen(real_popen):
        def wait(self, timeout=None):
            return super().wait(timeout=0.5 if timeout == 45 else timeout)

    def child_command(folder):
        # A detached child creates another detached grandchild, matching the
        # transport's new-session behavior without running the solver core.
        grand = "import os,time;from pathlib import Path;Path(" + repr(str(folder / "grandchild.pid")) + ").write_text(str(os.getpid()));time.sleep(60)"
        child = "import os,subprocess,sys,time;from pathlib import Path;subprocess.Popen([sys.executable,'-c'," + repr(grand) + "],start_new_session=True);Path(" + repr(str(folder / "child.pid")) + ").write_text(str(os.getpid()));time.sleep(60)"
        parent = "import subprocess,sys,time;subprocess.Popen([sys.executable,'-c'," + repr(child) + "],start_new_session=True);time.sleep(60)"
        return [sys.executable, "-c", parent]

    folder = OUT / "timeout-detached-descendants"
    folder.mkdir()
    with patch.object(launcher.subprocess, "Popen", ShortWaitPopen):
        try:
            launcher.execute(folder, "wrapper", child_command(folder))
            raise AssertionError("Timeout must fail")
        except RuntimeError as error:
            assert "exhausted resources" in str(error)
    receipt = load(folder / "wrapper.execution.json")
    pids = [int((folder / name).read_text()) for name in ("child.pid", "grandchild.pid")]
    assert all(dead(pid) for pid in pids)
    assert receipt["timeout"] is True and receipt["timeout_cleanup"]["descendants_killed"] == 2
    observations.append({"name": "outerTimeoutKillsDetachedChildAndGrandchild", "pass": True,
                         "test_wall_timeout_seconds": 0.5, "production_wall_timeout_seconds": 45,
                         "pids_terminated": pids, "execution_receipt_sha256": digest(folder / "wrapper.execution.json")})

    folder = OUT / "callback-detached-descendants"
    folder.mkdir()
    def callback():
        wait_file(folder / "grandchild.pid")
        raise ValueError("controlled launch callback failure")
    try:
        launcher.execute(folder, "wrapper", child_command(folder), on_launch=callback)
        raise AssertionError("Callback must fail")
    except ValueError as error:
        assert str(error) == "controlled launch callback failure"
    pids = [int((folder / name).read_text()) for name in ("child.pid", "grandchild.pid")]
    assert all(dead(pid) for pid in pids)
    observations.append({"name": "launchCallbackFailureKillsDetachedDescendants", "pass": True,
                         "pids_terminated": pids})

    # Test inconsistent child receipts and a changed staged request at the
    # outer interface. The real adapter/core stay untouched and are not called.
    source_request = ROOT / "applications/practical-solver/examples/calendar-law.json"
    template = load(BASE / "calendar-two-tip/component/RESULT.json")
    for name, mutation in (("foreign-child-request", "foreign"), ("changed-staged-request", "staged")):
        folder = OUT / name
        args = SimpleNamespace(command="calendar-law", request=source_request, output=folder,
                               native_binary=BINARY, expected_binary_sha256=digest(BINARY))
        def fake_execute(out, stage_name, command, on_launch=None, accepted_exit_codes=(0,)):
            if on_launch:
                on_launch()
            child = dict(template)
            if mutation == "foreign":
                child["request_sha256"] = "0" * 64
            else:
                (out / "REQUEST.json").write_bytes(source_request.read_bytes() + b" ")
            (out / "component").mkdir()
            (out / "component/RESULT.json").write_text(json.dumps(child))
            return {"exit_code": 0, "process_started": True}
        with patch.object(launcher, "execute", fake_execute):
            assert launcher.native_cell(args) == 1
        result = load(folder / "RESULT.json")
        assert result["status"] == "RESOURCE_OR_EXECUTION_FAILURE" and result["formal_table_checked"] is False
        observations.append({"name": name, "pass": True, "actual_native_execution": False,
                             "result_sha256": digest(folder / "RESULT.json")})

    functional = []
    for old in load(BASE / "CALENDAR-CASES.json"):
        request = ROOT / old["output"] / "REQUEST.json"
        folder = OUT / ("calendar-" + old["case"])
        command = [sys.executable, str(LAUNCHER), "calendar-law", "--request", str(request),
                   "--native-binary", str(BINARY), "--expected-binary-sha256",
                   "0" * 64 if old["case"] == "pin-mismatch" else digest(BINARY),
                   "--output", str(folder)]
        run = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=15)
        (OUT / (old["case"] + ".stdout")).write_bytes(run.stdout)
        (OUT / (old["case"] + ".stderr")).write_bytes(run.stderr)
        assert run.returncode == old["exit_code"], old["case"]
        result = load(folder / "RESULT.json")
        assert result["status"] == old["status"], old["case"]
        assert result["launcher_sha256"] == digest(LAUNCHER)
        assert result["request_bytes_sha256"] == digest(request)
        assert result["source_admission_verified"] is False
        if old["status"] == "SUPPLIED_CALENDAR_TABLE":
            assert result["formal_table_checked"] and result["independent_all_coefficients_checked"]
            assert result["component_result"]["certificate_valid"] is False
        functional.append({"name": old["case"], "status": result["status"], "exit_code": run.returncode,
                           "result_sha256": digest(folder / "RESULT.json"), "pass": True})
    receipt = {"schema": "calendar_launcher_final_controls_v1", "pass": True,
               "observed_utc": datetime.now(timezone.utc).isoformat(), "launcher_sha256": digest(LAUNCHER),
               "reviewer_sha256": digest(Path(__file__)), "native_binary_sha256": digest(BINARY),
               "focused_controls": observations, "functional_cases": functional,
               "focused_controls_passed": len(observations), "functional_cases_passed": len(functional),
               "full_solver_verified": False, "source_admission_verified": False,
               "scope": "Four lifecycle/request-binding controls and twelve fresh outer-application functional cases after cleanup/binding changes. Accepted native/frontend/117 suites were not rerun. Synthetic receipt tests do not execute a native solver."}
    (OUT / "RECEIPT.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"focused_controls": len(observations), "functional_cases": len(functional), "pass": True}))


if __name__ == "__main__":
    main()
