"""Bounded, isolated official-BPP execution; keeps terminal receipts per attempt."""
import argparse
import datetime
import hashlib
import json
import os
import re
import resource
import signal
import shutil
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "bpp-sequence-pilot-20261005"
BIN = ROOT / "runtime/bpp-4.8.7-linux-x86_64/bin/bpp"
EXAMPLE = ROOT / "upstream-bpp-v4.8.7/examples/frogs"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name, analysis, seed, burnin, nsample, sampfreq, usedata, timeout):
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,79}", name):
        raise ValueError("invalid isolated run name")
    if analysis != "A00" or usedata not in {0, 1}:
        raise ValueError("invalid analysis/data mode")
    if not all(isinstance(x, int) and not isinstance(x, bool) and x > 0 for x in [seed, burnin, nsample, sampfreq, timeout]):
        raise ValueError("positive integer settings required")
    if seed > 2147483647 or burnin > 200000 or nsample > 200000 or sampfreq > 100 or timeout > 1800:
        raise ValueError("bounded pilot cap exceeded")
    if sha(ROOT / "LOCAL-EXAMPLE-ADMISSION.json") != "ede7bd9435389e97f10b6ec71d391d6a56143ad9b81a0397b22e80ff5920a0ed":
        raise ValueError("pinned admission record changed")
    pins = json.loads((ROOT / "LOCAL-EXAMPLE-ADMISSION.json").read_text())["files"]
    for filename in ["frogs.txt", "frogs.Imap.txt", "A01.bpp.ctl"]:
        if sha(EXAMPLE / filename) != pins[filename]["sha256"]:
            raise ValueError("pinned example changed: " + filename)
    if sha(BIN) != "6c8828704e1037788e02d6943cc6cbb61d05d6aadbdd976095b71fc965e8e90e":
        raise ValueError("pinned official executable changed")
    folder = ROOT / "runs" / name
    folder.mkdir(parents=True, exist_ok=False)
    proc = None
    try:
        original = EXAMPLE / ("A01.bpp.ctl")
        text = original.read_text()
        edits = {"seed": seed, "jobname": "result", "burnin": burnin, "nsample": nsample,
                 "sampfreq": sampfreq, "usedata": usedata, "finetune": 1, "speciestree": 0}
        for key, value in edits.items():
            text, count = re.subn(r"(?m)^(\s*" + key + r"\s*=\s*)[^\n]*", r"\g<1>" + str(value), text)
            if count != 1:
                raise ValueError("control replacement not unique: " + key)
        if re.search(r"(?m)^\s*threads\s*=", text):
            raise ValueError("unexpected upstream thread setting")
        if text.count("((K, C), (L, H));") != 1:
            raise ValueError("expected single pinned starting topology")
        text = text.replace("((K, C), (L, H));", "(((H, L), C), K);")
        text += "\nthreads = 1\n"
        ctl = folder / "control.ctl"
        ctl.write_text(text)
        for input_name in ["frogs.txt", "frogs.Imap.txt"]:
            shutil.copyfile(EXAMPLE / input_name, folder / input_name)
        cmd = [str(BIN), "--cfile", "control.ctl"]
        before = {"binary": sha(BIN), "control": sha(ctl), "alignment": sha(folder / "frogs.txt"),
                  "map": sha(folder / "frogs.Imap.txt"), "runner": sha(Path(__file__))}
        receipt = {"schema": "bounded-bpp-fixed-leading-attempt-v1", "task_date": "2026-10-05",
                   "host_clock_start_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "analysis": analysis, "conditional_topology": "(((H,L),C),K);", "source_control": "official A01", "settings": edits, "wall_limit_seconds": timeout,
                   "threads": 1, "address_space_limit_bytes": 2 * 1024**3,
                   "status": "RUNNING", "input_hashes_before": before,
                   "command": ["bpp", "--cfile", "control.ctl"],
                   "posterior_convergence_claimed": False, "biological_admission_claimed": False,
                   "source_control_sha256": sha(original),
                   "upstream_commit": "da8caf3aa00cf275cc9a044e0d806e9bbb0e1460", "calendar_calibration": None,
                   "raw_alignment_redistribution": False,
                   "compatibility_conversion": "finetune=1 replaces rejected pre-v4.8.1 positional syntax with documented auto-tuned defaults"}
        (folder / "ATTEMPT.json").write_text(json.dumps(receipt, indent=2)+"\n")
        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
        start = time.monotonic()
        with (folder / "stdout.log").open("w") as output:
            proc = subprocess.Popen(cmd, cwd=folder, stdout=output, stderr=subprocess.STDOUT,
                                    start_new_session=True, preexec_fn=limits)
            (folder / "PID.json").write_text(json.dumps({"pid": proc.pid, "runner_pid": os.getpid()}))
            try:
                exit_code = proc.wait(timeout=timeout)
                status = "EXECUTION_EXIT_ZERO" if exit_code == 0 else "TERMINAL_FAILURE"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:
                    exit_code = proc.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL)
                    exit_code = proc.wait()
                status = "RESOURCE_TIME_LIMIT"
        receipt.update({"status": status, "exit_code": exit_code, "elapsed_seconds": time.monotonic()-start,
                        "host_clock_end_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        "input_hashes_after": {"binary": sha(BIN), "control": sha(ctl), "alignment": sha(folder / "frogs.txt"),
                                               "map": sha(folder / "frogs.Imap.txt"), "runner": sha(Path(__file__))},
                        "output_inventory": [{"path": p.name, "bytes": p.stat().st_size, "sha256": sha(p)}
                                             for p in sorted(folder.iterdir()) if p.is_file()
                                             and p.name not in {"ATTEMPT.json", "TERMINAL.json", "PID.json", "frogs.txt", "frogs.Imap.txt"}]})
        receipt["inputs_stable"] = receipt["input_hashes_before"] == receipt["input_hashes_after"]
        if not receipt["inputs_stable"]:
            receipt["status"] = "INPUT_CHANGED"
        (folder / "TERMINAL.json").write_text(json.dumps(receipt, indent=2)+"\n")
        print(json.dumps({"name": name, "status": receipt["status"], "exit_code": exit_code,
                          "elapsed_seconds": receipt["elapsed_seconds"], "inputs_stable": receipt["inputs_stable"]}))
    except BaseException as error:
        if proc is not None and proc.poll() is None:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        terminal = folder / "TERMINAL.json"
        if not terminal.exists():
            terminal.write_text(json.dumps({"schema": "bounded-bpp-startup-failure-v2", "status": "RUNNER_FAILURE", "error_type": type(error).__name__, "error": str(error), "posterior_convergence_claimed": False}, indent=2)+"\n")
        raise



if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("name")
    p.add_argument("--analysis", choices=["A00"], required=True)
    p.add_argument("--seed", type=int, required=True)
    p.add_argument("--burnin", type=int, default=200)
    p.add_argument("--nsample", type=int, default=500)
    p.add_argument("--sampfreq", type=int, default=2)
    p.add_argument("--usedata", type=int, choices=[0, 1], default=1)
    p.add_argument("--timeout", type=int, default=180)
    a = p.parse_args()
    if min(a.seed, a.burnin, a.nsample, a.sampfreq, a.timeout) <= 0:
        p.error("positive bounded settings required")
    run(**vars(a))
