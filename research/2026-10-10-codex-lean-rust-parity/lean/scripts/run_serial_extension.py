#!/usr/bin/env python3
"""Run a short extension check between invocations of a live public runner.

Only the Python manager is paused, at a boundary with no live child process.
An active bounded Lean invocation is never paused. The manager is resumed even
when the extension fails; each intervention is recorded separately from the
immutable public run and its component receipts.
"""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def children(pid: int) -> list[int]:
    # Some supported Linux sandboxes omit task/children. /proc/stat retains the
    # same parent relationship and is also used by the qualified build monitor.
    result = []
    for path in Path("/proc").iterdir():
        if not path.name.isdigit():
            continue
        try:
            fields = (path / "stat").read_text().rsplit(")", 1)[1].split()
            if int(fields[1]) == pid:
                result.append(int(path.name))
        except (FileNotFoundError, ProcessLookupError):
            continue
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--public-pid", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("An extension command is required.")
    cmdline = Path(f"/proc/{args.public_pid}/cmdline").read_bytes().replace(b"\0", b" ").decode()
    if "scripts/build_connected.py current/connected" not in cmdline:
        raise RuntimeError("The selected PID is not the expected public runner.")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/scheduler" / stamp
    evidence.mkdir(parents=True)
    record = {"public_pid": args.public_pid, "public_command": cmdline,
              "extension_command": command, "status": "WAITING_COMPONENT_BOUNDARY",
              "active_compiler_paused": False}
    def save():
        (evidence / "RECEIPT.json").write_text(json.dumps(record, indent=2) + "\n")
    save()
    stopped = False
    pause_start = None
    try:
        deadline = time.monotonic() + 120
        while time.monotonic() < deadline:
            if children(args.public_pid):
                time.sleep(0.005)
                continue
            os.kill(args.public_pid, signal.SIGSTOP)
            stopped = True
            time.sleep(0.01)
            if not children(args.public_pid):
                pause_start = time.monotonic()
                break
            os.kill(args.public_pid, signal.SIGCONT)
            stopped = False
            time.sleep(0.005)
        if not stopped:
            raise RuntimeError("No safe component boundary was available within 120 seconds.")
        record.update(status="EXTENSION_RUNNING", manager_paused_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      public_children_at_boundary=children(args.public_pid))
        save()
        print(json.dumps({"status": "EXTENSION_RUNNING", "evidence": str(evidence)}), flush=True)
        result = subprocess.run(command, cwd=ROOT)
        record.update(status="EXTENSION_COMPLETED", extension_exit_code=result.returncode)
        return result.returncode
    except Exception as error:
        record.update(status="SCHEDULER_FAILED_PRESERVED", error=repr(error))
        raise
    finally:
        if stopped:
            os.kill(args.public_pid, signal.SIGCONT)
            record.update(manager_resumed=True, manager_pause_seconds=time.monotonic()-pause_start if pause_start else None)
        save()
        print(json.dumps(record), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
