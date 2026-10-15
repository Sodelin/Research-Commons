#!/usr/bin/env python3
"""Sequential, bounded replay with exact input/output and source receipts."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


BASE = Path(__file__).resolve().parent
LIMITS = {"wall_seconds": 6, "cpu_seconds": 3, "address_space_bytes": 536870912,
          "per_output_file_bytes": 65536, "smt_milliseconds": 2000,
          "z3_memory_megabytes": 192}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def restrict():
    resource.setrlimit(resource.RLIMIT_CPU, (3, 3))
    resource.setrlimit(resource.RLIMIT_FSIZE, (65536, 65536))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def bounded(command, output, name):
    stdout_path, stderr_path = output / (name + ".stdout"), output / (name + ".stderr")
    started = time.monotonic()
    timed_out = False
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        child = subprocess.Popen(command, stdout=stdout, stderr=stderr,
                                 preexec_fn=restrict, start_new_session=True)
        try:
            child.wait(timeout=LIMITS["wall_seconds"])
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
    return {
        "command_argv": command, "exit_code": child.returncode,
        "wall_timeout": timed_out, "elapsed_seconds": round(time.monotonic() - started, 6),
        "stdout": stdout_path.name, "stdout_sha256": digest(stdout_path),
        "stderr": stderr_path.name, "stderr_sha256": digest(stderr_path),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path,
                        help="Fresh output directory; an existing path is refused")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    worker = BASE / "z3_c_api_worker.py"
    command = ["proot-distro", "login", "linux-levels-debian", "--",
               "/usr/bin/python3", "-B", str(worker)]
    probe = bounded(command + ["--probe"], output, "engine-probe")
    (output / "engine-probe.execution.json").write_text(json.dumps(probe, indent=2, sort_keys=True) + "\n")
    if probe["exit_code"] != 0 or probe["wall_timeout"]:
        raise SystemExit("Bounded engine probe failed; retained outputs in " + str(output))
    probe_data = json.loads((output / probe["stdout"]).read_text())
    manifest_path = BASE / "obligations.json"
    obligations = json.loads(manifest_path.read_text())
    results = []
    for obligation in obligations:
        source = BASE / "obligations" / (obligation["id"] + ".smt2")
        result = bounded(command + [str(source)], output, obligation["id"])
        raw = (output / result["stdout"]).read_text()
        statuses = [line.strip() for line in raw.splitlines()
                    if line.strip() in ("sat", "unsat", "unknown")]
        if result["wall_timeout"]:
            outcome = "WALL_TIMEOUT"
        elif result["exit_code"] != 0:
            outcome = "EXECUTION_FAILURE"
        elif "(error " in raw or len(statuses) != 1:
            outcome = "INVALID_SOLVER_OUTPUT"
        else:
            outcome = statuses[0]
        result.update(obligation)
        result.update({"query_path": str(source.relative_to(BASE)),
                       "query_sha256": digest(source), "actual": outcome,
                       "expectation_met": outcome == obligation["expected"],
                       "proof_term_present": "(proof" in raw})
        results.append(result)
    repository = BASE.parent.parent
    source_head = subprocess.run(["git", "-C", str(repository), "rev-parse", "HEAD"],
                                 check=True, capture_output=True, text=True).stdout.strip()
    receipt = {
        "schema": "expdec-bounded-native-z3-controls-v1",
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_head_at_execution": source_head,
        "authored_source_files": {p.name: digest(p) for p in (Path(__file__).resolve(), worker, manifest_path)},
        "limits_per_native_child": LIMITS,
        "limit_enforcement": "Outer proot-distro route: wall/CPU/file/core; glibc worker before loading Z3: CPU/address-space/file/core; SMT input: timeout/memory_max_size.",
        "engine": probe_data, "engine_probe": probe,
        "results": results,
        "all_expectations_met": all(item["expectation_met"] for item in results),
        "scope": "Finite algebraic SMT controls only; no transcendence, arbitrary exponential theory, source compiler, G3 or G4 proof.",
        "proof_tier": "Native Z3 results with retained proof terms when requested; no independent proof-kernel replay.",
    }
    (output / "RESULT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"output": str(output), "engine_version": probe_data["version"],
                      "jobs": len(results), "all_expectations_met": receipt["all_expectations_met"]}))
    if not receipt["all_expectations_met"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
