#!/usr/bin/env python3
"""Sequential, bounded replay with exact input/output and source receipts."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import re
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


def classify_result(raw, exit_code, wall_timeout, stderr=""):
    """Keep solver status, artifact errors and process failure independent.

    A resource-limited UNKNOWN can validly precede an unavailable-proof/model
    diagnostic. That diagnostic must not erase the solver's UNKNOWN status.
    SAT/UNSAT with an artifact error is insufficient for successful evidence.
    """
    statuses = [line.strip() for line in raw.splitlines()
                if line.strip() in ("sat", "unsat", "unknown")]
    solver_status = statuses[0] if len(statuses) == 1 else None
    diagnostics = [line.strip() for line in (raw + "\n" + stderr).splitlines()
                   if re.match(r"(?:\(error\b|Error:)", line.strip())]
    artifact_errors = [line for line in diagnostics
                       if re.search(r"(?:proof|model) (?:is )?not available|no current model", line, re.I)]
    non_artifact_errors = [line for line in diagnostics if line not in artifact_errors]
    if wall_timeout:
        actual = "WALL_TIMEOUT"
    elif exit_code != 0:
        actual = "EXECUTION_FAILURE"
    elif len(statuses) != 1 or non_artifact_errors:
        actual = "INVALID_SOLVER_OUTPUT"
    elif solver_status == "unknown":
        actual = "unknown"
    elif artifact_errors:
        actual = "ARTIFACT_FAILURE"
    else:
        actual = solver_status
    return {"actual": actual, "solver_status": solver_status,
            "solver_statuses": statuses, "artifact_error": bool(artifact_errors),
            "artifact_diagnostics": artifact_errors,
            "other_error_diagnostics": non_artifact_errors,
            "stderr_nonempty": bool(stderr.strip()),
            "usable_decision_evidence": actual in ("sat", "unsat")}


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
    parser.add_argument("--manifest", type=Path, default=BASE / "obligations.json",
                        help="Explicit small manifest; defaults to the 16 original controls")
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
    manifest_path = args.manifest.resolve()
    obligations = json.loads(manifest_path.read_text())
    results = []
    for obligation in obligations:
        source = BASE / "obligations" / (obligation["id"] + ".smt2")
        result = bounded(command + [str(source)], output, obligation["id"])
        raw = (output / result["stdout"]).read_text()
        stderr = (output / result["stderr"]).read_text()
        classification = classify_result(raw, result["exit_code"], result["wall_timeout"], stderr)
        result.update(obligation)
        result.update(classification)
        result.update({"query_path": str(source.relative_to(BASE)),
                       "query_sha256": digest(source),
                       "expectation_met": classification["actual"] == obligation["expected"],
                       "proof_term_present": "(proof" in raw})
        results.append(result)
    repository = BASE.parent.parent
    source_head = subprocess.run(["git", "-C", str(repository), "rev-parse", "HEAD"],
                                 check=True, capture_output=True, text=True).stdout.strip()
    receipt = {
        "schema": "expdec-bounded-native-z3-controls-v2",
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
