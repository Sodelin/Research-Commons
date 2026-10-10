#!/usr/bin/env python3
"""Execute eight inherited coefficient fixtures in an already checked context.

This records actual outputs and before/after artifact bindings. Independent
coefficient comparison belongs to the design oracle; successful execution is
not a general quotient/refinement proof and is not a standalone native ELF.
"""
from __future__ import annotations
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    preparation_path = ROOT / "POPULATION-EXECUTION-PREPARATION.json"
    preparation = json.loads(preparation_path.read_bytes())
    assert preparation["status"] == "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING"
    command = preparation["command_prefix"]
    assert sha(Path(command[0])) == COMPILER
    assert sha(Path(preparation["driver_path"])) == preparation["driver_sha256"]
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/source-population-execution" / stamp
    evidence.mkdir(parents=True)
    frozen_preparation = evidence / "PREPARATION.json"
    frozen_preparation.write_bytes(preparation_path.read_bytes())
    binding_root = ROOT / preparation["evidence"]
    artifacts = json.loads((binding_root / "ACTUAL-IMPORTED-ARTIFACTS.json").read_bytes())
    native = json.loads((binding_root / "NATIVE-RUNTIME-PINS.json").read_bytes())
    def bindings():
        actual = {}
        for row in artifacts:
            p = Path(row["path"])
            assert p.stat().st_size == row["bytes"]
            value = sha(p)
            assert value == row["sha256"], p
            actual[str(p)] = value
        for path, row in native["libraries"].items():
            value = sha(Path(path))
            assert value == row["sha256"], path
            actual[path] = value
        assert sha(Path(command[0])) == COMPILER
        assert sha(Path(preparation["driver_path"])) == preparation["driver_sha256"]
        return actual
    before = bindings()
    save(evidence / "BINDINGS-BEFORE.json", before)
    env = dict(os.environ, LEAN_PATH=preparation["lean_path"], LEAN_NUM_THREADS="1")
    records = []
    for fixture in preparation["fixtures"]:
        current = [*command, fixture]
        start = time.monotonic()
        code = None
        out = err = b""
        try:
            result = subprocess.run(current, cwd=preparation["workdir"], env=env,
                                    capture_output=True, timeout=30)
            code, out, err = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as failure:
            code = 124
            out, err = failure.stdout or b"", failure.stderr or b""
        (evidence / (fixture + ".stdout")).write_bytes(out)
        (evidence / (fixture + ".stderr")).write_bytes(err)
        record = {"fixture": fixture, "command": current, "exit_code": code,
                  "elapsed_seconds": time.monotonic()-start,
                  "stdout_sha256": hashlib.sha256(out).hexdigest(),
                  "stderr_sha256": hashlib.sha256(err).hexdigest(),
                  "status": "PASS_PROCESS_EXECUTION" if code == 0 else "FAILED_EXECUTION_PRESERVED"}
        records.append(record)
        save(evidence / (fixture + ".receipt.json"), record)
        print(json.dumps({k: record[k] for k in ["fixture", "status", "elapsed_seconds"]}), flush=True)
    after = bindings()
    save(evidence / "BINDINGS-AFTER.json", after)
    passed = before == after and all(r["exit_code"] == 0 for r in records)
    receipt = {"status": "PASS_EIGHT_IMPORTED_ORIGINAL_COEFFICIENT_EXECUTIONS" if passed
               else "FAILED_EXECUTIONS_PRESERVED", "execution_mode": preparation["execution_mode"],
               "standalone_native_elf_claimed": False, "coefficient_comparison_claimed": False,
               "preparation_sha256": sha(frozen_preparation),
               "kernel_evidence": preparation["kernel_evidence"],
               "compiler_sha256": COMPILER, "source_and_import_artifacts_stable": before == after,
               "fixture_source_sha256": preparation["fixture_source_sha256"],
               "population_provider_source_sha256": preparation["population_provider_source_sha256"],
               "records": records, "evidence": str(evidence.relative_to(ROOT))}
    save(evidence / "RECEIPT.json", receipt)
    save(ROOT / "POPULATION-EXECUTION-RESULT.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "execution_mode", "evidence"]}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
