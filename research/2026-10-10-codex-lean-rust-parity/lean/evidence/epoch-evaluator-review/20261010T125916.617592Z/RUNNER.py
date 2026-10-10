#!/usr/bin/env python3
"""Schedule one original evaluator differential with full artifact remeasurement."""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("configuration", type=Path)
    parser.add_argument("--family", choices=["epoch", "boundary"], required=True)
    parser.add_argument("--rust-probe", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--result-file", required=True)
    args = parser.parse_args()
    config_path = args.configuration.resolve()
    config = json.loads(config_path.read_bytes())
    assert config["status"] == "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING"
    original = ROOT / config["evidence"]
    artifacts = json.loads((original / "ACTUAL-IMPORTED-ARTIFACTS.json").read_bytes())
    native = json.loads((original / "NATIVE-RUNTIME-PINS.json").read_bytes())
    def measure():
        values = {str(config_path): sha(config_path), str(args.rust_probe.resolve()): sha(args.rust_probe.resolve())}
        for row in artifacts:
            p = Path(row["path"])
            assert p.stat().st_size == row["bytes"] and sha(p) == row["sha256"]
            values[str(p)] = row["sha256"]
        for path, row in native["libraries"].items():
            assert sha(Path(path)) == row["sha256"]
            values[path] = row["sha256"]
        assert sha(Path(config["compiler_path"])) == COMPILER
        assert sha(Path(config["driver_path"])) == config["driver_sha256"]
        return values
    before = measure()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence" / (args.family + "-evaluator-review") / stamp
    evidence.mkdir(parents=True)
    shutil_source = Path(__file__).read_bytes()
    (evidence / "RUNNER.py").write_bytes(shutil_source)
    (evidence / "EXECUTION-CONFIG.json").write_bytes(config_path.read_bytes())
    save(evidence / "BINDINGS-BEFORE.json", before)
    review = ROOT.parent / "design/review_compiled_fixtures.py"
    review_hash = sha(review)
    command = [sys.executable, str(review), "--family", args.family, "--rust-probe", str(args.rust_probe.resolve()),
        "--lean-execution-config", str(config_path), "--lean-artifact", str(original / "ACTUAL-IMPORTED-ARTIFACTS.json"),
        "--lean-artifact", str(original / "NATIVE-RUNTIME-PINS.json"), "--output", str(args.output.resolve())]
    for fixture in config["fixtures"]:
        command += ["--fixture", fixture]
    start = time.monotonic()
    with (evidence / "stdout").open("wb") as out, (evidence / "stderr").open("wb") as err:
        code = subprocess.run(command, stdout=out, stderr=err, timeout=65 * len(config["fixtures"]) + 60).returncode
    after = measure()
    save(evidence / "BINDINGS-AFTER.json", after)
    reviewed = json.loads((args.output / "RECEIPT.json").read_bytes())
    passed = code == 0 and reviewed["pass"] and before == after and sha(review) == review_hash
    result = {"status": "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL" if passed else "FAILED_DIFFERENTIAL_PRESERVED",
        "family": args.family, "execution_mode": config["execution_mode"], "standalone_elf_claimed": False,
        "command": command, "exit_code": code, "elapsed_seconds": time.monotonic() - start,
        "configuration_sha256": sha(config_path), "design_review_script_sha256": review_hash,
        "evidence": str(evidence.relative_to(ROOT)), "coefficient_review_evidence": str(args.output.resolve()),
        "coefficient_review_receipt_sha256": sha(args.output / "RECEIPT.json"),
        "fixtures_total": reviewed["cases_total"], "fixtures_passed": reviewed["cases_passed"],
        "all_actual_imported_artifacts_compiler_and_native_libraries_final_stable": before == after,
        "kernel_evidence": config["kernel_evidence"], "source_pins": config["source_pins"],
        "general_Rust_refinement_claimed": False, "scientific_provider_gates_promoted": False}
    save(evidence / "RECEIPT.json", result)
    destination = ROOT / args.result_file
    assert destination.parent == ROOT and destination.suffix == ".json"
    save(destination, result)
    print(json.dumps({k: result[k] for k in ["status", "fixtures_total", "fixtures_passed", "evidence"]}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
