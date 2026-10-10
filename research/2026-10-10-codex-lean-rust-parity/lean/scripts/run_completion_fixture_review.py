#!/usr/bin/env python3
"""Schedule the six original completion comparisons with full remeasurement.

Contributor: Codex / lean_integration_successor, 2026-10-10. Derived from the
separately preserved epoch/boundary scheduler; the independent design comparator
retains ownership of the reference, complete-row checks and adversarial controls.
"""
from __future__ import annotations
import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys
import time
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
REVIEW_SHA = "f87671690a634f9a7c12094828f7b5e5b39fc36ef9bf32f142098d08e35f2602"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("configuration", type=Path)
    parser.add_argument("--rust-probe", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--result-file", required=True)
    args = parser.parse_args()
    config_path = args.configuration.resolve()
    config = json.loads(config_path.read_bytes())
    assert config["status"] == "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING"
    assert config["execution_mode"] == "compiled_lean_evaluator_not_standalone_elf"
    assert config["entrypoint_module"] == "G7OriginalCompletionFixtureMain"
    assert config["source_pins"]["G7OriginalCompletionFixture"] == "f8c08aecad9d500d8bdcb49368d9bd43919210f4eeb31296c297e4d1b1363dc5"
    assert config["source_pins"]["G7OriginalCompletionFixtureMain"] == "67be7182eb7343b56636ede6fcff3952a6ebe883ef1d93b968305337e140a13e"
    original = ROOT / config["evidence"]
    artifacts_path = original / "ACTUAL-IMPORTED-ARTIFACTS.json"
    native_path = original / "NATIVE-RUNTIME-PINS.json"
    artifacts = json.loads(artifacts_path.read_bytes())
    native = json.loads(native_path.read_bytes())
    review = ROOT.parent / "design/review_completion_compiled_fixtures.py"
    assert sha(review) == REVIEW_SHA

    def measure():
        values = {str(p): sha(p) for p in [config_path, args.rust_probe.resolve(), review,
                  artifacts_path, native_path]}
        for row in artifacts:
            path = Path(row["path"])
            assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"]
            values[str(path)] = row["sha256"]
        for name, row in native["libraries"].items():
            path = Path(name)
            assert path.stat().st_size == row["bytes"] and sha(path) == row["sha256"]
            values[name] = row["sha256"]
        assert sha(Path(config["compiler_path"])) == COMPILER
        assert sha(Path(config["driver_path"])) == config["driver_sha256"]
        values[config["compiler_path"]] = COMPILER
        values[config["driver_path"]] = config["driver_sha256"]
        return values

    before = measure()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/completion-evaluator-review" / stamp
    evidence.mkdir(parents=True)
    (evidence / "RUNNER.py").write_bytes(Path(__file__).read_bytes())
    for source, name in [(config_path, "EXECUTION-CONFIG.json"),
                         (artifacts_path, artifacts_path.name), (native_path, native_path.name)]:
        (evidence / name).write_bytes(source.read_bytes())
    save(evidence / "BINDINGS-BEFORE.json", before)
    command = [sys.executable, str(review), "--rust-word-probe", str(args.rust_probe.resolve()),
        "--lean-execution-config", str(config_path), "--lean-artifact", str(artifacts_path),
        "--lean-artifact", str(native_path), "--output", str(args.output.resolve())]
    for fixture in config["fixtures"]:
        command += ["--fixture", fixture]
    start = time.monotonic()
    code = None
    errors = []
    with (evidence / "stdout").open("wb") as out, (evidence / "stderr").open("wb") as err:
        try:
            code = subprocess.run(command, stdout=out, stderr=err,
                                  timeout=65 * len(config["fixtures"]) + 60).returncode
        except (OSError, subprocess.TimeoutExpired) as error:
            errors.append(repr(error))
    try:
        after = measure()
    except (AssertionError, OSError) as error:
        after = {}
        errors.append("Final artifact measurement failed: " + repr(error))
    save(evidence / "BINDINGS-AFTER.json", after)
    review_receipt = args.output.resolve() / "RECEIPT.json"
    reviewed = json.loads(review_receipt.read_bytes()) if review_receipt.exists() else {}
    passed = code == 0 and reviewed.get("pass", False) and before == after and not errors
    result = {"status": "PASS_CHECKED_ORIGINAL_EVALUATOR_DIFFERENTIAL" if passed else "FAILED_DIFFERENTIAL_PRESERVED",
        "family": "completion", "execution_mode": config["execution_mode"], "standalone_elf_claimed": False,
        "command": command, "exit_code": code, "errors": errors, "elapsed_seconds": time.monotonic() - start,
        "configuration_sha256": sha(config_path), "design_review_script_sha256": REVIEW_SHA,
        "scheduler_sha256": sha(Path(__file__)), "evidence": str(evidence.relative_to(ROOT)),
        "coefficient_review_evidence": str(args.output.resolve()),
        "coefficient_review_receipt_sha256": sha(review_receipt) if review_receipt.exists() else None,
        "fixtures_total": reviewed.get("cases_total", len(config["fixtures"])),
        "fixtures_passed": reviewed.get("cases_passed", 0),
        "full_view_rows_total": reviewed.get("full_view_rows_total", 0),
        "invalid_table_controls_rejected": reviewed.get("invalid_table_controls_rejected", []),
        "languages_executed": reviewed.get("languages_executed", []),
        "all_actual_imported_artifacts_compiler_and_native_libraries_final_stable": before == after,
        "kernel_evidence": config["kernel_evidence"], "source_pins": config["source_pins"],
        "general_Rust_refinement_claimed": False, "scientific_provider_gates_promoted": False}
    save(evidence / "RECEIPT.json", result)
    destination = ROOT / args.result_file
    assert destination.parent == ROOT and destination.suffix == ".json"
    save(destination, result)
    print(json.dumps({k: result[k] for k in ["status", "fixtures_total", "fixtures_passed", "full_view_rows_total", "evidence"]}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
