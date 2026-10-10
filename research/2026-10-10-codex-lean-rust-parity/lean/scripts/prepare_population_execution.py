#!/usr/bin/env python3
"""Bind an import-only evaluator driver to an accepted original fixture audit.

This preparation runs no evaluator and claims no standalone native ELF.
The inherited executable coefficients are loaded from the checked exact
context. All actually imported companions and conservative native libraries
are measured again before publishing the command for independent comparison.
"""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
TARGET = "extraction/original-population-fixture"
FIXTURES = ["emptyEdge0", "oneAncestral", "twoAncestral", "threeEdge0", "fourAncestral",
            "carriedNonminimum", "permutedRestrictedEdge0", "frozenRegisterRepeat"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    work = args.workspace.resolve()
    final = json.loads((work / ".build/LATEST-RUN.json").read_bytes())
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS" and final["targets_passed"] == [TARGET]
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    run = Path(final["run"])
    target = run / "targets" / TARGET.replace("/", "_")
    result_path = target / "RESULT.json"
    result = json.loads(result_path.read_bytes())
    for key in ["aggregate_receipt", "audit_receipt"]:
        assert result[key]["status"] == "PASS_FRESH_KERNEL_CHECK"
    audit_path = Path(result["audit_receipt"]["audit_output"])
    audit = json.loads(audit_path.read_bytes())
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    preparation = json.loads((work / "PREPARATION.json").read_bytes())
    archived_run = Path(preparation["evidence"]) / ("run-" + run.name)
    assert (archived_run / "PRESERVATION-MANIFEST.json").is_file()
    frozen_result = archived_run / result_path.relative_to(run)
    assert frozen_result.read_bytes() == result_path.read_bytes()
    imported_path = target / "ACTUAL-IMPORTED-ARTIFACTS.json"
    imported = json.loads(imported_path.read_bytes())
    for row in imported:
        p = Path(row["path"])
        assert p.stat().st_size == row["bytes"] and sha(p) == row["sha256"], p
    native_path = run / "NATIVE-RUNTIME-PINS.json"
    native = json.loads(native_path.read_bytes())
    for path, row in native["libraries"].items():
        assert sha(Path(path)) == row["sha256"], path
    lean = Path(os.environ.get("CONNECTED_LEAN_BIN", "/workspace/toolchains/lean-4.33.1-linux/bin")) / "lean"
    mathlib = Path(os.environ.get("CONNECTED_MATHLIB", "/workspace/dependencies/mathlib4"))
    assert sha(lean) == COMPILER
    external = sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")) + [
        mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    lean_path = os.pathsep.join(map(str, [target / "objects"] + external))
    driver = work / "OriginalPopulationRunner.lean"
    body = b"import G7OriginalPopulationFixture\n"
    if driver.exists():
        assert driver.read_bytes() == body
    else:
        driver.write_bytes(body)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/source-population-execution" / stamp
    evidence.mkdir(parents=True)
    (evidence / driver.name).write_bytes(body)
    save(evidence / "ACTUAL-IMPORTED-ARTIFACTS.json", imported)
    save(evidence / "NATIVE-RUNTIME-PINS.json", native)
    command = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", "--run", str(driver)]
    receipt = {"status": "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING",
               "execution_mode": "Lean compiled evaluator, not standalone extracted ELF",
               "command_prefix": command, "lean_path": lean_path, "workdir": str(work),
               "driver_path": str(driver), "driver_sha256": sha(driver),
               "compiler_path": str(lean), "compiler_sha256": COMPILER,
               "fixtures": FIXTURES, "fixture_source_sha256": preparation["source_pins"]["G7OriginalPopulationFixture"],
               "population_provider_source_sha256": preparation["source_pins"]["G7EffectivePopulationCoefficients"],
               "support_source_sha256": preparation["source_pins"]["G7EffectiveCoefficientSupport"],
               "encoding_image_source_sha256": preparation["source_pins"]["G7EncodedMergerSupport"],
               "kernel_run": str(run), "kernel_result_sha256": sha(frozen_result),
               "kernel_evidence": str(archived_run.relative_to(ROOT)),
               "closure_modules": result["closure_modules"], "declarations": result["declarations"],
               "theorems": result["theorems"], "owned_axioms": [], "nonstandard_axiom_rows": [],
               "actual_imported_artifact_count": len(imported), "all_imported_artifacts_remeasured": True,
               "native_runtime_digest": native["native_runtime_digest"],
               "evidence": str(evidence.relative_to(ROOT)),
               "scope": "Eight fixed original-source coefficient rows with full literal destination and unordered fibre output. No general LAW quotient or Rust theorem refinement is inferred."}
    save(evidence / "PREPARATION.json", receipt)
    save(ROOT / "POPULATION-EXECUTION-PREPARATION.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "command_prefix", "lean_path", "kernel_evidence"]}))


if __name__ == "__main__":
    main()
