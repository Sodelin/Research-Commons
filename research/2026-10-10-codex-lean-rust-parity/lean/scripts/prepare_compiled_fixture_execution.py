#!/usr/bin/env python3
"""Pin an import-only driver to a freshly audited original fixture context."""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import re
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--target", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--fixture", action="append", required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--result-file", required=True)
    parser.add_argument("--native-provider", type=Path, action="append", default=[])
    args = parser.parse_args()
    work = args.workspace.resolve()
    final = json.loads((work / ".build/LATEST-RUN.json").read_bytes())
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS" and args.target in final["targets_passed"]
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    run = Path(final["run"])
    target = run / "targets" / re.sub("[^A-Za-z0-9_-]", "_", args.target)
    result_path = target / "RESULT.json"
    result = json.loads(result_path.read_bytes())
    assert result["status"] == "PASS"
    assert result["aggregate_receipt"]["status"] == result["audit_receipt"]["status"] == "PASS_FRESH_KERNEL_CHECK"
    audit = json.loads(Path(result["audit_receipt"]["audit_output"]).read_bytes())
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    prep = json.loads((work / "PREPARATION.json").read_bytes())
    graph = json.loads((work / "DEPENDENCY-GRAPH.json").read_bytes())["targets"][args.target]
    assert args.module in graph["roots"] and audit["selected_modules"] == graph["order"]
    saved = Path(prep["evidence"]) / ("run-" + run.name)
    preserved = json.loads((saved / "PRESERVATION-MANIFEST.json").read_bytes())
    assert preserved["actual_run"] == str(run)
    artifacts = json.loads((target / "ACTUAL-IMPORTED-ARTIFACTS.json").read_bytes())
    for row in artifacts:
        path = Path(row["path"])
        assert sha(path) == row["sha256"] and path.stat().st_size == row["bytes"]
    native = json.loads((run / "NATIVE-RUNTIME-PINS.json").read_bytes())
    native = dict(native, libraries=dict(native["libraries"]))
    for provider in args.native_provider:
        provider = provider.resolve()
        native["libraries"][str(provider)] = {"sha256": sha(provider), "bytes": provider.stat().st_size}
    for path, row in native["libraries"].items():
        assert sha(Path(path)) == row["sha256"]
    lean = Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")
    mathlib = Path("/workspace/dependencies/mathlib4")
    assert sha(lean) == COMPILER
    external = sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")) + [mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    lean_path = os.pathsep.join(map(str, [target / "objects"] + external))
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence" / args.label / stamp
    assert evidence.is_relative_to(ROOT / "evidence")
    evidence.mkdir(parents=True)
    driver = work / ("Runner_" + args.module + ".lean")
    body = ("import " + args.module + "\n").encode()
    assert not driver.exists() or driver.read_bytes() == body
    driver.write_bytes(body)
    (evidence / driver.name).write_bytes(body)
    save(evidence / "ACTUAL-IMPORTED-ARTIFACTS.json", artifacts)
    save(evidence / "NATIVE-RUNTIME-PINS.json", native)
    command = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false"]
    command += ["--load-dynlib=" + str(p.resolve()) for p in args.native_provider]
    command += ["--run", str(driver)]
    config = {"status": "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING",
        "execution_mode": "compiled_lean_evaluator_not_standalone_elf", "compiler_path": str(lean),
        "compiler_sha256": COMPILER, "driver_path": str(driver), "driver_sha256": sha(driver),
        "command_prefix": command, "lean_path": lean_path, "workdir": str(work), "fixtures": args.fixture,
        "entrypoint_module": args.module, "source_pins": prep["source_pins"], "kernel_run": str(run),
        "kernel_evidence": str(saved.relative_to(ROOT)), "kernel_result_sha256": sha(result_path),
        "kernel_preservation_manifest_sha256": sha(saved / "PRESERVATION-MANIFEST.json"),
        "closure_modules": result["closure_modules"], "owned_declarations": result["declarations"],
        "owned_theorems": result["theorems"], "owned_axioms": [], "nonstandard_axiom_rows": [],
        "actual_imported_artifact_count": len(artifacts), "evidence": str(evidence.relative_to(ROOT)),
        "additional_native_provider_boundary": [str(p.resolve()) for p in args.native_provider],
        "scope": "Only the named original-source compiled fixtures. This execution configuration supplies no standalone ELF or universal Rust refinement claim."}
    save(evidence / "PREPARATION.json", config)
    destination = ROOT / args.result_file
    assert destination.parent == ROOT and destination.suffix == ".json"
    save(destination, config)
    print(json.dumps({k: config[k] for k in ["status", "command_prefix", "kernel_evidence", "evidence"]}))


if __name__ == "__main__":
    main()
