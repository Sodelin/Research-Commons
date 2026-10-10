#!/usr/bin/env python3
"""Run unchanged coefficient smoke with the exact generated FinEnum runtime.

The original failed runtime attempts stay intact. This records an additional
native boundary and actual outputs; a full extended owned audit is separate.
"""
from __future__ import annotations
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from check_core import COMPILER, bundle, save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]


def main():
    previous_path = ROOT / "FINENUM-NATIVE-RESULT.json"
    previous = json.loads(previous_path.read_bytes())
    runtime_path = ROOT / "NATIVE-SYMBOL-CLOSURE-RESULT.json"
    runtime = json.loads(runtime_path.read_bytes())
    assert runtime["status"] == "PASS_EXACT_GENERATED_C_RUNTIME_LINK"
    assert runtime["leanc_identity_stable"] and runtime["source_and_generated_c_identities_stable"]
    plugin = Path(runtime["plugin_path"])
    assert sha(plugin) == runtime["plugin_sha256"]
    lean = Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")
    assert sha(lean) == COMPILER
    workspace = Path(previous["workspace"])
    graph_path = workspace / "DEPENDENCY-GRAPH.json"
    graph = json.loads(graph_path.read_bytes())["targets"]["evidence/g7-coefficient-codegen-smoke"]
    roots = [Path(p) for p in previous["lean_path"].split(os.pathsep)]
    prior_run = roots[0].parents[2]
    native = json.loads((prior_run / "NATIVE-RUNTIME-PINS.json").read_bytes())["libraries"]
    assert previous["generated_object_matches_accepted_provider"]
    sources, imports = {}, {}
    for module in graph["order"]:
        row = graph["modules"][module]
        source = workspace / "source-store" / (row["sha256"] + ".lean")
        assert sha(source) == row["sha256"]
        sources[module] = {"path": str(source), "source_sha256": row["sha256"], "imports": row["imports"]}
        if module != "G7EffectiveCoefficientSmoke":
            relative = module.replace(".", "/") + ".olean"
            path = next(root / relative for root in roots if (root / relative).is_file())
            imports[module] = {"path": str(path), "artifacts": bundle(path)}
    native = dict(native, **{str(plugin.resolve()): {"sha256": sha(plugin), "bytes": plugin.stat().st_size}})
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/finenum-smoke-runtime" / stamp
    work = ROOT / ".build/finenum-smoke-runtime" / stamp
    evidence.mkdir(parents=True)
    work.mkdir(parents=True)
    smoke = work / "G7EffectiveCoefficientSmoke.lean"
    shutil.copyfile(Path(sources["G7EffectiveCoefficientSmoke"]["path"]), smoke)
    shutil.copyfile(smoke, evidence / smoke.name)
    shutil.copyfile(Path(__file__), evidence / "RUNNER.py")
    save(evidence / "IMPORTED-PROVIDER-BINDINGS.json", imports)
    save(evidence / "SOURCE-IMPORT-CLOSURE.json", sources)
    save(evidence / "NATIVE-RUNTIME-PINS.json", native)
    preparation = {"source_graph_sha256": sha(graph_path), "original_failed_native_receipt_sha256": sha(previous_path),
        "linked_runtime_receipt_sha256": sha(runtime_path), "plugin_path": str(plugin), "plugin_sha256": sha(plugin),
        "compiler_sha256": COMPILER, "runner_sha256": sha(Path(__file__)), "source": sources["G7EffectiveCoefficientSmoke"],
        "lean_path": previous["lean_path"], "borrowed_checked_provider_count": len(imports),
        "all_sources_fresh_claimed": False, "global_dependency_or_toolchain_files_changed": False}
    save(evidence / "PREPARATION.json", preparation)
    def state():
        return {"compiler": sha(lean), "graph": sha(graph_path), "smoke": sha(smoke),
            "providers": {m: bundle(Path(row["path"])) for m, row in imports.items()},
            "sources": {m: sha(Path(row["path"])) for m, row in sources.items()},
            "native": {p: sha(Path(p)) for p in native}}
    before = state()
    output = work / "G7EffectiveCoefficientSmoke.olean"
    command = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false",
        "--load-dynlib=" + str(plugin), "-o", str(output), smoke.name]
    env = dict(os.environ, LEAN_PATH=previous["lean_path"], LEAN_NUM_THREADS="1",
               LD_DEBUG="libs", LD_DEBUG_OUTPUT=str(work / "NATIVE-LOADER"))
    start = time.monotonic()
    with (evidence / "stdout").open("wb") as out, (evidence / "stderr").open("wb") as err:
        try:
            code = subprocess.run(command, cwd=work, env=env, stdout=out, stderr=err, timeout=180).returncode
        except subprocess.TimeoutExpired:
            code = 124
    after = state()
    loader = sorted(work.glob("NATIVE-LOADER.*"))
    used = sorted({str(Path(value).resolve()) for p in loader
                   for value in re.findall(r"calling init:\s*(/[^\s]+)", p.read_text(errors="replace"))})
    loader_bound = bool(loader) and str(plugin.resolve()) in used and all(p in native for p in used)
    distributions = [distribute_file(p, evidence, Path(p.name), force_gzip=True) for p in loader]
    save(evidence / "COMPRESSED-DISTRIBUTIONS.json", {"status": "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION", "distributions": distributions})
    stdout, stderr = (evidence / "stdout").read_bytes(), (evidence / "stderr").read_bytes()
    passed = code == 0 and before == after and loader_bound and b"sorryAx" not in stdout + stderr
    result = dict(preparation, status="PASS_EXACT_ORIGINAL_SMOKE_WITH_GENERATED_NATIVE_PROVIDER" if passed else "FAILED_RUNTIME_ATTEMPT_PRESERVED",
        command=command, working_directory=str(work), exit_code=code, elapsed_seconds=time.monotonic() - start,
        cap_seconds=180, cap_memory_mib=4096, source_import_compiler_and_native_final_stable=before == after,
        actual_initialized_libraries=used, actual_native_libraries_bound=loader_bound,
        stdout_sha256=sha(evidence / "stdout"), stderr_sha256=sha(evidence / "stderr"),
        actual_stdout=stdout.decode(errors="replace"), loader_distributions=distributions,
        evidence=str(evidence.relative_to(ROOT)), full_extended_context_owned_audit_claimed=False,
        scope="Actual unchanged inherited coefficient smoke kernel elaboration and computations with exact original generated C runtime. No standalone ELF, all-source-fresh or full-context audit claim.")
    if passed:
        result["output_artifacts"] = bundle(output)
        result["output_path"] = str(output)
    save(evidence / "RECEIPT.json", result)
    save(ROOT / "FINENUM-SMOKE-RUNTIME-RESULT.json", result)
    print(json.dumps({k: result[k] for k in ["status", "exit_code", "actual_stdout", "evidence"]}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
