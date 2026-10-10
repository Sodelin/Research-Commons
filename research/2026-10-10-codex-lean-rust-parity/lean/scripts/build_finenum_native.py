#!/usr/bin/env python3
"""Generate isolated native code for the exact official enumeration provider.

This adds no file to global Mathlib or the toolchain. The smoke source remains
byte-identical; native generation and its first actual replay have independent
receipts, without assigning a new full-context theorem acceptance.
"""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
FINENUM = "381c6f445637fdf6bc04a77f062ed2079d9856eeb260b30b609f3c098a3e430a"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    final = json.loads((workspace / ".build/LATEST-RUN.json").read_bytes())
    run = Path(final["run"])
    target = "evidence/g7-coefficient-codegen-smoke"
    result = json.loads((run / "targets/evidence_g7-coefficient-codegen-smoke/RESULT.json").read_bytes())
    provider = next(r for r in result["component_receipts"] if r["module"] == "Mathlib.Data.FinEnum")
    assert provider["status"] == "PASS_FRESH_KERNEL_CHECK" and provider["source_sha256"] == FINENUM
    graph = json.loads((workspace / "DEPENDENCY-GRAPH.json").read_bytes())["targets"][target]
    lean = Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")
    leanc = lean.with_name("leanc")
    mathlib = Path("/workspace/dependencies/mathlib4")
    assert sha(lean) == COMPILER
    objects = run / "targets/evidence_g7-coefficient-codegen-smoke/objects"
    roots = [objects] + sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")) + [
        mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    bindings = {}
    for module in graph["modules"]["Mathlib.Data.FinEnum"]["imports"]:
        relative = module.replace(".", "/") + ".olean"
        path = next(root / relative for root in roots if (root / relative).is_file())
        bindings[module] = {"path": str(path), "artifacts": bundle(path)}
        assert bindings[module]["artifacts"] == provider["direct_import_artifacts"][module]
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/native-finenum" / stamp
    evidence = ROOT / "evidence/native-finenum" / stamp
    source = work / "Mathlib/Data/FinEnum.lean"
    source.parent.mkdir(parents=True)
    evidence.mkdir(parents=True)
    original = workspace / "source-store" / (FINENUM + ".lean")
    assert sha(original) == FINENUM
    shutil.copyfile(original, source)
    shutil.copyfile(original, evidence / "FinEnum.lean")
    shutil.copyfile(mathlib / "LICENSE", evidence / "LICENSE")
    smoke_hash = graph["modules"]["G7EffectiveCoefficientSmoke"]["sha256"]
    smoke = work / "G7EffectiveCoefficientSmoke.lean"
    shutil.copyfile(workspace / "source-store" / (smoke_hash + ".lean"), smoke)
    assert sha(smoke) == smoke_hash
    shutil.copyfile(smoke, evidence / smoke.name)
    code = work / "FinEnum.c"
    plugin = work / "libOriginalFinEnum.so"
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, roots)), LEAN_NUM_THREADS="1")
    records = []
    def invoke(label, command, seconds):
        before = sha(lean), sha(source), sha(smoke), {m: bundle(Path(r["path"])) for m, r in bindings.items()}
        start = time.monotonic()
        with (evidence / (label + ".stdout")).open("wb") as out, (evidence / (label + ".stderr")).open("wb") as err:
            try:
                proc = subprocess.run(command, cwd=work, env=env, stdout=out, stderr=err, timeout=seconds)
                status = proc.returncode
            except subprocess.TimeoutExpired:
                status = 124
        after = sha(lean), sha(source), sha(smoke), {m: bundle(Path(r["path"])) for m, r in bindings.items()}
        log = (evidence / (label + ".stdout")).read_bytes() + (evidence / (label + ".stderr")).read_bytes()
        passed = status == 0 and before == after and b"sorryAx" not in log
        record = {"status": "PASS" if passed else "FAILED_ATTEMPT_PRESERVED", "step": label,
                  "command": command, "working_directory": str(work), "exit_code": status,
                  "cap_seconds": seconds, "elapsed_seconds": time.monotonic() - start,
                  "source_compiler_and_direct_imports_stable": before == after,
                  "stdout_sha256": sha(evidence / (label + ".stdout")),
                  "stderr_sha256": sha(evidence / (label + ".stderr"))}
        records.append(record)
        save(evidence / (label + ".receipt.json"), record)
        return passed
    flags = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false"]
    generated = invoke("official-source-codegen", flags + ["-c", str(code), "-o", str(work / "FinEnum.olean"),
                        "Mathlib/Data/FinEnum.lean"], 180)
    native = generated and invoke("native-compile", [str(leanc), "-O2", "-shared", "-fPIC", "-o", str(plugin), str(code)], 180)
    executed = native and invoke("unchanged-original-smoke-replay", flags + ["--load-dynlib=" + str(plugin),
                               "G7EffectiveCoefficientSmoke.lean"], 180)
    certificate = {"status": "PASS_ISOLATED_FINENUM_CODEGEN_AND_ORIGINAL_SMOKE_REPLAY" if executed else "FAILED_NATIVE_ATTEMPT_PRESERVED",
                   "workspace": str(workspace), "work": str(work), "evidence": str(evidence.relative_to(ROOT)),
                   "original_provider_sha256": FINENUM, "original_smoke_sha256": smoke_hash,
                   "compiler_sha256": COMPILER, "leanc_sha256": sha(leanc),
                   "direct_import_bindings": bindings, "lean_path": env["LEAN_PATH"], "records": records,
                   "global_dependency_or_toolchain_files_changed": False,
                   "full_context_owned_audit_claimed": False,
                   "scope": "Actual exact-source native dependency and unchanged smoke execution; full extended native-boundary audit remains separate."}
    if generated:
        certificate["generated_c_sha256"] = sha(code)
        certificate["generated_object_artifacts"] = bundle(work / "FinEnum.olean")
        certificate["accepted_provider_artifacts"] = provider["object_artifacts"]
        certificate["generated_object_matches_accepted_provider"] = bundle(work / "FinEnum.olean") == provider["object_artifacts"]
    if native:
        certificate["plugin_path"] = str(plugin)
        certificate["plugin_sha256"] = sha(plugin)
    save(evidence / "RECEIPT.json", certificate)
    save(ROOT / "FINENUM-NATIVE-RESULT.json", certificate)
    print(json.dumps({k: certificate[k] for k in ["status", "evidence", "full_context_owned_audit_claimed"]}))
    return 0 if executed else 1


if __name__ == "__main__":
    raise SystemExit(main())
