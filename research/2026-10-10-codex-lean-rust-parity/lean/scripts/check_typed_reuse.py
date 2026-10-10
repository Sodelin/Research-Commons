#!/usr/bin/env python3
"""Check constructive original-bank wrappers against the actual public providers.

Only component objects installed by this packet's fresh kernel runner are
admitted. Their source and complete import contexts are checked before reuse.
The new proof modules are compiled fresh. No narrowed provider or historical
certificate is silently attached to the original public compiler.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "reuse/sources"
NEW = ["GParity.Rational", "GParity.Affine", "GParity.Chart", "G6RationalAffineWitness",
       "G6AffineContradictionCertificate", "G6WireAffineRefinement", "G6WireContradictionRefinement",
       "G6WireAffineCapSemantics", "G6RationalNaturalCellWitness", "G6NaturalCellOrderedCompiler", "G6TwoTipChartFixture"]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--public-run", type=Path)
    args = parser.parse_args()
    lean = Path(os.environ.get("CONNECTED_LEAN_BIN", "/workspace/toolchains/lean-4.33.1-linux/bin")) / "lean"
    mathlib = Path(os.environ.get("CONNECTED_MATHLIB", "/workspace/dependencies/mathlib4"))
    assert sha(lean) == COMPILER
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip() == "0df444a360eaa60ab8c11dca51a86af692955474"
    public_run = args.public_run or Path(json.loads((ROOT / ".build/LATEST-RUN.json").read_bytes())["run"])
    public_context = public_run / "targets/current_connected/objects"
    graph = json.loads((ROOT / "DEPENDENCY-GRAPH.json").read_bytes())["targets"]["current/connected"]
    original = []
    seen = set()
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        for imported in graph["modules"][module]["imports"]:
            if imported in graph["modules"]:
                visit(imported)
        original.append(module)
    visit("NaturalCellAffineCompiler")
    admitted = {}
    for receipt in sorted((public_run / "attempts").glob("*/receipt.json")):
        rec = json.loads(receipt.read_bytes())
        if rec["kind"] == "component" and rec["status"] == "PASS_FRESH_KERNEL_CHECK":
            admitted[rec["module"]] = rec
    missing = [m for m in original if m not in admitted or not
               (public_context / (m.replace(".", "/") + ".olean")).is_file()]
    if missing:
        print(json.dumps({"status": "WAITING_CHECKED_PUBLIC_PROVIDERS", "missing": missing}))
        return 2
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/typed-reuse" / stamp
    work = ROOT / ".build/typed-reuse" / stamp
    obj = work / "objects"
    obj.mkdir(parents=True)
    evidence.mkdir(parents=True)
    external = sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")) + [mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [obj] + external)), LEAN_NUM_THREADS="1")
    provider_records = []
    for module in original:
        rec = admitted[module]
        source = ROOT / "source-store" / (graph["modules"][module]["sha256"] + ".lean")
        assert sha(source) == rec["source_sha256"] == graph["modules"][module]["sha256"]
        imported = public_context / (module.replace(".", "/") + ".olean")
        assert bundle(imported) == rec["object_artifacts"]
        frozen = evidence / "providers" / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(source.read_bytes())
        target = obj / (module.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(imported, target)
        provider_records.append({"module": module, "source_sha256": rec["source_sha256"],
            "status": "REUSED_EXACT_FRESH_PUBLIC_COMPONENT_CONTEXT", "artifacts": rec["object_artifacts"],
            "public_receipt_directory": rec["receipt_directory"], "direct_import_bindings": rec["direct_import_bindings"]})
    def binding(imported):
        rel = imported.replace(".", "/") + ".olean"
        path = next(p / rel for p in [obj] + external if (p / rel).is_file())
        return {"path": str(path), "artifacts": bundle(path)}
    for rec in provider_records:
        for imported, expected in rec["direct_import_bindings"].items():
            assert binding(imported)["artifacts"] == expected["artifacts"], (rec["module"], imported)
    save(evidence / "PUBLIC-PROVIDER-ADMISSION.json", provider_records)
    records = []
    snapshots = {m: ((ROOT / (m.replace(".", "/") + ".lean")) if m.startswith("GParity.") else SOURCE / (m + ".lean")).read_bytes() for m in NEW}
    for module, source in snapshots.items():
        path = work / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(source)
        frozen = evidence / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(source)
        imports = re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.decode(), re.M)
        before = {m: binding(m) for m in imports}
        output = obj / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", "-o", str(output), str(path.relative_to(work))]
        start = time.monotonic()
        result = subprocess.run(cmd, cwd=work, env=env, capture_output=True, timeout=180)
        (evidence / (module + ".stdout")).write_bytes(result.stdout)
        (evidence / (module + ".stderr")).write_bytes(result.stderr)
        stable = before == {m: binding(m) for m in imports} and path.read_bytes() == source and sha(lean) == COMPILER
        passed = result.returncode == 0 and stable and b"sorryAx" not in result.stdout + result.stderr
        rec = {"module": module, "status": "PASS_FRESH_KERNEL_CHECK" if passed else "FAILED_ATTEMPT_PRESERVED",
            "source_sha256": hashlib.sha256(source).hexdigest(), "command": cmd,
            "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - start,
            "direct_import_bindings": before, "source_and_imports_stable": stable,
            "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(), "stderr_sha256": hashlib.sha256(result.stderr).hexdigest()}
        if passed:
            rec["output_artifacts"] = bundle(output)
        save(evidence / (module + ".receipt.json"), rec)
        records.append(rec)
        if not passed:
            save(evidence / "RECEIPT.json", {"status": "FAILED_ATTEMPT_PRESERVED", "records": records, "provider_records": provider_records})
            print(result.stdout.decode(errors="replace"), end="")
            print(result.stderr.decode(errors="replace"), end="")
            return 1
    selected = original + NEW
    template = (ROOT / "scripts/AuditTemplate.lean").read_text().replace(
        '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]', "#" + json.dumps(selected)).replace("AUDIT-OWNED.json", "AUDIT-RESULT.json")
    audit = work / "TypedReuseAudit.lean"
    audit.write_text("import G6TwoTipChartFixture\nimport G6WireContradictionRefinement\nimport G6WireAffineCapSemantics\nimport Lean.Elab.Command\n" + template)
    (evidence / "TypedReuseAudit.lean").write_bytes(audit.read_bytes())
    audit_source_sha = sha(audit)
    audit_bindings = {m: binding(m) for m in selected + ["Lean.Elab.Command"]}
    cmd = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", str(audit.relative_to(work))]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=work, env=env, capture_output=True, timeout=180)
    (evidence / "TypedReuseAudit.stdout").write_bytes(result.stdout)
    (evidence / "TypedReuseAudit.stderr").write_bytes(result.stderr)
    audit_stable = audit_source_sha == sha(audit) and sha(lean) == COMPILER and audit_bindings == {
        m: binding(m) for m in audit_bindings}
    save(evidence / "TypedReuseAudit.receipt.json", {"command": cmd,
        "source_sha256": audit_source_sha, "exit_code": result.returncode,
        "direct_and_selected_import_bindings": audit_bindings,
        "source_compiler_and_imports_stable": audit_stable,
        "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(result.stderr).hexdigest()})
    if result.returncode or not audit_stable or b"sorryAx" in result.stdout + result.stderr:
        save(evidence / "RECEIPT.json", {"status": "AUDIT_FAILED_PRESERVED", "records": records, "provider_records": provider_records})
        print(result.stdout.decode(errors="replace"), end="")
        return 1
    audit_result = json.loads((work / "AUDIT-RESULT.json").read_bytes())
    assert audit_result["selected_modules"] == selected
    assert not audit_result["owned_axioms"] and not audit_result["nonstandard_axiom_rows"] and not audit_result["missing_modules"]
    save(evidence / "AUDIT-RESULT.json", audit_result)
    receipt = {"status": "PASS_ORIGINAL_BANK_AND_NATIVE_TWO_TIP_COMPILER_FIXTURES", "compiler_sha256": COMPILER,
        "trust_level": 0, "kernel_checking": True, "all_new_modules_fresh": True,
        "original_public_provider_modules_reused": len(original), "original_provider_imports_changed": False,
        "provider_records": provider_records, "new_module_records": records, "public_run": str(public_run),
        "selected_modules": selected, "declarations": audit_result["declaration_count"],
        "theorems": audit_result["theorem_declaration_count"], "owned_axioms": [], "nonstandard_axiom_rows": [],
        "audit_elapsed_seconds": time.monotonic()-start, "evidence": str(evidence.relative_to(ROOT)),
        "object_directory": str(obj), "scope": "Constructive original typed cell bank, ordered typed compiler erasure, two literal native chart fixtures; general parser/graph and whole native solver refinements remain separate."}
    save(evidence / "RECEIPT.json", receipt)
    save(ROOT / "TYPED-REUSE-CERTIFICATE.json", receipt)
    print(json.dumps({k:receipt[k] for k in ["status", "declarations", "theorems", "evidence", "object_directory"]}))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
