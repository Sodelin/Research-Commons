#!/usr/bin/env python3
"""Compile the newly added arithmetic reuse chain with exact source receipts.

The original provider body is preserved. Its broad tactic import is replaced by
explicit tactic/data imports in a separate context with a new source identity.
The historical provider certificate is not attached to these replacement bytes.
"""
from __future__ import annotations
import datetime
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import time
from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
SOURCE = ROOT.parent / "reuse/sources"
IMPORTS = ["Mathlib.Data.Real.Basic", "Mathlib.Algebra.BigOperators.Fin",
           "Mathlib.Tactic.FieldSimp", "Mathlib.Tactic.Linarith", "Mathlib.Tactic.Ring", "Mathlib.Tactic.Order"]
MODULES = ["GParity.Rational", "GParity.Affine", "StrictAffineElimination",
           "G6RationalAffineWitness", "G6AffineContradictionCertificate", "G6WireAffineRefinement",
           "G6WireContradictionRefinement", "G6WireAffineCapSemantics"]

def main():
    lean = Path(os.environ.get("CONNECTED_LEAN_BIN", "/workspace/toolchains/lean-4.33.1-linux/bin")) / "lean"
    mathlib = Path(os.environ.get("CONNECTED_MATHLIB", "/workspace/dependencies/mathlib4"))
    assert sha(lean) == COMPILER
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip() == "0df444a360eaa60ab8c11dca51a86af692955474"
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/reuse" / stamp
    work = ROOT / ".build/reuse" / stamp
    obj = work / "objects"
    obj.mkdir(parents=True)
    evidence.mkdir(parents=True)
    external = sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")) + [mathlib / ".lake/build/lib/lean", lean.parent.parent / "lib/lean"]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [obj] + external)), LEAN_NUM_THREADS="1")
    original = REPO / "research/2026-10-09-dot-g6-proved-natural-cell-decision-1902z/StrictAffineElimination.lean"
    old = original.read_bytes()
    assert old.count(b"import Mathlib.Tactic\n") == 1
    derived = old.replace(b"import Mathlib.Tactic\n", ("\n".join("import " + n for n in IMPORTS) + "\n").encode())
    transformation = {"original_path": str(original.relative_to(REPO)), "original_sha256": hashlib.sha256(old).hexdigest(),
                      "derived_sha256": hashlib.sha256(derived).hexdigest(), "only_change": "Replace Mathlib.Tactic import with exact data/tactic imports.",
                      "original_theorem_body_bytes_unchanged": True, "imports_added": IMPORTS,
                      "historical_receipt_attached_to_derived_bytes": False}
    save(evidence / "IMPORT-TRANSFORMATION.json", transformation)
    sources = {}
    for name in MODULES:
        if name == "StrictAffineElimination": sources[name] = derived
        elif name.startswith("GParity."): sources[name] = (ROOT / (name.replace(".", "/") + ".lean")).read_bytes()
        else: sources[name] = (SOURCE / (name + ".lean")).read_bytes()
    records = []
    for name, source in sources.items():
        frozen = work / (name.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(source)
        (evidence / (name + ".lean")).write_bytes(source)
        output = obj / (name.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", "-o", str(output), str(frozen.relative_to(work))]
        imports = re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.decode(), re.M)
        def bindings():
            found = {}
            for imported in imports:
                rel = imported.replace(".", "/") + ".olean"
                path = next(p / rel for p in [obj] + external if (p / rel).is_file())
                found[imported] = {"path": str(path), "artifacts": bundle(path)}
            return found
        before = bindings()
        start = time.monotonic()
        result = subprocess.run(command, env=env, cwd=work, capture_output=True, timeout=180)
        after = bindings()
        stable = before == after and frozen.read_bytes() == source and sha(lean) == COMPILER
        (evidence / (name + ".stdout")).write_bytes(result.stdout)
        (evidence / (name + ".stderr")).write_bytes(result.stderr)
        rec = {"module": name, "source_sha256": hashlib.sha256(source).hexdigest(), "command": command,
               "exit_code": result.returncode, "elapsed_seconds": time.monotonic()-start,
               "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(), "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
               "direct_import_bindings": before, "source_and_imports_stable": stable,
               "compiler_identity_stable": sha(lean) == COMPILER}
        if result.returncode == 0: rec["output_artifacts"] = bundle(output)
        save(evidence / (name + ".receipt.json"), rec)
        records.append(rec)
        if result.returncode or not stable or b"sorryAx" in result.stdout + result.stderr:
            save(evidence / "RECEIPT.json", {"status": "FAILED_ATTEMPT_PRESERVED", "records": records, "failed_module": name})
            print(result.stdout.decode(errors="replace"), end="")
            print(result.stderr.decode(errors="replace"), end="")
            return 1
    template = (REPO / "research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean").read_text()
    template = template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]', "#" + json.dumps(MODULES)).replace("AUDIT-OWNED.json", "AUDIT-RESULT.json")
    audit = work / "ReuseAudit.lean"
    audit.write_text("import G6WireContradictionRefinement\nimport G6WireAffineCapSemantics\nimport Lean.Elab.Command\n" + template)
    (evidence / "ReuseAudit.lean").write_bytes(audit.read_bytes())
    cmd = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false", str(audit.relative_to(work))]
    result = subprocess.run(cmd, env=env, cwd=work, capture_output=True, timeout=180)
    (evidence / "ReuseAudit.stdout").write_bytes(result.stdout)
    (evidence / "ReuseAudit.stderr").write_bytes(result.stderr)
    if result.returncode:
        save(evidence / "RECEIPT.json", {"status": "AUDIT_FAILED_PRESERVED", "records": records})
        print(result.stdout.decode(errors="replace"), end="")
        return 1
    audit_result = json.loads((work / "AUDIT-RESULT.json").read_bytes())
    save(evidence / "AUDIT-RESULT.json", audit_result)
    assert audit_result["selected_modules"] == MODULES
    assert not audit_result["owned_axioms"] and not audit_result["nonstandard_axiom_rows"] and not audit_result["missing_modules"]
    assert all(b"sorryAx" not in (evidence / (name + ".stdout")).read_bytes() for name in MODULES)
    receipt = {"status": "PASS_NEW_ARITHMETIC_REUSE_AND_WIRE_CHECKER", "compiler_sha256": COMPILER,
               "trust_level": 0, "kernel_checking": True, "all_project_modules_fresh": True,
               "mathlib_source_build_reused": True, "modules": MODULES, "records": records,
               "declarations": audit_result["declaration_count"], "theorems": audit_result["theorem_declaration_count"],
               "owned_axioms": audit_result["owned_axioms"], "nonstandard_axiom_rows": audit_result["nonstandard_axiom_rows"],
               "missing_modules": audit_result["missing_modules"], "transformation": transformation,
               "evidence": str(evidence.relative_to(ROOT)), "object_directory": str(obj)}
    save(evidence / "RECEIPT.json", receipt)
    save(ROOT / "REUSE-CERTIFICATE.json", receipt)
    print(json.dumps({k:receipt[k] for k in ["status","declarations","theorems","evidence","object_directory"]}))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
