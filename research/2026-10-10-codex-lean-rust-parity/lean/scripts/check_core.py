#!/usr/bin/env python3
"""Fresh trust-zero core compilation plus complete owned declaration audit."""
from __future__ import annotations
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
MODULES = ["GParity.Rational", "GParity.Affine", "GParity.Count", "GParity.Chart", "GParity.Protocol", "GParity.Main"]
COMPILER = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
SUFFIXES = [".olean", ".olean.private", ".olean.server", ".ilean", ".ir"]

def sha(path: Path) -> str:
    return hashlib.file_digest(path.open("rb"), "sha256").hexdigest()

def save(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")

def bundle(path: Path):
    result = {}
    for suffix in SUFFIXES:
        p = path.with_suffix(suffix) if suffix in [".olean", ".ilean", ".ir"] else Path(str(path) + suffix[6:])
        if p.is_file():
            result[suffix] = sha(p)
    return result

def main():
    lean = Path(os.environ.get("CONNECTED_LEAN_BIN", "/workspace/toolchains/lean-4.33.1-linux/bin")) / "lean"
    assert sha(lean) == COMPILER
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/core" / stamp
    work = ROOT / ".build/core" / stamp
    obj = work / "objects"
    obj.mkdir(parents=True)
    evidence.mkdir(parents=True)
    std = lean.parent.parent / "lib/lean"
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [obj, std])), LEAN_NUM_THREADS="1")
    records = []

    def invoke(module: str, source: bytes, compile_object: bool):
        path = work / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(source)
        frozen = evidence / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(source)
        imports = re.findall(r"^import\s+([A-Za-z_][A-Za-z0-9_.]*)", source.decode(), re.M)
        bindings = {}
        for name in imports:
            rel = name.replace(".", "/") + ".olean"
            imported = next(p / rel for p in (obj, std) if (p / rel).is_file())
            bindings[name] = bundle(imported)
        command = [str(lean), "-j1", "-t0", "-M4096", "-Ddebug.skipKernelTC=false"]
        output = obj / (module.replace(".", "/") + ".olean")
        if compile_object:
            output.parent.mkdir(parents=True, exist_ok=True)
            command += ["-o", str(output)]
        command += [str(path.relative_to(work))]
        start = time.monotonic()
        result = subprocess.run(command, cwd=work, env=env, capture_output=True, timeout=180)
        stable = all(bindings[name] == bundle(next(p / (name.replace(".", "/") + ".olean")
            for p in (obj, std) if (p / (name.replace(".", "/") + ".olean")).is_file())) for name in imports)
        stable = stable and sha(lean) == COMPILER and path.read_bytes() == source
        (evidence / (module + ".stdout")).write_bytes(result.stdout)
        (evidence / (module + ".stderr")).write_bytes(result.stderr)
        rec = {"module": module, "source_sha256": hashlib.sha256(source).hexdigest(),
               "command": command, "exit_code": result.returncode,
               "elapsed_seconds": time.monotonic() - start, "direct_import_artifacts": bindings,
               "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
               "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
               "fresh_project_compilation": True, "source_and_imports_stable": stable,
               "compiler_identity_stable": sha(lean) == COMPILER}
        if result.returncode == 0 and compile_object:
            rec["output_artifacts"] = bundle(output)
        save(evidence / (module + ".receipt.json"), rec)
        records.append(rec)
        if result.returncode or not stable or b"sorryAx" in result.stdout + result.stderr:
            raise RuntimeError(result.stdout.decode(errors="replace") + result.stderr.decode(errors="replace"))

    for name in MODULES:
        invoke(name, (ROOT / (name.replace(".", "/") + ".lean")).read_bytes(), True)
    original = REPO / "research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean"
    template = original.read_text().replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]', "#" + json.dumps(MODULES)).replace("AUDIT-OWNED.json", "AUDIT-RESULT.json")
    audit_source = ("import GParity.Main\nimport Lean.Elab.Command\n" + template).encode()
    (evidence / "CoreAudit.lean").write_bytes(audit_source)
    invoke("CoreAudit", audit_source, False)
    audit = json.loads((work / "AUDIT-RESULT.json").read_bytes())
    assert audit["selected_modules"] == MODULES
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    save(evidence / "AUDIT-RESULT.json", audit)
    binary = ROOT / ".lake/build/bin/gparity"
    receipt = {"status": "PASS_FRESH_CORE_AND_COMPLETE_OWNED_AUDIT", "compiler_sha256": COMPILER,
               "trust_level": 0, "kernel_checking": True, "project_modules_fresh": MODULES,
               "standard_library_artifacts_reused": True, "mathlib_used": False,
               "records": records, "declarations": audit["declaration_count"],
               "theorem_declarations": audit["theorem_declaration_count"],
               "owned_axioms": 0, "nonstandard_axiom_rows": 0,
               "native_binary_sha256": sha(binary), "audit_sha256": sha(evidence / "AUDIT-RESULT.json"),
               "evidence": str(evidence.relative_to(ROOT)),
               "scope": "Exact executable arithmetic and protocol; no assertion of full G1-G7 scientific closure or native Rust theorem refinement."}
    save(evidence / "RECEIPT.json", receipt)
    save(ROOT / "CORE-CERTIFICATE.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "declarations", "theorem_declarations", "native_binary_sha256", "evidence"]}))

if __name__ == "__main__":
    main()
