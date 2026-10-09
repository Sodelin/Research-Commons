#!/usr/bin/env python3
"""Serial kernel replay of only two additive modules; never rebuild old 181 sources.

The caller supplies the pinned scratch runtime and already built pinned Mathlib.
Run outputs live in a new scratch directory and a separately supplied evidence dir.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

COMPILER_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"
MODULES = ["UnifiedLean.G3.ConditionalZeroScoreBound", "UnifiedLean.G3.ConditionalZeroScoreConsumer"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--mathlib", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, default=Path("/workspace/scratch"))
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[3]
    package = repo / "research/2026-10-04-dot-verified-lean-825-0203z/package/baseline"
    lean = args.lean_bin.resolve() / "lean"
    mathlib = args.mathlib.resolve()
    assert digest(lean) == COMPILER_SHA, "Compiler hash mismatch"
    assert subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip() == MATHLIB_COMMIT
    pinned_manifest = subprocess.check_output(["git", "-C", str(mathlib), "show", "HEAD:lake-manifest.json"])
    assert (mathlib / "lake-manifest.json").read_bytes() == pinned_manifest, "Mathlib dependency manifest drift"
    dependency_pins = {}
    for dep in json.loads(pinned_manifest)["packages"]:
        dep_path = mathlib / ".lake/packages" / dep["name"]
        actual = subprocess.check_output(["git", "-C", str(dep_path), "rev-parse", "HEAD"], text=True).strip()
        assert actual == dep["rev"], (dep["name"], actual, dep["rev"])
        dependency_pins[dep["name"]] = actual
    args.scratch.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix="conditional-zero-score-", dir=args.scratch)).resolve()
    args.evidence.mkdir(parents=True, exist_ok=False)
    objects = run / "objects"
    objects.mkdir()
    imports = [objects, *sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")), mathlib / ".lake/build/lib/lean"]
    env = dict(os.environ, LEAN_PATH=":".join(map(str, imports)), LEAN_NUM_THREADS="1")
    commands = []
    receipt = {
        "status": "RUNNING", "run": str(run), "compiler_sha256": COMPILER_SHA,
        "mathlib_commit": MATHLIB_COMMIT, "mathlib_manifest_sha256": hashlib.sha256(pinned_manifest).hexdigest(),
        "dependency_pins": dependency_pins, "kernel_typechecking_disabled": False,
        "old_181_modules_rebuilt": False, "source_provider_constructed": False, "commands": commands,
    }
    for module in [*MODULES, "AxiomAudit"]:
        source = package / (module.replace(".", "/") + ".lean") if module != "AxiomAudit" else Path(__file__).with_name("AxiomAudit.lean")
        frozen = run / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(source.read_bytes())
        obj = objects / (module.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(lean), "-j1", "-M4096", "-Ddebug.skipKernelTC=false", "-o", str(obj), str(frozen.relative_to(run))]
        start = time.monotonic()
        try:
            result = subprocess.run(cmd, cwd=run, env=env, capture_output=True, timeout=180)
            code, stdout, stderr = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as exc:
            code, stdout, stderr = 124, exc.stdout or b"", exc.stderr or b""
        label = module.split(".")[-1]
        (args.evidence / (label + ".stdout")).write_bytes(stdout)
        (args.evidence / (label + ".stderr")).write_bytes(stderr)
        record = {"module": module, "command": cmd, "cwd": str(run), "source_sha256": digest(frozen),
                  "exit_code": code, "seconds": time.monotonic() - start,
                  "stdout_sha256": hashlib.sha256(stdout).hexdigest(), "stderr_sha256": hashlib.sha256(stderr).hexdigest()}
        commands.append(record)
        print(module, code, round(record["seconds"], 3), flush=True)
        stable = source.read_bytes() == frozen.read_bytes()
        forbidden = any(word in stdout + stderr for word in [b"sorryAx", b"Lean.ofReduceBool", b"Lean.trustCompiler"])
        record["source_stable"] = stable
        if code or not stable or forbidden:
            receipt["status"] = "FAILED_OR_RESOURCE"
            (args.evidence / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            return 1
        record["object_sha256"] = digest(obj)
    audit = json.loads((run / "AUDIT-OWNED.json").read_text())
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    (args.evidence / "axiom-inventory.json").write_text(json.dumps(audit, indent=2) + "\n")
    receipt.update(status="PASS_FRESH_KERNEL_CHECK", theorem_count=audit["theorem_declaration_count"],
                   owned_axioms=audit["owned_axioms"], nonstandard_axiom_rows=audit["nonstandard_axiom_rows"])
    (args.evidence / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
