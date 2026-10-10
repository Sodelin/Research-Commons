#!/usr/bin/env python3
"""Freeze missing pinned Mathlib sources without modifying its installation.

Contributor: Codex / lean_integration_successor, 2026-10-10. This creates a
source-only input context for prepare_proof_extension.py. It compiles nothing,
copies no component pass and does not install global Mathlib artifacts.
"""
from __future__ import annotations
import argparse
import datetime
import json
from pathlib import Path
import re
import shutil
import subprocess
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = Path("/workspace/dependencies/mathlib4")
LEAN = Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")
COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", action="append", required=True)
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"[A-Za-z0-9_-]+", args.label)
    assert len(args.module) == len(set(args.module))
    assert all(re.fullmatch(r"Mathlib\.[A-Za-z_][A-Za-z0-9_.]*", m) for m in args.module)
    assert sha(LEAN) == COMPILER
    assert subprocess.check_output(["git", "-C", str(MATHLIB), "rev-parse", "HEAD"], text=True).strip() == COMMIT
    external = sorted((MATHLIB / ".lake/packages").glob("*/.lake/build/lib/lean"))
    external += [MATHLIB / ".lake/build/lib/lean", LEAN.parent.parent / "lib/lean"]
    rows, source_paths, order, active = {}, {}, [], set()
    available = {}

    def visit(module):
        relative = module.replace(".", "/")
        present = next((p / (relative + ".olean") for p in external
                        if (p / (relative + ".olean")).is_file()), None)
        if present is not None:
            available[module] = {"path": str(present), "sha256": sha(present)}
            return
        if module in rows:
            assert module not in active, ("Import cycle", module)
            return
        assert module.startswith("Mathlib."), ("Missing non-Mathlib prerequisite", module)
        source = MATHLIB / (relative + ".lean")
        body = source.read_bytes()
        imports = [m.decode() for m in re.findall(
            rb"^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)", body, re.M)]
        rows[module] = {"module": module, "sha256": sha(source), "imports": imports}
        source_paths[module] = source
        active.add(module)
        for dependency in imports:
            visit(dependency)
        active.remove(module)
        order.append(module)

    for module in args.module:
        visit(module)
    assert all(module in rows for module in args.module), "Requested root already has a global object; do not duplicate its compilation."
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/read-only-prerequisites" / args.label / stamp
    evidence = ROOT / "evidence/read-only-prerequisites" / args.label / stamp
    (work / "source-store").mkdir(parents=True)
    for module in order:
        source = source_paths[module]
        shutil.copyfile(source, work / "source-store" / (rows[module]["sha256"] + ".lean"))
        frozen = evidence / "sources" / (module.replace(".", "/") + ".lean")
        frozen.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, frozen)
        assert sha(source) == sha(frozen) == rows[module]["sha256"]
    target = "prerequisite/" + args.label
    graph = {"targets": {target: {"roots": args.module, "order": order, "modules": rows,
        "required_for_accepted_release": False, "status": "UNCOMPILED_READ_ONLY_MATHLIB_SOURCE_CONTEXT"}},
        "scope": {"contributor": "Codex / lean_integration_successor", "mathlib_commit": COMMIT,
        "original_mathlib_files_and_global_artifacts_modified": False,
        "compiled_pass_or_component_cache_copied": False}}
    for destination in [work, evidence]:
        save(destination / "DEPENDENCY-GRAPH.json", graph)
        (destination / "third-party/mathlib").mkdir(parents=True)
        shutil.copyfile(MATHLIB / "LICENSE", destination / "third-party/mathlib/LICENSE")
    shutil.copyfile(Path(__file__), evidence / "PREPARER.py")
    preparation = {"status": "UNCOMPILED_READ_ONLY_MATHLIB_SOURCE_CONTEXT", "workspace": str(work),
        "evidence": str(evidence), "target": target, "closure_modules": len(order),
        "source_pins": {m: rows[m]["sha256"] for m in order},
        "graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"), "mathlib_commit": COMMIT,
        "compiler_sha256": COMPILER, "available_external_import_objects_at_preparation": available,
        "preparer_sha256": sha(Path(__file__)), "original_installation_modified": False,
        "next_action": "Compose this source-only context with the exact proof root; then run the frozen bounded compiler and complete owned audit."}
    save(work / "SOURCE-CONTEXT-PREPARATION.json", preparation)
    save(evidence / "SOURCE-CONTEXT-PREPARATION.json", preparation)
    save(ROOT / (args.label.upper() + "-READONLY-SOURCE-PREPARATION.json"), preparation)
    print(json.dumps({k: preparation[k] for k in ["status", "workspace", "target", "closure_modules"]}))


if __name__ == "__main__":
    main()
