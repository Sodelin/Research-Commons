#!/usr/bin/env python3
"""Replay the accepted latest public union from its portable exact sources.

This creates an isolated workspace and invokes the accepted, frozen builder.
Existing exact component caches are authenticated individually if available;
otherwise components compile from source. Each new run records its actual
freshness and preserves its own results without changing accepted snapshots.
"""
from __future__ import annotations
import argparse
import datetime
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
TARGET = "current/latest-public-union"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    certificate_path = ROOT / "LATEST-PUBLIC-UNION-CERTIFICATE.json"
    certificate = json.loads(certificate_path.read_bytes())
    assert certificate["status"] == "PASS_1433_AUTHENTICATED_COMPONENTS_AND_FRESH_COMPLETE_OWNED_AUDIT"
    assert certificate["compiler_sha256"] == COMPILER
    source_evidence = ROOT / certificate["source_evidence"]
    run_evidence = ROOT / certificate["evidence"]
    closure_path = source_evidence / "SOURCE-IMPORT-CLOSURE.json"
    assert sha(closure_path) == certificate["source_import_closure_sha256"]
    closure = json.loads(closure_path.read_bytes())
    graph_path = source_evidence / "DEPENDENCY-GRAPH.json"
    assert sha(graph_path) == certificate["graph_sha256"] == closure["graph_sha256"]
    graph = json.loads(graph_path.read_bytes())
    selected = graph["targets"][TARGET]
    assert len(selected["order"]) == len(closure["modules"]) == 1433
    sources = {row["module"]: row for row in closure["modules"]}
    assert set(sources) == set(selected["order"])
    original_preparation = json.loads((source_evidence / "PREPARATION.json").read_bytes())
    builder = run_evidence / "BUILDER.py"
    audit_template = run_evidence / "AuditTemplate.lean"
    assert sha(builder) == original_preparation["builder_sha256"]
    assert sha(audit_template) == "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/latest-public-replay" / stamp
    evidence = ROOT / "evidence/latest-public-replay" / stamp
    (work / "source-store").mkdir(parents=True)
    (work / "scripts").mkdir()
    shutil.copyfile(graph_path, work / "DEPENDENCY-GRAPH.json")
    shutil.copyfile(builder, work / "scripts/build_connected.py")
    shutil.copyfile(audit_template, work / "scripts/AuditTemplate.lean")
    for module in selected["order"]:
        row = sources[module]
        expected = selected["modules"][module]
        assert row["source_sha256"] == expected["sha256"] and row["imports"] == expected["imports"]
        source = source_evidence / row["evidence_path"]
        assert source.is_relative_to(source_evidence) and sha(source) == expected["sha256"]
        destination = work / "source-store" / (expected["sha256"] + ".lean")
        if not destination.exists():
            shutil.copyfile(source, destination)
    # Explicit source context preparation, rather than previous status transfer.
    preparation = {"status": "PREPARED_PORTABLE_EXACT_LATEST_PUBLIC_REPLAY",
        "workspace": str(work), "evidence": str(evidence), "targets": {TARGET: 1433},
        "graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"), "builder_sha256": sha(builder),
        "audit_template_sha256": sha(audit_template), "portable_certificate_sha256": sha(certificate_path),
        "portable_source_import_closure_sha256": sha(closure_path),
        "original_preparation_sha256": sha(source_evidence / "PREPARATION.json"),
        "source_pins": {m: sources[m]["source_sha256"] for m in selected["order"]},
        "launcher_sha256": sha(Path(__file__)), "historical_target_passes_inherited": False,
        "historical_contexts_or_receipts_overwritten": False,
        "scope": "An isolated replay of the accepted compatible1433 public source composition, with original theorem assumptions and unchanged frozen resource policies."}
    save(work / "PREPARATION.json", preparation)
    save(evidence / "PREPARATION.json", preparation)
    shutil.copyfile(Path(__file__), evidence / "LAUNCHER.py")
    save(ROOT / "LATEST-PUBLIC-REPLAY-PREPARATION.json", preparation)
    print(json.dumps({k: preparation[k] for k in ["status", "workspace", "targets"]}), flush=True)
    if args.prepare_only:
        return 0
    assert os.environ.get("CONNECTED_LEAN_BIN") and os.environ.get("CONNECTED_MATHLIB"), (
        "Set CONNECTED_LEAN_BIN and CONNECTED_MATHLIB to the pinned compiler and Mathlib checkout")
    caches = [ROOT / ".build/cache", ROOT / ".build/published-modular-delivery-0855z/.build/cache",
              Path(certificate["workspace"]) / ".build/cache"]
    existing = list(dict.fromkeys(str(p) for p in caches if p.is_dir()))
    if existing:
        command = [sys.executable, str(ROOT / "scripts/seed_exact_cache.py"), str(work)]
        for cache in existing:
            command += ["--source-cache", cache]
        subprocess.run(command, check=True)
    command = [sys.executable, str(work / "scripts/build_connected.py"), TARGET]
    code = subprocess.run(command, cwd=work).returncode
    subprocess.run([sys.executable, str(ROOT / "scripts/preserve_recovery_result.py"), str(work),
        "--result-file", "LATEST-PUBLIC-REPLAY-RESULT.json"], check=True)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
