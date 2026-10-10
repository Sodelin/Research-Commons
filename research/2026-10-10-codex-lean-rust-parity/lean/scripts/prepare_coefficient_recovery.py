#!/usr/bin/env python3
"""Stage a separately pinned repair of the delivered coefficient context.

Historical sources, graphs and attempts are read only. The official FinEnum
namespace overlay is preserved; only its builder identity pin is updated to
the current hardened serial runner. The mathematical change is the explicit
proof derivative owned and documented by the reuse worker.
"""
from __future__ import annotations
import datetime
import hashlib
import json
from pathlib import Path
import shutil
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
ORIGINAL = REPO / "research/2026-10-10-dot-g7-pending-codex-recovery-0952z/latest/coefficients"
SOURCE = ROOT.parent / "reuse/sources/G7EffectiveFullEpochCoefficients.lean"


def main():
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/recovery/coefficients" / stamp
    evidence = ROOT / "evidence/recovery/coefficients" / stamp
    work.mkdir(parents=True)
    graph_bytes = (ORIGINAL / "DEPENDENCY-GRAPH.json").read_bytes()
    graph = json.loads(graph_bytes)
    provenance_path = ROOT.parent / "reuse/G7-FULL-EPOCH-REPAIR.json"
    provenance = json.loads(provenance_path.read_bytes())
    assert sha(SOURCE) == provenance["derivative_sha256"]
    for label, target in graph["targets"].items():
        row = target["modules"]["G7EffectiveFullEpochCoefficients"]
        assert row["sha256"] == provenance["original_sha256"]
        row["sha256"] = sha(SOURCE)
        target["status"] = "UNCOMPILED_SEPARATELY_PINNED_PROOF_REPAIR"
    graph["scope"]["status"] = "Separately pinned proof repair; historical source and failed attempts preserved."
    graph["scope"]["source_manifest"] = "PREPARATION.json"
    graph["scope"].pop("source_manifest_sha256", None)
    graph["scope"]["original_recovery_graph_sha256"] = hashlib.sha256(graph_bytes).hexdigest()
    graph["scope"]["repair_provenance_sha256"] = sha(provenance_path)
    save(work / "DEPENDENCY-GRAPH.json", graph)
    (work / "ORIGINAL-DEPENDENCY-GRAPH.json").write_bytes(graph_bytes)
    store = work / "source-store"
    store.mkdir()
    sources = []
    for source in sorted((ORIGINAL / "source-store").glob("*.lean")):
        assert sha(source) == source.stem
        shutil.copy2(source, store / source.name)
        sources.append({"sha256": source.stem, "bytes": source.stat().st_size})
    shutil.copy2(SOURCE, store / (sha(SOURCE) + ".lean"))
    scripts = work / "scripts"
    scripts.mkdir()
    for name in ["build_connected.py", "AuditTemplate.lean"]:
        shutil.copy2(ROOT / "scripts" / name, scripts / name)
    wrapper_original = (ORIGINAL / "scripts/build_with_mathlib_overlay.py").read_bytes()
    old = b"CORE_SHA = 'f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be'"
    assert wrapper_original.count(old) == 1
    new = ("CORE_SHA = '" + sha(scripts / "build_connected.py") + "'").encode()
    wrapper = wrapper_original.replace(old, new)
    (scripts / "build_with_mathlib_overlay.py").write_bytes(wrapper)
    for source in (ORIGINAL / "third-party").rglob("*"):
        if source.is_file():
            target = work / source.relative_to(ORIGINAL)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
    receipt = {"status": "PREPARED_UNCOMPILED_ISOLATED_COEFFICIENT_REPAIR",
        "workspace": str(work), "evidence": str(evidence),
        "original_graph_sha256": hashlib.sha256(graph_bytes).hexdigest(),
        "repaired_graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"),
        "preserved_original_source_versions": sources,
        "proof_repair": provenance, "derivative_source_sha256": sha(SOURCE),
        "builder_sha256": sha(scripts / "build_connected.py"),
        "audit_template_sha256": sha(scripts / "AuditTemplate.lean"),
        "original_overlay_wrapper_sha256": hashlib.sha256(wrapper_original).hexdigest(),
        "overlay_wrapper_sha256": sha(scripts / "build_with_mathlib_overlay.py"),
        "overlay_change": "Only the core builder hash pin; full Mathlib namespace overlay, original official FinEnum source, and first-namespace resolution checks retained.",
        "runner_changes": "Require full audit invocation PASS status, final compiler identity and existing bounded serial resource checks. No theorem or executable definition weakened.",
        "historical_receipts_reused_as_new_pass": False,
        "kernel_target": "candidate/g7-coefficients",
        "separate_explicit_audit_target": "evidence/g7-coefficients-explicit-audit",
        "separate_execution_target": "evidence/g7-coefficient-codegen-smoke"}
    save(work / "PREPARATION.json", receipt)
    save(evidence / "PREPARATION.json", receipt)
    save(ROOT / "COEFFICIENT-RECOVERY-PREPARATION.json", receipt)
    frozen = evidence / "derivative/G7EffectiveFullEpochCoefficients.lean"
    frozen.parent.mkdir(parents=True)
    frozen.write_bytes(SOURCE.read_bytes())
    (evidence / "ORIGINAL-DEPENDENCY-GRAPH.json").write_bytes(graph_bytes)
    (evidence / "DEPENDENCY-GRAPH.json").write_bytes((work / "DEPENDENCY-GRAPH.json").read_bytes())
    print(json.dumps({"status": receipt["status"], "workspace": str(work),
                      "derivative_source_sha256": sha(SOURCE)}))


if __name__ == "__main__":
    main()
