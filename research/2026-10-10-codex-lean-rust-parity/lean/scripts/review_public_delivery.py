#!/usr/bin/env python3
"""Compare the newly published frozen release to the additive current union.

This is a source/context inventory, never a compilation or cache-admission
certificate. Object reuse still requires complete measured artifact bindings.
"""
from __future__ import annotations
import datetime
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
PUBLISHED = REPO / "research/2026-10-10-dot-connected-modular-lake-0855z"
UNPACKED = ROOT / ".build/published-modular-delivery-0855z"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contexts(graph):
    result = {}
    for module in graph["order"]:
        row = graph["modules"][module]
        assert all(dep not in graph["modules"] or dep in result for dep in row["imports"])
        value = {"module": module, "source": row["sha256"], "imports": [
            (dep, result.get(dep, {"external": dep})) for dep in row["imports"]]}
        result[module] = hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()
    return result


def main():
    original = json.loads((ROOT / "DEPENDENCY-GRAPH.json").read_bytes())
    published = json.loads((UNPACKED / "DEPENDENCY-GRAPH.json").read_bytes())
    current = original["targets"]["current/connected"]
    current_contexts = contexts(current)
    stores = {}
    for label, path in [("current", ROOT / "source-store"), ("published", PUBLISHED / "source-store")]:
        values = set()
        for source in path.glob("*.lean"):
            assert digest(source) == source.stem
            values.add(source.stem)
        stores[label] = values
    profiles = []
    externals = set()
    for label, graph in published["targets"].items():
        pins = contexts(graph)
        matches = [m for m in graph["order"] if current_contexts.get(m) == pins[m]]
        missing = [m for m in graph["order"] if current_contexts.get(m) != pins[m]]
        profiles.append({"profile": label,
            "required": graph.get("required_for_accepted_release", True),
            "selected_modules": len(graph["order"]),
            "exact_transitive_source_context_matches": len(matches),
            "different_or_absent_contexts": [{"module": m, "source_sha256": graph["modules"][m]["sha256"]} for m in missing],
            "new_compilation_status": "NOT_CHECKED_BY_THIS_INVENTORY"})
        externals.update(dep for row in graph["modules"].values() for dep in row["imports"]
                         if dep not in graph["modules"])
    canonical = published["targets"]["connected/20261009-canonical"]
    later = [{"module": m, "source_sha256": current["modules"][m]["sha256"]}
             for m in current["order"] if m not in canonical["modules"]]
    records = ["AGENTS.md", "START-HERE.md", "RESEARCH-STATUS.md", "docs/RESEARCH-COMPLETION-STANDARD.md",
        "research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md",
        "research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md",
        "handoffs/2026-10-09-goal-oriented-finish-lines/20261010T094500Z-CODEX-BUILD-HANDOFF.md",
        "research/2026-10-10-dot-connected-modular-lake-0855z/README.md",
        "research/2026-10-10-dot-g7-pending-codex-recovery-0952z/README.md",
        "research/2026-10-10-dot-g6-forest-exposure-handoff-0941z/README.md",
        "research/2026-10-10-dot-g7-qe-interface-review-0026z/README.md"]
    recent_hand_packets = sorted({str(p.relative_to(REPO)) for pattern in [
        "research/2026-10-10-dot-g3-*/README.md", "research/2026-10-10-dot-g4-*/README.md"]
        for p in REPO.glob(pattern)})
    records.extend(recent_hand_packets)
    pins = [{"path": p, "sha256": digest(REPO / p), "bytes": (REPO / p).stat().st_size} for p in records]
    review = {"schema": "PUBLIC_DELIVERY_SOURCE_CONTEXT_REVIEW_V1",
        "status": "PASS_STATIC_IDENTITIES_AND_CONTEXT_COMPARISON_ONLY",
        "current_graph_sha256": digest(ROOT / "DEPENDENCY-GRAPH.json"),
        "published_graph_sha256": digest(UNPACKED / "DEPENDENCY-GRAPH.json"),
        "unpack_result": json.loads((UNPACKED / "UNPACK-RESULT.json").read_bytes()),
        "source_versions": {"current": len(stores["current"]), "published": len(stores["published"]),
            "shared": len(stores["current"] & stores["published"]),
            "published_only": len(stores["published"] - stores["current"]),
            "current_only": len(stores["current"] - stores["published"])},
        "required_profiles": sum(p["required"] for p in profiles),
        "provisional_profiles": sum(not p["required"] for p in profiles),
        "profiles": profiles, "all_profile_external_import_roots": sorted(externals),
        "current_later_modules_outside_frozen_canonical": later,
        "leading_records": pins,
        "omission_disposition": [
            {"scope": "Frozen canonical and historical release", "disposition":
             "Publication hold superseded by exact public delivery. Preserve 78 isolated contexts and run the qualified 53 selector; provisional sources receive no inherited pass."},
            {"scope": "Later G2/G5-M3/G6-cell-TV/protected-bin checked packets", "disposition":
             "Kept as separately pinned current-union extensions. They were not inserted into the frozen 53 release by the publisher."},
            {"scope": "Three later G7 candidate chains", "disposition":
             "Now publicly delivered as failed/uncompiled recovery sources. Compile repaired isolated contexts with their own audits and separate code-generation smoke."},
            {"scope": "G6 full-forest exposure hand/source argument", "disposition":
             "Integrate scoped proof obligations separately; no Lean pass inherited from the handoff."},
            {"scope": "Later published G3/G4 source-specific handproof and counterexample packets",
             "public_records": recent_hand_packets, "disposition":
             "Tracked as scoped mathematical evidence with their original assumptions and open implications. Their publication adds no accepted Lean provider or automatic executable source/coverage gate."},
            {"scope": "G7 QE interface, master G3/G4/G6/G7 admission/coverage", "disposition":
             "Guidance or unresolved mathematical obligations, not missing accepted Lean providers. Retain original quantifiers and explicit gates."}],
        "reproduction_plan": {"workspace": str(UNPACKED),
            "entrypoint": "CONNECTED_LEAN_BIN=<pinned>/bin CONNECTED_MATHLIB=<pinned> <pinned>/bin/lake build connectedQualified",
            "policy": "Byte-identical public builder/wrapper; 53 required profiles. Exact-context cache reuse must be authenticated independently and reported as reuse, with every aggregate and audit newly invoked.",
            "running_1340_graph_overwritten": False, "historical_receipts_promoted": False,
            "fresh_execution_result": "PENDING_SOLE_COMPILER_SLOT"}}
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/public-delivery" / stamp
    evidence.mkdir(parents=True)
    data = json.dumps(review, indent=2) + "\n"
    (evidence / "REVIEW.json").write_text(data)
    (ROOT / "PUBLIC-DELIVERY-REVIEW.json").write_text(data)
    print(json.dumps({"status": review["status"], "source_versions": review["source_versions"],
                      "required_profiles": review["required_profiles"], "provisional_profiles": review["provisional_profiles"],
                      "evidence": str(evidence)}))


if __name__ == "__main__":
    main()
