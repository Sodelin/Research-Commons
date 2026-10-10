#!/usr/bin/env python3
"""Dated read-only history/accepted-union feasibility derivative; never launches Lean.
Original auditor SHA256: df4bea081fd59e2d46e20331c0027a66ad4398415fa2f22f87f1ef4b937350b9.
Only output names and proposed scratch location change; admission checks are identical.

Contributor: Codex / lean_integration_successor, 2026-10-10.
The explicitly supplied accepted contexts remain unchanged. This report
authenticates source and cache identities, not a new target, aggregate or
ownership audit. The module count is measured from their exact union.
"""
from __future__ import annotations

import argparse
import datetime
import re
import hashlib
import json
from pathlib import Path
import shutil

from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
NATIVE = "6f8ad181b1b3b832d74cf0f88255b519a3512252c343d3e0cde0c540cbfe7aac"
EXPECTED_MATHLIB = {
    "Mathlib.Data.FinEnum": "381c6f445637fdf6bc04a77f062ed2079d9856eeb260b30b609f3c098a3e430a",
    "Mathlib.Algebra.MvPolynomial.Polynomial": "43330a5e928a56af89b209101f98be347937384d2d435f875e2eaff698ccd650",
    "Mathlib.Algebra.MvPolynomial.Funext": "cb1821884a139917b692103a0b267115179cd4e7084da5487857ec49abb0cc7e",
    "Mathlib.Analysis.Convex.Caratheodory": "8e2ead25535366604c2caab3071e5549586f909fe70b885d1c75784e117720f2",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--context", nargs=2, action="append", required=True,
                        metavar=("WORKSPACE", "ACCEPTED_TARGET"))
    parser.add_argument("--label", required=True)
    args = parser.parse_args()
    assert re.fullmatch(r"[A-Za-z0-9_-]+", args.label)
    contexts = args.context
    assert len(contexts) == len(set(map(tuple, contexts)))
    entries, sources, roots, context_pins, caches = {}, {}, [], [], []
    conflicts = []
    original = set()
    for index, (relative, label) in enumerate(contexts):
        work = (ROOT / relative).resolve()
        path = work / "DEPENDENCY-GRAPH.json"
        selected = json.loads(path.read_bytes())["targets"][label]
        latest = work / ".build/LATEST-RUN.json"
        final = json.loads(latest.read_bytes())
        assert final["status"] == "PASS_ALL_REQUESTED_TARGETS", work
        assert label in final["targets_passed"] and final["graph_sha256"] == sha(path)
        assert final["kernel_checking"] and final["trust_level"] == 0
        assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
        if index == 0:
            original = set(selected["order"])
        roots.extend(selected["roots"])
        context_pins.append({"workspace": str(work), "target": label,
                             "graph_sha256": sha(path), "selected_modules": len(selected["order"]),
                             "completed_run_receipt_sha256": sha(latest), "actual_run": final["run"]})
        caches.append(work / ".build/cache")
        for module in selected["order"]:
            row = selected["modules"][module]
            source = work / "source-store" / (row["sha256"] + ".lean")
            assert sha(source) == row["sha256"]
            if module in entries:
                prior = entries[module]
                if (prior["sha256"], prior["imports"]) != (row["sha256"], row["imports"]):
                    conflicts.append({"module": module, "prior": prior, "candidate": row})
            else:
                entries[module], sources[module] = row, source
    assert not conflicts, conflicts
    roots = list(dict.fromkeys(roots))
    order, seen, active = [], set(), set()

    def visit(module):
        if module in seen:
            return
        assert module not in active
        active.add(module)
        for dependency in entries[module]["imports"]:
            if dependency in entries:
                visit(dependency)
        active.remove(module)
        seen.add(module)
        order.append(module)

    for module in roots:
        visit(module)
    assert set(order) == set(entries) and len(order) == len(entries)
    owned_mathlib = {m: row["sha256"] for m, row in entries.items() if m.startswith("Mathlib.")}
    assert owned_mathlib == EXPECTED_MATHLIB
    caches.append(ROOT / ".build/cache")
    eligible = {m: [] for m in order}
    for cache in dict.fromkeys(caches):
        assert cache.is_dir(), cache
        for folder in sorted(cache.iterdir()):
            receipt_path = folder / "receipt.json"
            if folder.name.startswith(".") or not receipt_path.is_file():
                continue
            rec = json.loads(receipt_path.read_bytes())
            module = rec["module"]
            if module not in entries or rec["source_sha256"] != entries[module]["sha256"]:
                continue
            assert rec["status"] == "PASS_FRESH_KERNEL_CHECK"
            assert rec["compiler_sha256"] == COMPILER and rec["mathlib_commit"] == MATHLIB
            assert rec["native_runtime_digest"] == NATIVE
            assert set(rec["direct_import_artifacts"]) == set(entries[module]["imports"])
            eligible[module].append((folder, rec))
    chosen, records = {}, []
    authenticated_bundles = {}

    def checked_bundle(path, expected):
        path = Path(path)
        if str(path) not in authenticated_bundles:
            authenticated_bundles[str(path)] = bundle(path)
        assert authenticated_bundles[str(path)] == expected, path

    for module in order:
        candidates = eligible[module]
        assert candidates, ("Missing completed exact cache", module)
        variants = {json.dumps(rec["object_artifacts"], sort_keys=True) for _, rec in candidates}
        assert len(variants) == 1, ("Different object bundles", module)
        matches = [(folder, rec) for folder, rec in candidates if all(
            dep not in entries or rec["direct_import_artifacts"][dep] == chosen[dep][1]["object_artifacts"]
            for dep in entries[module]["imports"])]
        assert matches, ("Owned direct import bundle mismatch", module)
        folder, rec = matches[0]
        key_data = {"module": module, "source": rec["source_sha256"], "compiler": COMPILER,
                    "mathlib": MATHLIB, "trust": 0, "kernel_check": True,
                    "imports": rec["direct_import_artifacts"], "native_runtime_digest": NATIVE,
                    "artifact_boundary": "olean-private-server-ilean-ir-native-v3"}
        if module == "ThetaCertificate5" and rec["source_sha256"] == "e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab":
            key_data["resource_exception"] = {"memory_mib": 6144, "seconds": 600}
        assert hashlib.sha256(json.dumps(key_data, sort_keys=True).encode()).hexdigest() == folder.name
        checked_bundle(rec["cached_object"], rec["object_artifacts"])
        checked_bundle(folder / "artifact.olean", rec["object_artifacts"])
        for imported in rec["direct_import_bindings"].values():
            checked_bundle(imported["path"], imported["artifacts"])
        files = [p for p in folder.rglob("*") if p.is_file()]
        records.append({"module": module, "source_sha256": rec["source_sha256"],
                        "source_path": str(sources[module]), "cache_key": folder.name,
                        "cache_entry": str(folder), "receipt_sha256": sha(folder / "receipt.json"),
                        "cached_object": rec["cached_object"], "object_artifacts": rec["object_artifacts"],
                        "entry_bytes": sum(p.stat().st_size for p in files),
                        "object_bytes": sum(p.stat().st_size for p in files if p.name != "receipt.json")})
        chosen[module] = (folder, rec)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = ROOT / "evidence/scheduler" / (args.label + "-feasibility-" + stamp)
    output.mkdir(parents=True)
    graph = {"targets": {"current/connected": {"roots": roots, "order": order,
             "modules": {m: entries[m] for m in order}, "required_for_accepted_release": False,
             "status": "UNCOMPILED_COHERENT_LATEST_MODULAR_CONTEXT"}},
             "scope": {"status": "Read-only integration feasibility; no target or aggregate acceptance",
                       "contexts": context_pins, "existing_contexts_unchanged": True}}
    save(output / "PROPOSED-DEPENDENCY-GRAPH.json", graph)
    save(output / "SELECTED-CACHE-IDENTITIES.json", records)
    source_bytes = sum(p.stat().st_size for p in set(sources.values()))
    cache_bytes = sum(row["entry_bytes"] for row in records)
    object_bytes = sum(row["object_bytes"] for row in records)
    report = {"status": "PASS_READONLY_EXACT_COHERENT_UNION_FEASIBILITY", "modules": len(order),
              "previous_union_modules": len(original), "added_modules": len(set(order) - original),
              "additions": {m: entries[m]["sha256"] for m in order if m not in original},
              "source_or_literal_import_conflicts": conflicts, "contexts": context_pins,
              "eligible_completed_receipt_copies": sum(map(len, eligible.values())),
              "selected_completed_cache_keys": len(chosen), "missing_cache_keys": [],
              "owned_import_bundle_mismatches": [], "object_bundle_variants": [],
              "authenticated_companion_bundle_paths": len(authenticated_bundles),
              "source_bytes": source_bytes, "selected_cache_tree_bytes": cache_bytes,
              "selected_object_bytes": object_bytes,
              "conservative_new_workspace_bytes": source_bytes + cache_bytes + object_bytes + 64 * 1024 * 1024,
              "recommended_scratch_location": "/dev/shm/rc-lean-" + args.label + "-NEW_TIMESTAMP",
              "available_bytes": {p: shutil.disk_usage(p).free for p in [str(ROOT), "/tmp", "/dev/shm"]},
              "compiler_sha256": COMPILER, "mathlib_commit": MATHLIB, "native_runtime_digest": NATIVE,
              "exact_owned_mathlib_source_pins": EXPECTED_MATHLIB,
              "proposed_target": "current/connected", "core_builder_sha256": sha(ROOT / "scripts/build_connected.py"),
              "aggregate_and_audit_caps": {"memory_mib": 6144, "seconds": 300},
              "compiler_launched": False, "large_workspace_materialized": False,
              "accepted_evidence_modified": False, "cache_receipt_bytes_rewritten": False,
              "new_target_or_baseline_accepted": False, "fixture_targets_included": any("Fixture" in m for m in set(order) - original),
              "required_next_check": "Fresh aggregate and complete owned audit after builder-authenticated cache admission",
              "proposed_graph_sha256": sha(output / "PROPOSED-DEPENDENCY-GRAPH.json"),
              "selected_cache_manifest_sha256": sha(output / "SELECTED-CACHE-IDENTITIES.json"),
              "auditor_sha256": sha(Path(__file__)), "evidence": str(output.relative_to(ROOT))}
    shutil.copyfile(Path(__file__), output / "AUDITOR.py")
    save(output / "RECEIPT.json", report)
    save(ROOT / "HISTORY-CONTEXT-COVERAGE-AUDIT-FEASIBILITY-20261010T204126.032060Z.json", report)
    print(json.dumps({k: report[k] for k in ["status", "modules", "added_modules", "selected_completed_cache_keys",
                                         "source_bytes", "selected_cache_tree_bytes", "conservative_new_workspace_bytes", "evidence"]}))


if __name__ == "__main__":
    main()
