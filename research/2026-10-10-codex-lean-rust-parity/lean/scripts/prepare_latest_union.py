#!/usr/bin/env python3
"""Freeze a coherent latest union without changing either original graph.

The published canonical 1411 environment and later checked current 1340
environment have compatible module/source/import identities. Their composition
requires its own kernel checks and complete audit. Historical profiles remain
in the byte-identical public release, never concatenated by logical name.
"""
from __future__ import annotations
import datetime
import json
from pathlib import Path
import shutil
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]
PUBLIC = ROOT / ".build/published-modular-delivery-0855z"
TARGET = "current/latest-public-union"


def main():
    old_path = ROOT / "DEPENDENCY-GRAPH.json"
    public_path = PUBLIC / "DEPENDENCY-GRAPH.json"
    old = json.loads(old_path.read_bytes())["targets"]["current/connected"]
    canonical = json.loads(public_path.read_bytes())["targets"]["connected/20261009-canonical"]
    entries = {}
    sources = {}
    origins = {}
    for label, target, store in [("current-1340", old, ROOT / "source-store"),
                                 ("published-canonical-1411", canonical, PUBLIC / "source-store")]:
        for m in target["order"]:
            row = target["modules"][m]
            identity = {"module": m, "sha256": row["sha256"], "imports": row["imports"]}
            if m in entries:
                assert entries[m] == identity, ("Conflicting module/source/import identity", m)
            else:
                entries[m] = identity
                source = store / (row["sha256"] + ".lean")
                assert sha(source) == row["sha256"]
                sources[m] = source
            origins.setdefault(m, []).append({"context": label, "original_record": row})
    order = []
    seen = set()
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for dependency in entries[m]["imports"]:
            if dependency in entries:
                visit(dependency)
        order.append(m)
    for m in entries:
        visit(m)
    assert len(order) == 1433
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    work = ROOT / ".build/latest-public-union" / stamp
    evidence = ROOT / "evidence/latest-public-union" / stamp
    store = work / "source-store"
    store.mkdir(parents=True)
    for m in order:
        shutil.copy2(sources[m], store / (entries[m]["sha256"] + ".lean"))
    graph = {"targets": {TARGET: {"roots": order, "order": order,
             "modules": {m: entries[m] for m in order}, "required_for_accepted_release": True,
             "status": "PREPARED_NEW_COMPOSITION_UNCOMPILED"}},
             "scope": {"status": "New coherent public composition with independent acceptance pending.",
                       "original_current_graph_sha256": sha(old_path),
                       "original_published_graph_sha256": sha(public_path),
                       "historical_profiles_remain_isolated": True,
                       "frozen_53_profile_reproduction_is_separate": True}}
    save(work / "DEPENDENCY-GRAPH.json", graph)
    scripts = work / "scripts"
    scripts.mkdir()
    original_builder = (ROOT / "scripts/build_connected.py").read_bytes()
    old_policy = b"combined=label in ['current/connected','historical/connected/compatible']"
    assert original_builder.count(old_policy) == 1
    new_policy = b"combined=label in ['current/connected','historical/connected/compatible','current/latest-public-union']"
    (scripts / "build_connected.py").write_bytes(original_builder.replace(old_policy, new_policy))
    shutil.copy2(ROOT / "scripts/AuditTemplate.lean", scripts / "AuditTemplate.lean")
    receipt = {"status": "PREPARED_UNCOMPILED_COHERENT_LATEST_PUBLIC_UNION",
        "workspace": str(work), "evidence": str(evidence), "target": TARGET,
        "closure_modules": len(order), "current_modules": len(old["modules"]),
        "published_canonical_modules": len(canonical["modules"]),
        "additional_published_modules": len(set(canonical["modules"]) - set(old["modules"])),
        "later_current_modules_outside_frozen_canonical": len(set(old["modules"]) - set(canonical["modules"])),
        "sources_or_imports_changed": False, "graph_sha256": sha(work / "DEPENDENCY-GRAPH.json"),
        "original_current_graph_sha256": sha(old_path), "original_published_graph_sha256": sha(public_path),
        "original_builder_sha256": sha(ROOT / "scripts/build_connected.py"),
        "builder_sha256": sha(scripts / "build_connected.py"),
        "builder_change": "Only the exact new aggregate/audit target is admitted to the existing bounded 6144 MiB / 300-second combined policy. Components retain unchanged ordinary caps and exact-source Theta exception.",
        "historical_sources_graphs_or_receipts_overwritten": False,
        "frozen_release_pass_inherited": False,
        "source_context_inventory": [{"module": m, "sha256": entries[m]["sha256"],
            "imports": entries[m]["imports"], "origins": origins[m]} for m in order]}
    save(work / "PREPARATION.json", receipt)
    save(evidence / "PREPARATION.json", receipt)
    save(evidence / "DEPENDENCY-GRAPH.json", graph)
    save(ROOT / "LATEST-UNION-PREPARATION.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "workspace", "closure_modules", "additional_published_modules"]}))


if __name__ == "__main__":
    main()
