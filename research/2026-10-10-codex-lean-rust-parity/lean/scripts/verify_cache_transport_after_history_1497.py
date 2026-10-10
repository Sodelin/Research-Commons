#!/usr/bin/env python3
"""Rehash preserved originals, staged cache inputs and actual installed bundles.

Contributor: Codex / lean_integration_successor, 2026-10-10.
Read-only verification of the separately frozen storage transport after the
unchanged strict builder completes. This does not copy a target or audit pass.
"""
from __future__ import annotations
# Dated history1497 metadata-output derivative; original SHA256 6e90ae6c50c66b74b74f69fc6afabc7dad872a1a889c330af231c47e1e06696e.
# Transport/admission/rehash code is unchanged; accepted generic output is preserved.

import argparse
import datetime
import json
from pathlib import Path
import re
import shutil

from check_core import bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    work = args.workspace.resolve(strict=True)
    prep = json.loads((work / "PREPARATION.json").read_bytes())
    final = json.loads((work / ".build/LATEST-RUN.json").read_bytes())
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
    assert final["kernel_checking"] and final["trust_level"] == 0
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    run = Path(final["run"])
    assert run.is_relative_to(work)
    graph_path = work / "DEPENDENCY-GRAPH.json"
    assert sha(graph_path) == prep["graph_sha256"] == final["graph_sha256"]
    graph = json.loads(graph_path.read_bytes())
    seed = json.loads((work / "CACHE-SEED-RECEIPT.json").read_bytes())
    plan_path = work / "CACHE-TRANSPORT-PRE-USE-PLAN.json"
    plan = json.loads(plan_path.read_bytes())
    assert sha(plan_path) == seed["pre_use_plan_sha256"]
    aliases_path = work / "CACHE-INSTALL-ALIASES.json"
    aliases = json.loads(aliases_path.read_bytes())
    derivation = json.loads((work / "CACHE-INSTALL-TRANSPORT-DERIVATION.json").read_bytes())
    assert sha(aliases_path) == derivation["alias_manifest_sha256"]
    assert aliases["graph_sha256"] == final["graph_sha256"]
    assert sha(work / "scripts/build_connected.py") == derivation["core_builder_sha256"]
    assert sha(work / "scripts/AuditTemplate.lean") == derivation["audit_template_sha256"]
    assert sha(work / "scripts/build_with_mathlib_overlay.py") == derivation["derived_namespace_wrapper_sha256"]
    assert sha(work / "scripts/build_with_authenticated_overlay.py") == derivation["derived_authenticated_wrapper_sha256"]
    imports = {}

    def checked_bundle(path, expected):
        path = Path(path)
        if str(path) not in imports:
            imports[str(path)] = bundle(path)
        assert imports[str(path)] == expected, path

    files = 0
    logical_bytes = 0
    for entry in plan["entries"]:
        for row in entry["files"]:
            source, staged = Path(row["source"]), Path(row["destination"])
            assert sha(source) == sha(staged) == row["sha256"], ("Original/staged file changed", row)
            assert source.stat().st_size == staged.stat().st_size == row["bytes"]
            files += 1
            logical_bytes += row["bytes"]
    installs = [json.loads(line) for line in (run / "CACHE-INSTALL-TRANSPORT-CHECKS.jsonl").read_text().splitlines()]
    installed = {row["destination"]: row for row in installs}
    assert len(installed) == len(installs)
    records = []
    installed_files = hardlinks = copies = 0
    for target in final["targets_passed"]:
        g = graph["targets"][target]
        context = run / "targets" / re.sub("[^A-Za-z0-9_-]", "_", target) / "objects"
        assert set(g["order"]) == {row["module"] for row in aliases["entries"]}
        chosen = {row["module"]: row for row in aliases["entries"]}
        for module in g["order"]:
            row = chosen[module]
            original_receipt, staged_receipt = Path(row["original_receipt"]), Path(row["staged_receipt"])
            assert sha(original_receipt) == sha(staged_receipt) == row["receipt_sha256"]
            rec = json.loads(original_receipt.read_bytes())
            assert rec["cached_object"] == row["original_cached_object"] and rec["module"] == module
            assert rec["source_sha256"] == g["modules"][module]["sha256"] == row["source_sha256"]
            assert sha(work / "source-store" / (row["source_sha256"] + ".lean")) == row["source_sha256"]
            expected = row["object_artifacts"]
            out = context / (module.replace(".", "/") + ".olean")
            checked_bundle(row["original_cached_object"], expected)
            checked_bundle(row["staged_cached_object"], expected)
            checked_bundle(out, expected)
            install = installed[str(out)]
            assert install["original_object"] == row["original_cached_object"]
            assert install["install_source"] == row["staged_cached_object"]
            assert install["cache_key"] == row["cache_key"] and install["object_artifacts"] == expected
            for imported, binding in rec["direct_import_bindings"].items():
                checked_bundle(binding["path"], binding["artifacts"])
                if imported in chosen:
                    assert binding["artifacts"] == chosen[imported]["object_artifacts"]
            for f in install["files"]:
                source, destination = Path(f["source"]), Path(f["destination"])
                assert sha(source) == sha(destination) == f["sha256"]
                assert source.stat().st_size == destination.stat().st_size == f["bytes"]
                if f["transport"] == "SAME_FILESYSTEM_HARD_LINK":
                    assert (source.stat().st_dev, source.stat().st_ino) == (destination.stat().st_dev, destination.stat().st_ino)
                    hardlinks += 1
                elif f["transport"] == "EXDEV_HASH_CHECKED_COPY2":
                    copies += 1
                else:
                    assert f["transport"] == "VERIFIED_EXISTING_DESTINATION"
                installed_files += 1
            records.append({"module": module, "target": target, "cache_key": row["cache_key"],
                "original_receipt_sha256": row["receipt_sha256"], "original_cached_object": row["original_cached_object"],
                "staged_cached_object": row["staged_cached_object"], "installed_object": str(out),
                "object_artifacts": expected, "all_original_staged_installed_rehashes_pass": True})
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/cache-transport-post-run" / stamp
    evidence.mkdir(parents=True)
    shutil.copyfile(Path(__file__), evidence / "VERIFIER.py")
    receipt = {"status": "PASS_POST_BUILDER_ORIGINAL_STAGED_INSTALLED_CACHE_REHASH",
        "workspace": str(work), "run": str(run), "graph_sha256": final["graph_sha256"],
        "final_run_receipt_sha256": sha(work / ".build/LATEST-RUN.json"),
        "seed_receipt_sha256": sha(work / "CACHE-SEED-RECEIPT.json"),
        "pre_use_transport_plan_sha256": sha(plan_path), "install_alias_manifest_sha256": sha(aliases_path),
        "install_derivation_sha256": sha(work / "CACHE-INSTALL-TRANSPORT-DERIVATION.json"),
        "verifier_sha256": sha(Path(__file__)), "source_and_staged_cache_files_rehashed": files,
        "selected_cache_logical_bytes": logical_bytes, "selected_modules_verified": len(records),
        "installed_cache_companion_files_rehashed": installed_files, "installed_same_filesystem_hard_links": hardlinks,
        "installed_exdev_copies": copies, "original_import_companion_bundle_paths_verified": len(imports),
        "records": records, "accepted_inputs_modified": False, "compiler_or_evaluator_invoked": False,
        "evidence": str(evidence.relative_to(ROOT))}
    save(evidence / "RECEIPT.json", receipt)
    save(work / "CACHE-TRANSPORT-POST-RUN-REHASH.json", receipt)
    save(ROOT / "CACHE-TRANSPORT-HISTORY-1497-POST-RUN-REHASH.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "selected_modules_verified", "source_and_staged_cache_files_rehashed",
                                           "installed_same_filesystem_hard_links", "installed_exdev_copies", "evidence"]}))


if __name__ == "__main__":
    main()
