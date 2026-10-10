#!/usr/bin/env python3
"""Stage explicitly selected verified cache entries without duplicating bytes.

Contributor: Codex / lean_integration_successor, 2026-10-10.
The original cache admission checks remain intact. Only storage transport uses
hard links on the same filesystem, with hash-checked copy2 after EXDEV. Existing
receipts, cached_object paths and keys remain byte-identical. No compiler runs.
"""
from __future__ import annotations

import argparse
import datetime
import errno
import hashlib
import json
import os
from pathlib import Path
import shutil

from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL_SEEDER_SHA = "e3ed1782e89359ec321625774552bfdf1226db2a0736df7c6cc13250b67a53ae"
CORE_SHA = "13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc"
AUDIT_SHA = "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
NATIVE = "6f8ad181b1b3b832d74cf0f88255b519a3512252c343d3e0cde0c540cbfe7aac"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--selection-manifest", type=Path, required=True)
    args = parser.parse_args()
    destination = args.destination.resolve(strict=True)
    selected_path = args.selection_manifest.resolve(strict=True)
    assert sha(ROOT / "scripts/seed_exact_cache.py") == ORIGINAL_SEEDER_SHA
    assert sha(destination / "scripts/build_connected.py") == CORE_SHA
    assert sha(destination / "scripts/AuditTemplate.lean") == AUDIT_SHA
    graph = json.loads((destination / "DEPENDENCY-GRAPH.json").read_bytes())
    selected = {m: row for target in graph["targets"].values()
                for m, row in target["modules"].items()}
    identities = json.loads(selected_path.read_bytes())
    assert len(identities) == len(selected)
    assert {row["module"] for row in identities} == set(selected)
    cache = destination / ".build/cache"
    assert not cache.exists() or not any(cache.iterdir()), "Only a new empty candidate cache is allowed"
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/cache-transport" / stamp
    evidence.mkdir(parents=True)
    plan = []
    validated = []
    for selected_row in identities:
        entry = Path(selected_row["cache_entry"]).resolve(strict=True)
        receipt = entry / "receipt.json"
        assert sha(receipt) == selected_row["receipt_sha256"]
        rec = json.loads(receipt.read_bytes())
        module = rec["module"]
        row = selected[module]
        assert (module, rec["source_sha256"]) == (selected_row["module"], row["sha256"])
        assert rec["status"] == "PASS_FRESH_KERNEL_CHECK"
        assert rec["compiler_sha256"] == COMPILER and rec["mathlib_commit"] == MATHLIB
        assert rec["native_runtime_digest"] == NATIVE
        assert rec["source_and_imports_stable"] and rec["native_initialized_libraries_bound"]
        assert rec["exit_code"] == 0 and all(flag in rec["command"] for flag in
            ["-j1", "-t0", "-Ddebug.skipKernelTC=false"])
        source = destination / "source-store" / (rec["source_sha256"] + ".lean")
        assert sha(source) == rec["source_sha256"]
        assert set(rec["direct_import_bindings"]) == set(row["imports"])
        for imported, expected in rec["direct_import_bindings"].items():
            assert bundle(Path(expected["path"])) == expected["artifacts"], (module, imported)
        assert bundle(Path(rec["cached_object"])) == rec["object_artifacts"]
        assert bundle(entry / "artifact.olean") == rec["object_artifacts"]
        assert rec["object_artifacts"] == selected_row["object_artifacts"]
        key_data = {"module": module, "source": rec["source_sha256"], "compiler": COMPILER,
            "mathlib": rec["mathlib_commit"], "trust": 0, "kernel_check": True,
            "imports": rec["direct_import_artifacts"], "native_runtime_digest": rec["native_runtime_digest"],
            "artifact_boundary": "olean-private-server-ilean-ir-native-v3"}
        if module == "ThetaCertificate5" and rec["source_sha256"] == "e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab":
            key_data["resource_exception"] = {"memory_mib": 6144, "seconds": 600}
        assert hashlib.sha256(json.dumps(key_data, sort_keys=True).encode()).hexdigest() == entry.name
        assert entry.name == selected_row["cache_key"]
        target = cache / entry.name
        files = []
        for path in sorted(entry.rglob("*")):
            assert not path.is_symlink(), ("Completed cache entry contains symlink", path)
            if path.is_file():
                relative = path.relative_to(entry)
                stat = path.stat()
                files.append({"relative": str(relative), "source": str(path), "destination": str(target / relative),
                              "sha256": sha(path), "bytes": stat.st_size,
                              "source_device": stat.st_dev, "source_inode": stat.st_ino})
        assert any(row["relative"] == "receipt.json" for row in files)
        plan.append({"module": module, "key": entry.name, "source_entry": str(entry),
                     "destination_entry": str(target), "source_sha256": rec["source_sha256"],
                     "original_receipt_sha256": sha(receipt), "original_cached_object_path": rec["cached_object"],
                     "object_artifacts": rec["object_artifacts"], "files": files})
        validated.append(rec)
    assert len({row["key"] for row in plan}) == len(plan)
    derivation = {"status": "PRE_USE_FROZEN_VERIFIED_CACHE_TRANSPORT_PLAN",
        "destination": str(destination), "destination_graph_sha256": sha(destination / "DEPENDENCY-GRAPH.json"),
        "selection_manifest": str(selected_path), "selection_manifest_sha256": sha(selected_path),
        "original_seeder_sha256": ORIGINAL_SEEDER_SHA, "transport_seeder_sha256": sha(Path(__file__)),
        "unchanged_core_builder_sha256": CORE_SHA, "unchanged_audit_template_sha256": AUDIT_SHA,
        "policy": "Same-filesystem immutable input file hard links; only EXDEV permits fully hash-checked copy2. No shared chmod, overwrite or deletion.",
        "read_only_builder_review": "Completed-key component branch reads receipt and source bundles then installs into fresh run context. install verifies existing destination bytes or creates a new link/copy. cache_result refuses an existing completed key and writes only a new staging directory. Compiler outputs are new attempt paths. The cache input companions and receipts are not written.",
        "compiler_cache_admission_kernel_and_resource_policy_changed": False,
        "original_paths_keys_or_receipt_bytes_changed": False, "compiler_launched": False,
        "entries": plan}
    save(evidence / "PRE-USE-TRANSPORT-PLAN.json", derivation)
    save(destination / "CACHE-TRANSPORT-PRE-USE-PLAN.json", derivation)
    shutil.copyfile(Path(__file__), evidence / "TRANSPORT-SEEDER.py")
    shutil.copyfile(ROOT / "scripts/seed_exact_cache.py", evidence / "ORIGINAL-SEEDER.py")
    records = []
    linked_files = copied_files = linked_bytes = copied_bytes = 0
    for entry, rec in zip(plan, validated):
        target = Path(entry["destination_entry"])
        assert not target.exists()
        target.mkdir(parents=True)
        transports = []
        for row in entry["files"]:
            source, out = Path(row["source"]), Path(row["destination"])
            assert sha(source) == row["sha256"] and source.stat().st_size == row["bytes"]
            out.parent.mkdir(parents=True, exist_ok=True)
            assert not out.exists()
            try:
                os.link(source, out)
                mode = "SAME_FILESYSTEM_HARD_LINK"
                assert (source.stat().st_dev, source.stat().st_ino) == (out.stat().st_dev, out.stat().st_ino)
                linked_files += 1
                linked_bytes += row["bytes"]
            except OSError as error:
                if error.errno != errno.EXDEV:
                    raise
                shutil.copy2(source, out)
                mode = "EXDEV_HASH_CHECKED_COPY2"
                copied_files += 1
                copied_bytes += row["bytes"]
            assert sha(source) == sha(out) == row["sha256"]
            assert source.stat().st_size == out.stat().st_size == row["bytes"]
            transports.append({**row, "transport": mode, "destination_device": out.stat().st_dev,
                               "destination_inode": out.stat().st_ino})
        assert sha(target / "receipt.json") == entry["original_receipt_sha256"]
        assert bundle(target / "artifact.olean") == rec["object_artifacts"]
        records.append({"module": rec["module"], "key": entry["key"],
            "source_sha256": rec["source_sha256"], "original_receipt_sha256": entry["original_receipt_sha256"],
            "retained_destination_receipt_sha256": sha(target / "receipt.json"),
            "original_receipt_directory": rec["receipt_directory"], "original_cached_object": rec["cached_object"],
            "native_runtime_digest": rec["native_runtime_digest"], "object_artifacts": rec["object_artifacts"],
            "file_transports": transports})
    for entry, rec in zip(plan, validated):
        for row in entry["files"]:
            assert sha(Path(row["source"])) == sha(Path(row["destination"])) == row["sha256"]
        assert bundle(Path(rec["cached_object"])) == rec["object_artifacts"]
        for binding in rec["direct_import_bindings"].values():
            assert bundle(Path(binding["path"])) == binding["artifacts"]
    receipt = {"status": "PASS_VERIFIED_IMMUTABLE_CACHE_TRANSPORT_ONLY", "destination": str(destination),
        "destination_graph_sha256": sha(destination / "DEPENDENCY-GRAPH.json"),
        "pre_use_plan_sha256": sha(evidence / "PRE-USE-TRANSPORT-PLAN.json"),
        "selected_manifest_sha256": sha(selected_path), "transport_seeder_sha256": sha(Path(__file__)),
        "new_entries_copied": len(records), "completed_entries_verified": len(records), "records": records,
        "hard_linked_files": linked_files, "hard_linked_bytes": linked_bytes,
        "exdev_copied_files": copied_files, "exdev_copied_bytes": copied_bytes,
        "pre_post_original_and_destination_identity_checks_pass": True,
        "receipt_bytes_rewritten": False, "target_or_audit_pass_copied": False,
        "new_builder_must_measure_imports_and_native_runtime_before_reuse": True,
        "original_cached_objects_and_imported_companions_written": False,
        "evidence": str(evidence.relative_to(ROOT))}
    save(evidence / "RECEIPT.json", receipt)
    save(destination / "CACHE-SEED-RECEIPT.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "new_entries_copied", "hard_linked_files", "hard_linked_bytes",
                                          "exdev_copied_files", "exdev_copied_bytes", "evidence"]}))


if __name__ == "__main__":
    main()
