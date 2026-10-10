#!/usr/bin/env python3
"""Copy verified completed component cache entries into an isolated workspace.

Only exact source/compiler/import/object/native keys are eligible. The original
receipt bytes remain unchanged, so subsequent builders report authenticated
cache reuse rather than current-run fresh compilation. No target pass is copied.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import shutil
from check_core import bundle, COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--source-cache", type=Path, action="append", default=[],
                        help="Additional completed cache; original receipt bytes remain pinned.")
    args = parser.parse_args()
    destination = args.destination.resolve()
    graph = json.loads((destination / "DEPENDENCY-GRAPH.json").read_bytes())
    selected = {(m, row["sha256"]) for target in graph["targets"].values()
                for m, row in target["modules"].items()}
    records = []
    copied = 0
    caches = [ROOT / ".build/cache"] + [p.resolve() for p in args.source_cache]
    for entry in [entry for cache in caches for entry in sorted(cache.iterdir())]:
        if not (entry / "receipt.json").is_file() or entry.name.startswith("."):
            continue
        rec = json.loads((entry / "receipt.json").read_bytes())
        if (rec["module"], rec["source_sha256"]) not in selected:
            continue
        assert rec["status"] == "PASS_FRESH_KERNEL_CHECK"
        assert rec["compiler_sha256"] == COMPILER and rec["mathlib_commit"] == "0df444a360eaa60ab8c11dca51a86af692955474"
        assert rec["source_and_imports_stable"] and rec["native_initialized_libraries_bound"]
        assert rec["exit_code"] == 0 and all(flag in rec["command"] for flag in
            ["-j1", "-t0", "-Ddebug.skipKernelTC=false"])
        source = destination / "source-store" / (rec["source_sha256"] + ".lean")
        assert sha(source) == rec["source_sha256"]
        for imported, expected in rec["direct_import_bindings"].items():
            assert bundle(Path(expected["path"])) == expected["artifacts"], (rec["module"], imported)
        assert bundle(Path(rec["cached_object"])) == rec["object_artifacts"]
        key_data = {"module": rec["module"], "source": rec["source_sha256"],
            "compiler": COMPILER, "mathlib": rec["mathlib_commit"], "trust": 0,
            "kernel_check": True, "imports": rec["direct_import_artifacts"],
            "native_runtime_digest": rec["native_runtime_digest"],
            "artifact_boundary": "olean-private-server-ilean-ir-native-v3"}
        if rec["module"] == "ThetaCertificate5" and rec["source_sha256"] == "e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab":
            key_data["resource_exception"] = {"memory_mib": 6144, "seconds": 600}
        assert hashlib.sha256(json.dumps(key_data, sort_keys=True).encode()).hexdigest() == entry.name
        target = destination / ".build/cache" / entry.name
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert (target / "receipt.json").read_bytes() == (entry / "receipt.json").read_bytes()
            assert bundle(target / "artifact.olean") == rec["object_artifacts"]
        else:
            shutil.copytree(entry, target)
            copied += 1
        records.append({"module": rec["module"], "key": entry.name,
            "source_sha256": rec["source_sha256"], "original_receipt_sha256": sha(entry / "receipt.json"),
            "original_receipt_directory": rec["receipt_directory"],
            "native_runtime_digest": rec["native_runtime_digest"], "object_artifacts": rec["object_artifacts"]})
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/cache-admission" / stamp
    receipt = {"status": "PASS_VERIFIED_COMPONENT_CACHE_COPY_ONLY", "destination": str(destination),
        "destination_graph_sha256": sha(destination / "DEPENDENCY-GRAPH.json"),
        "source_caches": [str(p) for p in caches], "new_entries_copied": copied,
        "completed_entries_verified": len(records), "records": records,
        "receipt_bytes_rewritten": False, "target_or_audit_pass_copied": False,
        "new_builder_must_measure_imports_and_native_runtime_before_reuse": True}
    save(evidence / "RECEIPT.json", receipt)
    save(destination / "CACHE-SEED-RECEIPT.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "new_entries_copied", "completed_entries_verified", "destination"]}))


if __name__ == "__main__":
    main()
