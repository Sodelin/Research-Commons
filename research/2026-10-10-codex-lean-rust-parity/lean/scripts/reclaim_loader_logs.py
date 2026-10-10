#!/usr/bin/env python3
"""Reclaim only verified losslessly archived completed-run loader diagnostics.

Validate the whole manifest against unchanged completed invocation receipts
before removing any raw scratch log. Compiled objects, receipts, stdout/stderr,
sources and audits are never removed. Archives remain in ignored scratch.
"""
from __future__ import annotations
import argparse
import datetime
import gzip
import hashlib
import json
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def validate_archive(row):
    archive = Path(row["archive_path"])
    assert archive.is_relative_to(ROOT / ".build/native-loader-archives")
    assert archive.stat().st_size == row["archive_bytes"]
    assert sha(archive) == row["archive_sha256"]
    digest = hashlib.sha256()
    count = 0
    with gzip.open(archive, "rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
            count += len(block)
    assert digest.hexdigest() == row["raw_sha256"] and count == row["raw_bytes"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = args.manifest.resolve()
    manifest_hash = sha(manifest)
    data = json.loads(manifest.read_bytes())
    assert data["status"] == "PASS_LOSSLESS_COMPLETED_LOADER_ARCHIVES_ORIGINALS_RETAINED"
    run = Path(data["run"]).resolve()
    assert run.is_relative_to(ROOT / ".build/runs")
    final_path = run / "FINAL-RECEIPT.json"
    final_hash = sha(final_path)
    final = json.loads(final_path.read_bytes())
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
    assert final["counts"] == {"fresh_components": 1340}
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    expected = {}
    protected = {str(final_path): final_hash}
    for path in sorted((run / "attempts").glob("*/receipt.json")):
        protected[str(path)] = sha(path)
        receipt = json.loads(path.read_bytes())
        assert receipt["status"] == "PASS_FRESH_KERNEL_CHECK"
        for pin in receipt["native_loader_outputs"]:
            raw = Path(pin["path"])
            assert raw.is_relative_to(path.parent) and raw.name.startswith("NATIVE-LOADER.")
            assert str(raw) not in expected
            expected[str(raw)] = (pin["sha256"], str(path), protected[str(path)])
    rows = data["logs"]
    assert len(rows) == len(expected) == 1342
    assert len({r["raw_path"] for r in rows}) == len(rows)
    assert {r["raw_path"] for r in rows} == set(expected)
    for index, row in enumerate(rows, 1):
        assert expected[row["raw_path"]] == (row["raw_sha256"], row["receipt_path"], row["receipt_sha256"])
        validate_archive(row)
        raw = Path(row["raw_path"])
        assert raw.is_relative_to(run / "attempts")
        if raw.exists():
            assert sha(raw) == row["raw_sha256"] and raw.stat().st_size == row["raw_bytes"]
        if index % 200 == 0:
            print(json.dumps({"verified_logs": index}), flush=True)
    assert sha(manifest) == manifest_hash and sha(final_path) == final_hash
    for path, digest in protected.items():
        assert sha(Path(path)) == digest
    removed = 0
    for row in rows:
        raw = Path(row["raw_path"])
        if raw.exists():
            raw.unlink()
            removed += row["raw_bytes"]
    assert all(sha(Path(path)) == digest for path, digest in protected.items())
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    ledger = {"status": "PASS_VERIFIED_LOADER_DIAGNOSTIC_RECLAIM",
              "utc": stamp, "original_run": str(run),
              "original_final_receipt_sha256": final_hash,
              "archive_manifest": str(manifest), "archive_manifest_sha256": manifest_hash,
              "archived_logs": len(rows), "raw_bytes_reclaimed_this_execution": removed,
              "lossless_raw_log_identities": rows,
              "protected_receipt_sha256": protected,
              "receipt_or_object_or_source_bytes_removed": False,
              "archive_and_decompressed_raw_hashes_verified": True,
              "restoration": "python3 scripts/restore_loader_logs.py MANIFEST --module MODULE --restore",
              "cache_authentication": "All original invocation and import/native bundle receipts remain unchanged; raw diagnostic hashes can be reverified or restored from the authenticated gzip manifest."}
    save(ROOT / "evidence/native-loader-reclaim" / stamp / "RECEIPT.json", ledger)
    save(ROOT / "NATIVE-LOADER-RECLAIM-RESULT.json", ledger)
    print(json.dumps({k: ledger[k] for k in ["status", "archived_logs", "raw_bytes_reclaimed_this_execution"]}))


if __name__ == "__main__":
    main()
