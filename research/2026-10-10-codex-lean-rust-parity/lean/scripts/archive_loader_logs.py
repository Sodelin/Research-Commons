#!/usr/bin/env python3
"""Copy completed loader logs into verified lossless gzip scratch archives.

Original logs and receipts are never deleted or rewritten. Each decompressed
archive is checked against the exact hash recorded by its bounded invocation.
This makes later space reclamation reviewable without changing run provenance.
"""
from __future__ import annotations
import argparse
import datetime
import gzip
import hashlib
import json
from pathlib import Path
import shutil
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", type=Path)
    args = parser.parse_args()
    run = args.run.resolve()
    assert run.is_relative_to(ROOT / ".build")
    archive_root = ROOT / ".build/native-loader-archives" / run.name
    archive_root.mkdir(parents=True, exist_ok=True)
    rows = []
    for receipt_path in sorted((run / "attempts").glob("*/receipt.json")):
        rec = json.loads(receipt_path.read_bytes())
        if rec["status"] != "PASS_FRESH_KERNEL_CHECK":
            continue
        for pin in rec["native_loader_outputs"]:
            raw = Path(pin["path"])
            assert raw.is_relative_to(receipt_path.parent)
            assert sha(raw) == pin["sha256"]
            target = archive_root / raw.relative_to(run)
            target = Path(str(target) + ".gz")
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                temporary = Path(str(target) + ".incomplete")
                with raw.open("rb") as source, temporary.open("wb") as destination:
                    with gzip.GzipFile(filename="", mode="wb", fileobj=destination, mtime=0) as compressed:
                        shutil.copyfileobj(source, compressed, 1024 * 1024)
                temporary.rename(target)
            with gzip.open(target, "rb") as decoded:
                assert hashlib.file_digest(decoded, "sha256").hexdigest() == pin["sha256"]
            assert sha(raw) == pin["sha256"]
            rows.append({"raw_path": str(raw), "raw_sha256": pin["sha256"],
                         "raw_bytes": raw.stat().st_size,
                         "archive_path": str(target), "archive_sha256": sha(target),
                         "archive_bytes": target.stat().st_size,
                         "receipt_path": str(receipt_path), "receipt_sha256": sha(receipt_path),
                         "invocation_module": rec["module"], "decompression_hash_verified": True})
        if len(rows) % 100 == 0:
            print(json.dumps({"verified_logs": len(rows)}), flush=True)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/native-loader-archives" / stamp
    receipt = {"status": "PASS_LOSSLESS_COMPLETED_LOADER_ARCHIVES_ORIGINALS_RETAINED",
               "run": str(run), "archive_root": str(archive_root),
               "logs": rows, "verified_logs": len(rows),
               "raw_bytes": sum(r["raw_bytes"] for r in rows),
               "archive_bytes": sum(r["archive_bytes"] for r in rows),
               "original_log_or_receipt_bytes_changed": False,
               "original_logs_removed": False, "scope": "Completed invocation diagnostic copies; not a new kernel or target acceptance."}
    save(evidence / "RECEIPT.json", receipt)
    save(ROOT / "NATIVE-LOADER-ARCHIVE-PREPARATION.json", receipt)
    print(json.dumps({k: receipt[k] for k in ["status", "verified_logs", "raw_bytes", "archive_bytes"]}))


if __name__ == "__main__":
    main()
