#!/usr/bin/env python3
"""Independently hash preserved run evidence against its declared scratch originals.

This reads receipts and bytes only. It never invokes Lean, Rust, or a law provider,
and preservation PASS does not promote a failed or incomplete mathematical run.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def review(path):
    raw = path.read_bytes()
    manifest = json.loads(raw)
    native = "preserved_files" not in manifest
    records = manifest["files" if native else "preserved_files"]
    base = PACKET if native else PACKET / "lean" / manifest["evidence"]
    seen = set()
    rows = []
    for record in records:
        relative = record["preserved" if native else "path"]
        part = Path(relative)
        if part.is_absolute() or ".." in part.parts or relative in seen:
            raise ValueError("Invalid or duplicate preserved path: " + relative)
        seen.add(relative)
        preserved = base / part
        if preserved.is_symlink() or not preserved.is_file():
            raise ValueError("Missing regular preserved file: " + str(preserved))
        saved = preserved.read_bytes()
        if len(saved) != record["bytes"] or digest(saved) != record["sha256"]:
            raise ValueError("Preserved identity mismatch: " + relative)
        restored = gzip.decompress(saved) if record.get("encoding") == "gzip" else saved
        original = Path(record["original" if native else "original_path"])
        if not original.is_absolute() or not original.is_file():
            raise ValueError("Missing declared scratch original: " + str(original))
        original_raw = original.read_bytes()
        declared = record.get("original_sha256", record["sha256"])
        if digest(original_raw) != declared or restored != original_raw:
            raise ValueError("Saved/restored bytes differ from scratch: " + relative)
        if record.get("encoding") == "gzip":
            if (len(restored) != record["restored_bytes"]
                    or digest(restored) != record["restored_sha256"]):
                raise ValueError("Restored identity mismatch: " + relative)
        rows.append({"path": relative, "sha256": digest(saved), "bytes": len(saved),
                     "restored_sha256": digest(restored), "restored_bytes": len(restored)})
    return {"manifest": str(path.relative_to(PACKET)), "sha256": digest(raw),
            "declared_status": manifest.get("status"), "files": len(rows),
            "preserved_bytes": sum(row["bytes"] for row in rows),
            "restored_bytes": sum(row["restored_bytes"] for row in rows),
            "all_saved_and_original_bytes_equal": True, "identities": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="+", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    reviews = [review(path.resolve()) for path in args.manifest]
    result = {"schema": "independent_preservation_review_v1",
              "status": "PASS_SAVED_AND_SCRATCH_BYTE_IDENTITY",
              "observed_utc": datetime.now(timezone.utc).isoformat(),
              "reviewer_sha256": digest(Path(__file__).read_bytes()),
              "compiler_or_law_provider_called": False,
              "mathematical_acceptance_inferred": False, "reviews": reviews}
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "manifests": len(reviews),
                      "files": sum(row["files"] for row in reviews),
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
