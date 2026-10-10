#!/usr/bin/env python3
"""Create a byte-reversible portable projection of an immutable snapshot."""
from __future__ import annotations
import argparse
import datetime
import gzip
import hashlib
import json
from pathlib import Path
from check_core import save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--label", required=True)
    parser.add_argument("--result-file", required=True)
    args = parser.parse_args()
    certificate_path = args.certificate.resolve()
    original = json.loads(certificate_path.read_bytes())
    snapshot = ROOT / original["evidence"]
    assert snapshot.is_relative_to(ROOT / "evidence") and snapshot.is_dir()
    assert sha(snapshot / "CERTIFICATE.json") == sha(certificate_path)
    for row in original["copied_evidence_files"]:
        assert sha(snapshot / row["path"]) == row["sha256"]
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    destination = ROOT / "evidence" / args.label / stamp
    assert destination.is_relative_to(ROOT / "evidence")
    destination.mkdir(parents=True)
    original_files = {str(path.relative_to(snapshot)): {"sha256": sha(path), "bytes": path.stat().st_size}
                      for path in snapshot.rglob("*") if path.is_file() and not path.is_symlink()}
    rows = []
    renamed = {"CERTIFICATE.json": "ORIGINAL-CERTIFICATE.json",
               "COMPRESSED-DISTRIBUTIONS.json": "ORIGINAL-COMPRESSED-DISTRIBUTIONS.json"}
    for relative, identity in sorted(original_files.items()):
        source = snapshot / relative
        target_relative = Path(renamed.get(relative, relative))
        row = distribute_file(source, destination, target_relative,
            force_gzip=source.name in {"ACTUAL-IMPORTED-ARTIFACTS.json", "RESULT.json"})
        rows.append({"original_path": relative, "original_sha256": identity["sha256"],
                     "original_bytes": identity["bytes"], "distribution": row})
    assert all(sha(snapshot / relative) == item["sha256"] for relative, item in original_files.items())
    # Original audit archives keep their exact archive and decoded byte identity.
    existing = json.loads((snapshot / "COMPRESSED-DISTRIBUTIONS.json").read_bytes())["distributions"]
    added = [r["distribution"] for r in rows if r["distribution"].get("encoding") == "gzip"]
    save(destination / "COMPRESSED-DISTRIBUTIONS.json", {
         "status": "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION", "distributions": existing + added,
         "original_snapshot_and_compiler_run_unchanged": True,
         "restore_command": "python3 scripts/restore_distributed_evidence.py MANIFEST --output DESTINATION"})
    restore = {"status": "PASS_COMPLETE_ORIGINAL_SNAPSHOT_RESTORABLE", "original_snapshot": str(snapshot),
         "original_certificate_sha256": sha(certificate_path), "files": rows,
         "original_snapshot_files": len(rows), "original_snapshot_bytes": sum(r["original_bytes"] for r in rows),
         "verify_or_restore_command": "python3 scripts/restore_evidence_projection.py RESTORE-MANIFEST.json [--output DESTINATION]"}
    save(destination / "RESTORE-MANIFEST.json", restore)
    portable = dict(original)
    portable.update({"evidence": str(destination.relative_to(ROOT)),
         "copied_evidence_files": [r["distribution"] for r in rows],
         "compressed_distributions_manifest_sha256": sha(destination / "COMPRESSED-DISTRIBUTIONS.json"),
         "original_snapshot_sha256_manifest": "RESTORE-MANIFEST.json",
         "restore_manifest_sha256": sha(destination / "RESTORE-MANIFEST.json"),
         "original_certificate_sha256": sha(certificate_path),
         "original_certificate_preserved_path": "ORIGINAL-CERTIFICATE.json",
         "projection_helper_sha256": sha(Path(__file__)),
         "projection_changes_only_file_distribution": True,
         "historical_snapshot_unchanged": True})
    save(destination / "CERTIFICATE.json", portable)
    output = ROOT / args.result_file
    assert output.parent == ROOT and output.suffix == ".json"
    save(output, portable)
    print(json.dumps({"status": portable["status"], "evidence": portable["evidence"],
         "original_snapshot_bytes": restore["original_snapshot_bytes"],
         "portable_bytes": sum(p.stat().st_size for p in destination.rglob("*") if p.is_file())}))


if __name__ == "__main__":
    main()
