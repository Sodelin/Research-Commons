#!/usr/bin/env python3
"""Verify or restore every byte of an immutable evidence snapshot projection."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
from check_core import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = args.manifest.resolve()
    base = manifest.parent
    data = json.loads(manifest.read_bytes())
    assert data["status"] == "PASS_COMPLETE_ORIGINAL_SNAPSHOT_RESTORABLE"
    if args.output:
        assert args.output.resolve() != Path(data["original_snapshot"]).resolve(), "Restore to a separate directory."
    checked = 0
    for row in data["files"]:
        distribution = row["distribution"]
        path = base / distribution["path"]
        assert path.is_relative_to(base) and sha(path) == distribution["sha256"]
        digest, count = hashlib.sha256(), 0
        opener = gzip.open if distribution.get("encoding") == "gzip" else open
        with opener(path, "rb") as stream:
            while block := stream.read(1024 * 1024):
                digest.update(block)
                count += len(block)
        assert digest.hexdigest() == row["original_sha256"] and count == row["original_bytes"]
        if args.output:
            target = args.output.resolve() / row["original_path"]
            assert target.is_relative_to(args.output.resolve())
            if target.exists():
                assert sha(target) == row["original_sha256"], "Existing restore file differs."
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                temporary = Path(str(target) + ".incomplete")
                with opener(path, "rb") as stream, temporary.open("xb") as output:
                    shutil.copyfileobj(stream, output, 1024 * 1024)
                assert sha(temporary) == row["original_sha256"]
                temporary.replace(target)
        checked += 1
    print(json.dumps({"status": "PASS_ORIGINAL_SNAPSHOT_BYTE_IDENTITIES", "verified_files": checked,
                      "restored": bool(args.output)}))


if __name__ == "__main__":
    main()
