#!/usr/bin/env python3
"""Verify or restore the exact raw bytes of distributed gzip evidence.

By default only verify. --output names a separate restoration directory;
existing files are accepted only when their exact original identities match.
"""
from __future__ import annotations
import argparse
import gzip
import json
from pathlib import Path
import shutil
from check_core import sha
from evidence_distribution import verify_distribution


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest = args.manifest.resolve()
    data = json.loads(manifest.read_bytes())
    for row in data["distributions"]:
        for field in ["path", "restored_path"]:
            relative = Path(row[field])
            assert not relative.is_absolute() and ".." not in relative.parts
        verify_distribution(manifest.parent, row)
        if args.output:
            target = args.output.resolve() / row["restored_path"]
            if target.exists():
                assert sha(target) == row["restored_sha256"]
                assert target.stat().st_size == row["restored_bytes"]
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            temporary = Path(str(target) + ".restoring")
            assert not temporary.exists()
            with gzip.open(manifest.parent / row["path"], "rb") as source, temporary.open("xb") as output:
                shutil.copyfileobj(source, output, 1024 * 1024)
            assert sha(temporary) == row["restored_sha256"]
            assert temporary.stat().st_size == row["restored_bytes"]
            temporary.replace(target)
    print(json.dumps({"status": "PASS_LOSSLESS_DISTRIBUTION_VERIFICATION",
                      "files": len(data["distributions"]), "restored": bool(args.output)}))


if __name__ == "__main__":
    main()
