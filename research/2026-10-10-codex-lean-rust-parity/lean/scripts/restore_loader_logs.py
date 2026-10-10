#!/usr/bin/env python3
"""Verify archived loader diagnostic identities; optionally restore selected bytes."""
from __future__ import annotations
import argparse
import gzip
import json
from pathlib import Path
import shutil
from check_core import sha
from reclaim_loader_logs import ROOT, validate_archive


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--restore", action="store_true")
    args = parser.parse_args()
    data = json.loads(args.manifest.read_bytes())
    rows = [r for r in data["logs"] if not args.module or r["invocation_module"] in args.module]
    assert rows and (not args.module or set(args.module) <= {r["invocation_module"] for r in rows})
    if args.restore:
        required = sum(r["raw_bytes"] for r in rows if not Path(r["raw_path"]).exists())
        assert shutil.disk_usage(ROOT).free >= required + 1024 ** 3
    for row in rows:
        assert sha(Path(row["receipt_path"])) == row["receipt_sha256"]
        validate_archive(row)
        raw = Path(row["raw_path"])
        assert raw.is_relative_to(ROOT / ".build/runs") and raw.name.startswith("NATIVE-LOADER.")
        if raw.exists():
            assert sha(raw) == row["raw_sha256"] and raw.stat().st_size == row["raw_bytes"]
        elif args.restore:
            temporary = Path(str(raw) + ".restoring")
            assert not temporary.exists()
            with gzip.open(row["archive_path"], "rb") as source, temporary.open("xb") as target:
                shutil.copyfileobj(source, target, 1024 * 1024)
            assert sha(temporary) == row["raw_sha256"] and temporary.stat().st_size == row["raw_bytes"]
            temporary.replace(raw)
    print(json.dumps({"status": "PASS_ARCHIVE_AND_ORIGINAL_RECEIPT_IDENTITIES",
                      "logs": len(rows), "restored": args.restore}))


if __name__ == "__main__":
    main()
