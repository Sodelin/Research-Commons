#!/usr/bin/env python3
"""Create an additive frozen corpus snapshot without changing the original inventory."""
from __future__ import annotations
import argparse
import csv
import gzip
import io
import json
import os
from pathlib import Path
import build_inventory


def render(revision: str, observed: str, out: Path) -> dict[str, bytes]:
    rendered = build_inventory.inventory(revision, observed)
    repo = Path(build_inventory.git("rev-parse", "--show-toplevel").decode().strip())
    prefix = os.path.relpath(repo, out).replace(os.sep, "/") + "/"
    index = rendered["PACKET-INDEX.md"].decode().replace("](../../", "](" + prefix)
    rendered["PACKET-INDEX.md"] = index.encode()
    obj = json.loads(rendered["INVENTORY.json"])
    obj["scope"] = ("All tracked tree entries at the frozen successor commit, including "
                    "then-published lane packets and navigation; excludes later uncommitted "
                    "or post-snapshot files.")
    obj["predecessor_inventory"] = "../../INVENTORY.json"
    obj["read_depth"] = ("Complete tracked-path metadata enumeration and automatic "
                         "first heading of one entry point per packet only; no new proof review.")
    rendered["INVENTORY.json"] = (json.dumps(obj, indent=2, ensure_ascii=False) + "\n").encode()
    predecessor_dir = Path(__file__).resolve().parent
    predecessor = json.loads((predecessor_dir / "INVENTORY.json").read_bytes())
    def records(data: bytes) -> dict[str, dict[str, str]]:
        rows = csv.DictReader(io.StringIO(gzip.decompress(data).decode()), delimiter="\t")
        return {row["path"]: row for row in rows}
    old = records((predecessor_dir / "FROZEN-FILES.tsv.gz").read_bytes())
    new = records(rendered["FROZEN-FILES.tsv.gz"])
    old_packets = {p["path"] for p in predecessor["packets"]}
    delta = {
        "schema": "frozen-corpus-metadata-delta-v1",
        "predecessor_commit": predecessor["commons_commit"],
        "successor_commit": obj["commons_commit"],
        "limits": "Path/blob metadata only; no inference of theorem novelty, execution or proof review.",
        "files": obj["files"], "packets": obj["research_packets"],
        "unique_blob_ids": obj["unique_blob_ids"],
        "added_paths": len(new.keys() - old.keys()),
        "removed_paths": len(old.keys() - new.keys()),
        "changed_blob_paths": sum(old[p]["blob"] != new[p]["blob"] for p in old.keys() & new.keys()),
        "new_packets": sorted({p["path"] for p in obj["packets"]} - old_packets),
        "root_status_paths": [
            {"path": p, "blob": new[p]["blob"], "bytes": new[p]["bytes"]}
            for p in ["README.md", "RESEARCH-STATUS.md", "START-HERE.md", "projects.md"] if p in new
        ],
    }
    rendered["DELTA.json"] = (json.dumps(delta, indent=2) + "\n").encode()
    return rendered


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--observed", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    out = Path(args.output).resolve()
    if not args.check:
        out.mkdir(parents=True, exist_ok=True)
    rendered = render(args.revision, args.observed, out)
    for name, contents in rendered.items():
        destination = out / name
        if args.check:
            if destination.read_bytes() != contents:
                raise SystemExit(f"Successor inventory mismatch: {name}")
        else:
            if destination.exists():
                raise SystemExit(f"Refusing to overwrite existing snapshot file: {name}")
            destination.write_bytes(contents)
    obj = json.loads(rendered["INVENTORY.json"])
    print(json.dumps({"check": args.check, "commit": obj["commons_commit"],
                      "files": obj["files"], "packets": obj["research_packets"],
                      "output": str(out)}))


if __name__ == "__main__":
    main()
