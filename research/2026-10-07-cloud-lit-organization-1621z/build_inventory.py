#!/usr/bin/env python3
"""Inventory a frozen Git tree; artifact counts do not assert scientific status."""
from __future__ import annotations
import argparse
import collections
import gzip
import json
import re
import subprocess
from pathlib import Path


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args])


def category(path: str) -> str:
    suffix = Path(path).suffix.lower()
    if suffix == ".lean":
        return "Lean-source-including-copies-and-failures"
    if suffix in {".py", ".sh", ".cjs", ".js", ".cpp", ".c", ".wl", ".smt2"}:
        return "executable-or-solver-source"
    if suffix in {".md", ".bib", ".tex"}:
        return "prose-or-bibliography"
    if suffix in {".log", ".stdout", ".stderr", ".exit"}:
        return "execution-record-status-uninterpreted"
    if suffix in {".json", ".csv", ".tsv", ".sha256", ".toml", ".yml", ".yaml"}:
        return "structured-data-or-manifest"
    if suffix in {".gz", ".xz", ".zip", ".tar"}:
        return "compressed-artifact"
    return "other-artifact"


def inventory(revision: str, observed: str) -> dict[str, bytes]:
    commit = git("rev-parse", revision).decode().strip()
    tree = git("rev-parse", f"{commit}^{{tree}}").decode().strip()
    records = []
    for raw in git("ls-tree", "-r", "-l", "-z", commit).split(b"\0"):
        if not raw:
            continue
        header, path_raw = raw.split(b"\t", 1)
        mode, kind, blob, size = header.decode().split()
        path = path_raw.decode()
        records.append({"mode": mode, "kind": kind, "blob": blob,
                        "bytes": None if size == "-" else int(size),
                        "artifact_type": category(path), "path": path})
    records.sort(key=lambda r: r["path"])
    by_packet = collections.defaultdict(list)
    for r in records:
        pieces = r["path"].split("/")
        if len(pieces) >= 3 and pieces[0] == "research":
            by_packet["/".join(pieces[:2])].append(r)
    packets = []
    rows = ["# Complete research-packet index", "",
            f"Frozen Commons commit `{commit}`; tree `{tree}`. Observed {observed}.", "",
            "Each title is an automatic first-heading read from its selected entry point. "
            "This is complete tracked-path coverage at this snapshot, not proof review. "
            "Artifact counts include historical copies, guards, drafts, failures and support.", "",
            "| Packet / entry point | Automatic title | Files / Lean source / prose / execution records |",
            "|---|---|---|"]
    for path, items in sorted(by_packet.items()):
        by_path = {r["path"]: r for r in items}
        prose = [r["path"] for r in items if r["path"].endswith(".md")]
        preference = [f"{path}/{name}" for name in
                      ["README.md", "CURRENT-SCOPE.md", "PROOF.md", "REVIEW.md", "CHECKPOINT.md"]]
        entry = next((x for x in preference if x in by_path), prose[0] if prose else None)
        title = "No Markdown entry point"
        if entry:
            body = git("show", f"{commit}:{entry}").decode(errors="replace")
            match = re.search(r"^#{1,6}\s+(.+)$", body, re.MULTILINE)
            title = match.group(1).strip() if match else "No Markdown heading"
        counts = dict(sorted(collections.Counter(r["artifact_type"] for r in items).items()))
        packet = {"path": path, "entrypoint": entry, "automatic_title": title,
                  "read_depth": "mechanical-first-heading-only",
                  "files": len(items), "artifact_counts": counts}
        packets.append(packet)
        title_cell = title.replace("|", "\\|").replace("\n", " ")
        target = entry or path
        label = path.removeprefix("research/")
        nums = [len(items), counts.get("Lean-source-including-copies-and-failures", 0),
                counts.get("prose-or-bibliography", 0),
                counts.get("execution-record-status-uninterpreted", 0)]
        rows.append(f"| [{label}](../../{target}) | {title_cell} | {' / '.join(map(str, nums))} |")
    obj = {"schema": "commons-corpus-inventory-v1", "observed_utc": observed,
           "commons_commit": commit, "commons_tree": tree,
           "scope": "All tracked tree entries at frozen commit; self packet is added afterward.",
           "scientific_claim": "None from inventory metadata; use CORPUS-MAP and cited source receipts.",
           "files": len(records), "unique_blob_ids": len({r["blob"] for r in records}),
           "tracked_bytes_including_duplicate_blobs": sum(r["bytes"] or 0 for r in records),
           "root_counts": dict(sorted(collections.Counter(r["path"].split("/")[0] for r in records).items())),
           "artifact_counts": dict(sorted(collections.Counter(r["artifact_type"] for r in records).items())),
           "research_packets": len(packets), "packets": packets,
           "complete_file_list": "FROZEN-FILES.tsv.gz"}
    tsv = "mode\tkind\tblob\tbytes\tartifact_type\tpath\n"
    tsv += "".join("\t".join(str(r[k]) for k in
                     ["mode", "kind", "blob", "bytes", "artifact_type", "path"]) + "\n"
                   for r in records)
    return {"INVENTORY.json": (json.dumps(obj, indent=2, ensure_ascii=False) + "\n").encode(),
            "PACKET-INDEX.md": ("\n".join(rows) + "\n").encode(),
            "FROZEN-FILES.tsv.gz": gzip.compress(tsv.encode(), compresslevel=9, mtime=0)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--observed", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    out = Path(__file__).resolve().parent
    rendered = inventory(args.revision, args.observed)
    for name, content in rendered.items():
        destination = out / name
        if args.check:
            if destination.read_bytes() != content:
                raise SystemExit(f"Inventory mismatch: {name}")
        else:
            destination.write_bytes(content)
    result = json.loads(rendered["INVENTORY.json"])
    print(json.dumps({"check": args.check, "commit": result["commons_commit"],
                      "files": result["files"], "packets": result["research_packets"]}))


if __name__ == "__main__":
    main()
