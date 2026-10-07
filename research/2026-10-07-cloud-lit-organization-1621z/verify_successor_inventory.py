#!/usr/bin/env python3
"""Verify an additive metadata snapshot; this does not review scientific claims."""
from __future__ import annotations
import argparse
import csv
import datetime
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote, urlsplit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True)
    args = parser.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"]).decode().strip())
    packet = Path(__file__).resolve().parent
    snapshot = Path(args.snapshot).resolve()
    inv = json.loads((snapshot / "INVENTORY.json").read_bytes())
    original = json.loads((packet / "INVENTORY.json").read_bytes())
    commands = [
        ["python", "-B", str(packet / "build_successor_inventory.py"),
         "--revision", inv["commons_commit"], "--observed", inv["observed_utc"],
         "--output", str(snapshot), "--check"],
        ["python", "-B", str(packet / "build_inventory.py"),
         "--revision", original["commons_commit"], "--observed", original["observed_utc"], "--check"],
        ["git", "diff", "--check"],
    ]
    checks = []
    for command in commands:
        result = subprocess.run(command, cwd=repo, capture_output=True, text=True)
        checks.append({"argv": [x.replace(str(repo) + "/", "") for x in command],
                       "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr})
        if result.returncode:
            raise SystemExit(json.dumps(checks, indent=2))
    def rows(path: Path) -> list[dict[str, str]]:
        return list(csv.DictReader(io.StringIO(gzip.decompress(path.read_bytes()).decode()), delimiter="\t"))
    tracked = rows(snapshot / "FROZEN-FILES.tsv.gz")
    assert len(tracked) == len({row["path"] for row in tracked}) == inv["files"]
    assert len({row["blob"] for row in tracked}) == inv["unique_blob_ids"]
    assert len(inv["packets"]) == len({p["path"] for p in inv["packets"]}) == inv["research_packets"]
    dated = json.loads((packet / "VERIFICATION.json").read_bytes())
    retained = {}
    for name in ["INVENTORY.json", "PACKET-INDEX.md", "FROZEN-FILES.tsv.gz", "build_inventory.py"]:
        digest = hashlib.sha256((packet / name).read_bytes()).hexdigest()
        assert digest == dated["files"][name]["sha256"], name
        retained[name] = digest
    relative_links = 0
    broken = []
    markdown = sorted(packet.rglob("*.md"))
    for source in markdown:
        for raw in re.findall(r"(?<!!)\[[^\]]*\]\(([^\s)]+)(?:\s+[^)]*)?\)", source.read_text()):
            target = raw.strip("<>")
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or not parsed.path or parsed.path.startswith("/"):
                continue
            relative_links += 1
            if not (source.parent / unquote(parsed.path)).exists():
                broken.append({"source": str(source.relative_to(repo)), "target": target})
    if broken:
        raise SystemExit(json.dumps({"broken_relative_links": broken}, indent=2))
    covered = list(snapshot.glob("*")) + [packet / "README.md", packet / "build_successor_inventory.py",
                                          Path(__file__).resolve()]
    identities = {}
    for path in sorted(covered):
        if not path.is_file() or path.name == "VERIFICATION.json":
            continue
        data = path.read_bytes()
        identities[str(path.relative_to(repo))] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    receipt = {
        "schema": "successor-documentation-verification-v1",
        "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "source_commit": inv["commons_commit"], "source_tree": inv["commons_tree"],
        "source_observed_utc": inv["observed_utc"], "executed_checks": checks,
        "tracked_paths": len(tracked), "unique_tracked_paths": len({row["path"] for row in tracked}),
        "unique_blob_ids": inv["unique_blob_ids"], "research_packets": inv["research_packets"],
        "retained_predecessor_sha256": retained,
        "markdown_files_checked": len(markdown), "relative_links_checked": relative_links,
        "link_check_scope": "All Markdown files within this additive literature/organization packet, including both indexes; file/directory existence only, fragments not validated.",
        "broken_relative_links": broken, "files": identities,
        "read_depth": inv["read_depth"],
        "scientific_scope": "Metadata inventory, regeneration, identity and documentation-link checks only; no new proof review or execution claims.",
        "dated_original_receipt": "../../VERIFICATION.json preserved; original README hash predates the successor pointer.",
    }
    (snapshot / "VERIFICATION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"verified": True, "commit": inv["commons_commit"], "files": len(tracked),
                      "packets": inv["research_packets"], "relative_links_checked": relative_links}))


if __name__ == "__main__":
    main()
