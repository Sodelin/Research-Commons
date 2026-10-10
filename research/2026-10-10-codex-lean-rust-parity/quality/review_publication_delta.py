#!/usr/bin/env python3
"""Read-only byte inventory of the six research packets after snapshot d47787d8."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
BASE = "d47787d8f4f9a91a4d66dbc5769a4358d0383c0d"
HEAD = "4d7a0467"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def main():
    head = git("rev-parse", HEAD).decode().strip()
    paths = git("diff", "--name-only", BASE, head).decode().splitlines()
    rows = []
    for path in paths:
        raw = (ROOT / path).read_bytes()
        published = git("show", f"{head}:{path}")
        rows.append({"path": path, "bytes": len(raw),
                     "sha256": hashlib.sha256(raw).hexdigest(),
                     "published_sha256": hashlib.sha256(published).hexdigest(),
                     "pass": raw == published})
    directories = sorted({"/".join(path.split("/")[:2]) for path in paths})
    commits = git("rev-list", "--reverse", f"{BASE}..{head}").decode().splitlines()
    result = {"schema": "bounded_publication_delta_byte_review_v1",
              "observed_utc": datetime.now(timezone.utc).isoformat(),
              "base": BASE, "head": head, "commits": commits,
              "packet_directories": directories, "files": rows,
              "pass": len(commits) == 6 and len(directories) == 6 and len(rows) == 40
                      and all(row["pass"] for row in rows),
              "scope": "Additional six published research packets only. Frozen earlier 13-packet discovery and source-map reviews remain separate. This is byte coverage, not proof acceptance or an exhaustive historical review.",
              "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output = PACKET / "quality/evidence/publication-delta-4d7a0467/RECEIPT.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": result["pass"], "commits": len(commits),
                      "packets": len(directories), "files": len(rows)}))
    return not result["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
