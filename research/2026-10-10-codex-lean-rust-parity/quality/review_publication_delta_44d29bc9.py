#!/usr/bin/env python3
"""Read-only byte inventory of the five publication commits after snapshot 4d7a0467."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
BASE = "4d7a046790a8f55e120d9ccd8097aefefc2f2025"
HEAD = "44d29bc9cfcf0e815005e4f432506051e3782fd7"


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
              "pass": len(commits) == 5 and len(directories) == 4 and len(rows) == 39
                      and all(row["pass"] for row in rows),
              "scope": "Additional five commits, three new packets and one additive prior-attribution supplement only. Earlier frozen discovery/source-map and40-file publication review remain separate. This is byte coverage, not proof acceptance or an exhaustive historical review.",
              "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    output = PACKET / "quality/evidence/publication-delta-44d29bc9/RECEIPT.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": result["pass"], "commits": len(commits),
                      "packets": len(directories), "files": len(rows)}))
    return not result["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
