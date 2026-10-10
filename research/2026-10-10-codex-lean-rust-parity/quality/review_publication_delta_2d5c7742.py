#!/usr/bin/env python3
"""Preserve a bounded byte review of the six newest published research commits."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
BASE = "44d29bc9cfcf0e815005e4f432506051e3782fd7"
HEAD = "2d5c7742413aa14a8cc46cdc70a8b0a009b85e7e"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def main():
    paths = git("diff", "--name-only", BASE, HEAD).decode().splitlines()
    rows = []
    for path in paths:
        raw, published = (ROOT / path).read_bytes(), git("show", f"{HEAD}:{path}")
        rows.append({"path": path, "bytes": len(raw),
                     "sha256": hashlib.sha256(raw).hexdigest(),
                     "published_sha256": hashlib.sha256(published).hexdigest(),
                     "pass": raw == published})
    directories = sorted({"/".join(path.split("/")[:2]) for path in paths})
    commits = git("rev-list", "--reverse", f"{BASE}..{HEAD}").decode().splitlines()
    receipt = {"schema": "bounded_publication_delta_byte_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "base": BASE, "head": HEAD,
        "commits": commits, "packet_directories": directories, "files": rows,
        "pass": len(commits) == 6 and len(directories) == 2 and len(rows) == 27
                and all(row["pass"] for row in rows),
        "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Six additional published commits: one G3 exact-slice/effectivity/base-recovery packet and G4 attenuation/weak-scale/prior supplements. Earlier frozen inventories remain dated independent snapshots. Byte coverage does not certify the mathematical claims or exhaust historical discovery coverage."}
    output = PACKET / "quality/evidence/publication-delta-2d5c7742/RECEIPT.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "commits": len(commits),
                      "packets": len(directories), "files": len(rows)}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
