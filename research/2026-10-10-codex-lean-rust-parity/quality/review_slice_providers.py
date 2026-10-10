#!/usr/bin/env python3
"""Read back the older published providers pinned by the newest G3 slice."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]


def main():
    manifest = ROOT / "research/2026-10-10-dot-g3-variable-count-exact-slice-1300z/PROVIDER-PINS.json"
    providers = json.loads(manifest.read_text())
    rows = []
    for provider in providers:
        raw = subprocess.check_output(["git", "cat-file", "blob", provider["git_blob"]], cwd=ROOT)
        actual = hashlib.sha256(raw).hexdigest()
        rows.append({"name": provider["name"], "url": provider["url"],
                     "bytes": len(raw), "sha256": actual,
                     "git_blob": provider["git_blob"],
                     "pass": actual == provider["sha256"]
                             and provider["git_blob"] == provider["expected_git_blob"]})
    receipt = {"schema": "g3_slice_older_provider_blob_readback_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": len(rows) == 10 and all(row["pass"] for row in rows), "providers": rows,
        "manifest_sha256": hashlib.sha256(manifest.read_bytes()).hexdigest(),
        "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact published-byte identity of ten inherited October6 provider/review blobs. Attribution and source interfaces remain those of the published hand reviews; no independent proof, literature or novelty audit claimed."}
    output = PACKET / "quality/evidence/latest-slice-provider-review-1/RECEIPT.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "providers": len(rows)}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
