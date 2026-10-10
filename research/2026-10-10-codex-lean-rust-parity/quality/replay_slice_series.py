#!/usr/bin/env python3
"""Replay the new published symbolic residual checker in a preserved directory."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PACKET = Path(__file__).resolve().parents[1]
SOURCE = PACKET.parent / "2026-10-10-dot-g3-variable-count-exact-slice-1300z"
OUT = PACKET / "quality/evidence/latest-slice-arithmetic-replay-1"


def pin(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    OUT.mkdir(parents=True, exist_ok=False)
    script, expected = SOURCE / "check_residual_series.py", SOURCE / "check_residual_series.log"
    before = {str(p): pin(p) for p in (script, expected)}
    copied = OUT / script.name
    copied.write_bytes(script.read_bytes())
    (OUT / "published.log").write_bytes(expected.read_bytes())
    run = subprocess.run([sys.executable, str(copied)], cwd=OUT,
                         capture_output=True, timeout=60, check=False)
    (OUT / "stdout").write_bytes(run.stdout)
    (OUT / "stderr").write_bytes(run.stderr)
    after = {str(p): pin(p) for p in (script, expected)}
    receipt = {"schema": "published_symbolic_slice_replay_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": run.returncode == 0 and not run.stderr
                and run.stdout == expected.read_bytes() and before == after,
        "exit_code": run.returncode, "source_before": before, "source_after": after,
        "copied_script": pin(copied), "stdout": pin(OUT / "stdout"),
        "stderr": pin(OUT / "stderr"), "python": sys.version,
        "python_executable": sys.executable,
        "reviewer": pin(Path(__file__)),
        "scope": "Fresh exact symbolic coefficient/derivative/log-series identities only, with byte-identical published output. No analytic tail/localization proof, returned radius/count cap, RCF search, physical witness or Lean verification executed."}
    (OUT / "RECEIPT.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "exit_code": run.returncode,
                      "published_output_equal": run.stdout == expected.read_bytes()}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
