#!/usr/bin/env python3
"""Preserve and replay the latest finite G3 Jacobian and failed-route arithmetic."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    output = PACKET / "quality/evidence/local-boundary-arithmetic-replay-1"
    output.mkdir(parents=True, exist_ok=True)
    definitions = [
        ("2026-10-10-dot-g3-local-killing-recognizer-1238z", "check_transverse.py", "transverse-certificate.json"),
        ("2026-10-10-dot-g3-local-killing-recognizer-1238z", "independent_transverse_review.py", "transverse-certificate.json"),
        ("2026-10-10-dot-g3-retained-chart-limits-1250z/diagnostics", "check_active_killing_minimum.py", "active-killing-minimum-certificate.json"),
    ]
    originals = {}
    for directory, _, _ in definitions:
        source = ROOT / "research" / directory
        if directory not in originals:
            originals[directory] = {path.name: digest(path) for path in source.iterdir() if path.is_file()}
            destination = output / directory
            if destination.exists():
                raise RuntimeError("Preserved replay already exists; use a separately attributed attempt")
            shutil.copytree(source, destination)
    results = []
    for directory, script, certificate in definitions:
        copied = output / directory
        command = [sys.executable, str(copied / script)]
        started = time.monotonic()
        completed = subprocess.run(command, cwd=copied, capture_output=True, timeout=30, check=False)
        (copied / (Path(script).stem + ".fresh.stdout")).write_bytes(completed.stdout)
        (copied / (Path(script).stem + ".fresh.stderr")).write_bytes(completed.stderr)
        source = ROOT / "research" / directory
        result = {
            "source_script": str((source / script).relative_to(ROOT)),
            "source_sha256": digest(source / script), "command": command,
            "exit_code": completed.returncode, "wall_seconds": time.monotonic() - started,
            "stderr_empty": not completed.stderr,
            "stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
            "published_log_exact": completed.stdout == (source / (Path(script).stem + ".log")).read_bytes(),
            "generated_certificate_exact": (copied / certificate).read_bytes() == (source / certificate).read_bytes(),
            "certificate_sha256": digest(copied / certificate),
            "copied_script_unchanged": digest(copied / script) == digest(source / script),
        }
        result["pass"] = completed.returncode == 0 and all(result[key] for key in
            ("stderr_empty", "published_log_exact", "generated_certificate_exact", "copied_script_unchanged"))
        results.append(result)
    after = {directory: {path.name: digest(path) for path in (ROOT / "research" / directory).iterdir() if path.is_file()}
             for directory in originals}
    receipt = {
        "schema": "local_g3_boundary_finite_arithmetic_replay_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": originals == after and all(row["pass"] for row in results),
        "source_pins_before": originals, "source_pins_after": after, "source_stable": originals == after,
        "python": sys.executable, "python_sha256": digest(Path(sys.executable)),
        "scripts": results, "reviewer_sha256": digest(Path(__file__)),
        "scope": "Fresh exact Fraction Jacobian/inverse and independent integer-Bareiss verification, plus published rational/SymPy positive-definite critical-head failed-shortcut control. No cutoff, base, neighborhood, QE, native witness, Lean theorem or master recognition executed.",
    }
    (output / "RECEIPT.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "scripts": len(results),
                      "results": [{"script": row["source_script"], "pass": row["pass"]} for row in results]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
