#!/usr/bin/env python3
"""Replay the cutoff's finite chart certificate, not its full construction."""
import hashlib
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
COMMONS = PACKET.parents[1]
SOURCE = COMMONS / "research/2026-10-10-dot-g3-computable-killing-cutoff-1132z"
EVIDENCE = PACKET / "quality/evidence/cutoff-chart-replay-1"
SCRATCH = Path("/workspace/scratch/codex-cutoff-chart-replay-1")


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def main():
    EVIDENCE.mkdir(parents=True, exist_ok=False)
    SCRATCH.mkdir(parents=True, exist_ok=False)
    before = {name: identity(SOURCE / name) for name in ("check_chart_pivot.py", "chart-pivot.json")}
    shutil.copyfile(SOURCE / "check_chart_pivot.py", SCRATCH / "check_chart_pivot.py")
    result = subprocess.run([sys.executable, "-I", "-B", str(SCRATCH / "check_chart_pivot.py")],
                            cwd=SCRATCH, capture_output=True, timeout=30)
    for name, data in (("stdout", result.stdout), ("stderr", result.stderr)):
        (EVIDENCE / name).write_bytes(data)
    match = result.returncode == 0 and identity(SCRATCH / "chart-pivot.json") == before["chart-pivot.json"]
    physical_derivatives = False
    normal_annihilation = False
    if result.returncode == 0:
        shutil.copyfile(SCRATCH / "chart-pivot.json", EVIDENCE / "chart-pivot.json")
        chart = json.loads((EVIDENCE / "chart-pivot.json").read_text())
        normal = json.loads((COMMONS / "research/2026-10-10-dot-g3-fair-head-killing-1111z/normal_certificate.json").read_text())["c"]
        expected = []
        for exponent in chart["Lambda"]:
            row = [Fraction(exponent), Fraction(1)]
            for probability, survival in ((Fraction(1, 2), Fraction(1, 2)),
                                          (Fraction(1, 2), Fraction(1, 3))):
                denominator = 1 - probability + probability * survival**exponent
                row.extend([(1 - survival**exponent) / denominator,
                            -probability * exponent * survival**(exponent - 1) / denominator])
            expected.append(row)
        supplied = [[Fraction(value) for value in row] for row in chart["J"]]
        physical_derivatives = supplied == expected
        normal_annihilation = all(sum(coefficient * row[column] for coefficient, row in zip(normal, supplied)) == 0 for column in range(6))
    after = {name: identity(SOURCE / name) for name in before}
    passed = match and physical_derivatives and normal_annihilation and before == after
    receipt = {
        "schema": "computable_cutoff_chart_replay_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": passed,
        "exit_code": result.returncode, "source_pins_before": before,
        "source_pins_after": after, "source_identities_stable": before == after,
        "published_chart_bytes_reproduced": match,
        "physical_H_derivatives_match": physical_derivatives,
        "published_normal_annihilates_all_six_columns": normal_annihilation,
        "stdout": identity(EVIDENCE / "stdout"), "stderr": identity(EVIDENCE / "stderr"),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Exact physical-coordinate Jacobian, two-sided rational inverse and inverse norm replay. No final cutoff evaluation, derivative-strip/chart upper-bound execution, numerical NO fixture, analytic proof reproving, Lean formalization or general G3 closure."
    }
    (EVIDENCE / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "published_chart_bytes_reproduced", "physical_H_derivatives_match", "published_normal_annihilates_all_six_columns")}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
