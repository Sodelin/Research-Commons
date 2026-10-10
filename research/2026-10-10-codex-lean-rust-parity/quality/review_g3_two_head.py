#!/usr/bin/env python3
"""Replay the published exact algebraic checks, without changing source bytes."""
import hashlib
import json
import resource
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
COMMONS = PACKET.parents[1]
SOURCE = COMMONS / "research/2026-10-10-dot-g3-two-head-residue-attainment-1100z"
EVIDENCE = PACKET / "quality/evidence/g3-two-head-replay-1"
SCRATCH = Path("/workspace/scratch/codex-g3-two-head-replay-1")
INPUTS = ("check_exact.py", "independent_hessian_review.py",
          "independent_sturm_review.py", "compact-certificate.txt",
          "exact-polynomials.json")


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024 * 1024**2, 1024 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (60, 60))


def main():
    # Each attempt is immutable; use a new evidence/scratch name for a rerun.
    EVIDENCE.mkdir(parents=True, exist_ok=False)
    SCRATCH.mkdir(parents=True, exist_ok=False)
    before = {name: identity(SOURCE / name) for name in INPUTS}
    for name in INPUTS:
        shutil.copyfile(SOURCE / name, SCRATCH / name)
    executions = []
    for name, arguments in (("check_exact.py", ["--full-sturm"]),
                            ("independent_hessian_review.py", []),
                            ("independent_sturm_review.py", [])):
        command = [sys.executable, "-I", "-B", str(SCRATCH / name), *arguments]
        try:
            result = subprocess.run(command, cwd=SCRATCH, capture_output=True,
                                    timeout=90, preexec_fn=limits)
            stdout, stderr, code = result.stdout, result.stderr, result.returncode
        except subprocess.TimeoutExpired as error:
            stdout, stderr, code = error.stdout or b"", error.stderr or b"", None
        stem = name.removesuffix(".py")
        (EVIDENCE / (stem + ".stdout")).write_bytes(stdout)
        (EVIDENCE / (stem + ".stderr")).write_bytes(stderr)
        executions.append({"script": name, "arguments": arguments,
                           "exit_code": code, "pass": code == 0,
                           "stdout": identity(EVIDENCE / (stem + ".stdout")),
                           "stderr": identity(EVIDENCE / (stem + ".stderr"))})
        if code != 0:
            break
    after = {name: identity(SOURCE / name) for name in INPUTS}
    polynomial_match = (identity(SCRATCH / "exact-polynomials.json") ==
                        before["exact-polynomials.json"])
    outputs = {}
    for name in ("exact-polynomials.json", "full-sturm.json", "exact-basis.txt"):
        if (SCRATCH / name).is_file():
            shutil.copyfile(SCRATCH / name, EVIDENCE / name)
            outputs[name] = identity(EVIDENCE / name)
    passed = (len(executions) == 3 and all(row["pass"] for row in executions)
              and before == after and polynomial_match)
    receipt = {
        "schema": "g3_two_head_exact_arithmetic_replay_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "source_packet": str(SOURCE.relative_to(COMMONS)),
        "source_pins_before": before, "source_pins_after": after,
        "source_identities_stable": before == after,
        "published_polynomial_bytes_reproduced": polynomial_match,
        "executions": executions, "outputs": outputs, "pass": passed,
        "verified": "Fresh exact rank/Hessian and Sturm certificate execution; independent rational long-division verification of every supplied Sturm step.",
        "not_verified": ["Analytic source-interior provider theorem",
                         "Calibrated original-menu compiler theorem",
                         "Extracted finite source witness",
                         "Lean formalization", "General G3 completeness"]
    }
    (EVIDENCE / "RECEIPT.json").write_text(json.dumps(receipt, indent=2,
                                                       sort_keys=True) + "\n")
    print(json.dumps({"pass": passed, "scripts": len(executions),
                      "published_polynomial_bytes_reproduced": polynomial_match}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
