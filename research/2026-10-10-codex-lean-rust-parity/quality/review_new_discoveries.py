#!/usr/bin/env python3
"""Replay three published packets' exact arithmetic in isolated copies."""
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
EVIDENCE = PACKET / "quality/evidence/research-replay-1"
SCRATCH = Path("/workspace/scratch/codex-research-replay-1")
KILLING = "research/2026-10-10-dot-g3-fair-head-killing-1111z"
EXTRACTION = "research/2026-10-10-dot-g3-effective-fair-head-extraction-1122z"
INVERSE = "research/2026-10-10-dot-g4-sign-free-inverse-estimate-1116z"
GROUPS = {
    "killing": (KILLING, ["check_killing_normal.py", "normal_certificate.json"]),
    "valuation": (KILLING + "/rational-zero-level-supplement",
                  ["check_valuation_independence.py"]),
    "extraction": (EXTRACTION, ["check_exposure.py",
                    "independent_exposure_multiplication.py", "exposure-certificate.json"]),
    "inverse_primary": (INVERSE + "/primary", ["check.py", "RESULT.json"]),
    "inverse_independent": (INVERSE + "/independent",
                            ["check_inverse.py", "RESULT.json", "EXACT-MATRICES.json"]),
}
SCRIPTS = {
    "killing": ["check_killing_normal.py"],
    "valuation": ["check_valuation_independence.py"],
    "extraction": ["check_exposure.py", "independent_exposure_multiplication.py"],
    "inverse_primary": ["check.py"],
    "inverse_independent": ["check_inverse.py"],
}


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (1024 * 1024**2, 1024 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (60, 60))


def execute_group(group):
    executions = []
    for name in SCRIPTS[group]:
        command = [sys.executable, "-I", "-B", str(SCRATCH / group / name)]
        try:
            result = subprocess.run(command, cwd=SCRATCH / group,
                                    capture_output=True, timeout=90, preexec_fn=limits)
            stdout, stderr, code = result.stdout, result.stderr, result.returncode
        except subprocess.TimeoutExpired as error:
            stdout, stderr, code = error.stdout or b"", error.stderr or b"", None
        stem = group + "-" + name.removesuffix(".py")
        for suffix, data in (("stdout", stdout), ("stderr", stderr)):
            (EVIDENCE / (stem + "." + suffix)).write_bytes(data)
        executions.append({"group": group, "script": name, "exit_code": code,
                           "pass": code == 0,
                           "stdout": identity(EVIDENCE / (stem + ".stdout")),
                           "stderr": identity(EVIDENCE / (stem + ".stderr"))})
        if code != 0:
            break
    return executions


def load(path):
    return json.loads(path.read_text())


def main():
    EVIDENCE.mkdir(parents=True, exist_ok=False)
    SCRATCH.mkdir(parents=True, exist_ok=False)
    inputs = [f"{directory}/{name}" for directory, names in GROUPS.values()
              for name in names]
    before = {name: identity(COMMONS / name) for name in inputs}
    for group, (directory, names) in GROUPS.items():
        (SCRATCH / group).mkdir()
        for name in names:
            # Producer scripts must create their own output, not read a copied receipt.
            if name.endswith(".py"):
                shutil.copyfile(COMMONS / directory / name, SCRATCH / group / name)
    executions = [row for group in GROUPS for row in execute_group(group)]
    checks = {}
    if len(executions) == 6 and all(row["pass"] for row in executions):
        normal = load(SCRATCH / "killing/killing-normal-certificate.json")
        published = load(COMMONS / KILLING / "normal_certificate.json")
        checks["killing_normal_and_quotient_match_published"] = (
            normal["Lambda"] == published["Lambda"] and
            normal["normal"] == published["c"] and
            normal["Q_ascending"] == published["Q"])
        checks["exposure_certificate_bytes_match_published"] = (
            identity(SCRATCH / "extraction/exposure-certificate.json") ==
            before[EXTRACTION + "/exposure-certificate.json"])
        actual = load(SCRATCH / "inverse_primary/RESULT.json")
        expected = load(COMMONS / INVERSE / "primary/RESULT.json")
        actual.pop("elapsed_seconds")
        expected.pop("elapsed_seconds")
        checks["five_inverse_fixtures_match_published_except_elapsed_time"] = actual == expected
        checks["independent_inverse_result_bytes_match_published"] = (
            identity(SCRATCH / "inverse_independent/RESULT.json") ==
            before[INVERSE + "/independent/RESULT.json"])
        checks["independent_exact_matrices_bytes_match_published"] = (
            identity(SCRATCH / "inverse_independent/EXACT-MATRICES.json") ==
            before[INVERSE + "/independent/EXACT-MATRICES.json"])
    outputs = {}
    for group in GROUPS:
        (EVIDENCE / group).mkdir()
        for path in sorted((SCRATCH / group).glob("*.json")):
            destination = EVIDENCE / group / path.name
            shutil.copyfile(path, destination)
            outputs[f"{group}/{path.name}"] = identity(destination)
    after = {name: identity(COMMONS / name) for name in inputs}
    passed = (len(executions) == 6 and all(row["pass"] for row in executions)
              and len(checks) == 5 and all(checks.values()) and before == after)
    receipt = {
        "schema": "new_dot_exact_arithmetic_replay_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "source_pins_before": before, "source_pins_after": after,
        "source_identities_stable": before == after,
        "executions": executions, "checks": checks, "outputs": outputs,
        "pass": passed,
        "verified": ["Rational killing normal, exact positive quotient and Sturm check",
                     "Seven-prime valuation determinant and rational zero-level obstruction algebra",
                     "Sparse exposure polynomial, positive coefficients and independent multiplication",
                     "Actual finite count-kernel inverse sign counterexample with independent exact matrices"],
        "not_verified": ["All-length analytic extraction and weak-collar proofs",
                         "Numerical killing cutoff or specified rational NO witness",
                         "General opaque-forest inverse norm theorem",
                         "G3 or G4 completeness", "Lean formalization"]
    }
    (EVIDENCE / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": passed, "scripts": len(executions), "checks": checks}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
