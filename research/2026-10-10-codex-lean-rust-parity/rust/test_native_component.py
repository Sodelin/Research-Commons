#!/usr/bin/env python3
"""Meaningful native-component controls: scope, provenance and forgery rejection."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ADAPTER = HERE / "native_component.py"
SAT = b"RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\n"
UNSAT = b"RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLE 0/1 1/1\n"
UNKNOWN = b"RC1 AFFINE 1 2 0\nLT 0/1 -1/1\nLT 1/1 1/1\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    binary = args.binary.resolve()
    fixtures = args.output / "fixtures"
    fixtures.mkdir()
    paths = {}
    for name, raw in [("sat", SAT), ("unsat", UNSAT), ("unknown", UNKNOWN),
                      ("count", b"RC1 COUNT 1/1 1/1 1/1 0/1\n"),
                      ("invalid", b"RC1 AFFINE 1 1 1\nLT 2/2 1/1\n")]:
        path = fixtures / (name + ".rc1")
        path.write_bytes(raw)
        paths[name] = path
    paths["symlink"] = fixtures / "symlink.rc1"
    paths["symlink"].symlink_to(paths["sat"])
    digest = hashlib.sha256(binary.read_bytes()).hexdigest()
    accepted_cert = subprocess.run([str(binary)], input=SAT, capture_output=True, check=True).stdout

    def fake(name, cert=None, exit_code=0, checker_accept=True):
        path = fixtures / name
        if cert is None:
            path.write_bytes(b"bad executable bytes\n")
        else:
            # Literal bytes are embedded as Python repr; no shell interpolation.
            path.write_text("#!/usr/bin/python3\nimport sys\n"
                            "if len(sys.argv)>1:\n"
                            f"    sys.stdout.buffer.write({b'RC1 CHECK ACCEPT\n' if checker_accept else b'RC1 CHECK REJECT\n'!r})\n"
                            f"    sys.exit({0 if checker_accept else 1})\n"
                            f"sys.stdout.buffer.write({cert!r})\nsys.exit({exit_code})\n")
        path.chmod(0o700)
        return path

    fake_launch = fake("cannot-launch")
    fake_exit = fake("post-start-failure", b"", 7)
    fake_status = fake("sat-wrong-exit", accepted_cert, 2)
    fake_witness = fake("forged-witness", accepted_cert.replace(b"WITNESS 1 1/2", b"WITNESS 1 0/1"))
    fake_other = fake("certificate-other-request", accepted_cert)
    fake_reject = fake("native-checker-rejects", accepted_cert, checker_accept=False)
    cases = [
        ("sat_observed_identity", "sat", binary, [], "MATRIX_WITNESS", 0, True, True, True),
        ("sat_expected_pin", "sat", binary, ["--expected-binary-sha256", digest], "MATRIX_WITNESS", 0, True, True, True),
        ("unsat", "unsat", binary, [], "MATRIX_EXCLUSION", 0, True, True, True),
        ("unknown", "unknown", binary, [], "UNKNOWN", 2, True, False, False),
        ("count_refused", "count", binary, [], "REFUSED_REQUEST", 1, False, False, False),
        ("malformed_refused", "invalid", binary, [], "REFUSED_REQUEST", 1, False, False, False),
        ("symlink_refused", "symlink", binary, [], "REFUSED_REQUEST", 1, False, False, False),
        ("pin_mismatch", "sat", binary, ["--expected-binary-sha256", "0" * 64], "REFUSED_REQUEST", 1, False, False, False),
        ("launch_failure", "sat", fake_launch, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, False, False, False),
        ("post_start_failure", "sat", fake_exit, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("sat_exit2_refused", "sat", fake_status, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("forged_witness", "sat", fake_witness, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True),
        ("other_request", "unsat", fake_other, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("native_check_rejection", "sat", fake_reject, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True),
    ]
    records = []
    for name, input_name, executable, extra, expected, expected_exit, solver, checker, fraction in cases:
        output = args.output / name
        command = [sys.executable, "-B", str(ADAPTER), "--request", str(paths[input_name]),
                   "--output", str(output), "--binary", str(executable), *extra]
        process = subprocess.run(command, capture_output=True, timeout=60, check=False)
        (args.output / (name + ".stdout")).write_bytes(process.stdout)
        (args.output / (name + ".stderr")).write_bytes(process.stderr)
        result = json.loads((output / "RESULT.json").read_text())
        passed = (process.returncode == expected_exit and result["status"] == expected
                  and result["solver_called"] == solver and result["checker_called"] == checker
                  and result["fraction_checker_called"] == fraction
                  and result["source_admission_verified"] is False
                  and result["source_admission"] == "SOURCE_ADMISSION_NOT_ESTABLISHED")
        if name == "sat_observed_identity":
            passed &= result["binary_pin_verification"] == "NOT_REQUESTED_OBSERVED_HASH_ONLY"
        if name == "sat_expected_pin":
            passed &= result["binary_pin_verification"] == "EXPECTED_PIN_MATCHED"
        records.append({"id": name, "pass": bool(passed), "expected_status": expected,
                        "actual_status": result["status"], "command": command,
                        "exit_code": process.returncode, "solver_called": result["solver_called"],
                        "checker_called": result["checker_called"], "fraction_checker_called": result["fraction_checker_called"]})
    # Reusing a component output cannot overwrite an earlier certificate/result.
    preserved = args.output / "sat_expected_pin"
    before = (preserved / "RESULT.json").read_bytes()
    process = subprocess.run([sys.executable, "-B", str(ADAPTER), "--request", str(paths["unsat"]),
                              "--output", str(preserved), "--binary", str(binary)],
                             capture_output=True, timeout=10, check=False)
    records.append({"id": "fresh_output_preservation", "pass": process.returncode == 1
                    and (preserved / "RESULT.json").read_bytes() == before})
    summary = {"schema": "native_affine_component_controls_v1", "status": "PASS" if all(r["pass"] for r in records) else "FAILED",
               "cases": records, "case_count": len(records), "binary_sha256": digest,
               "adapter_sha256": hashlib.sha256(ADAPTER.read_bytes()).hexdigest(),
               "scope": "Authored bounded execution, identity and certificate-forgery controls. No biological source admission."}
    (args.output / "TEST-RESULT.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": summary["status"], "cases": len(records),
                      "failures": [r["id"] for r in records if not r["pass"]]}))
    raise SystemExit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
