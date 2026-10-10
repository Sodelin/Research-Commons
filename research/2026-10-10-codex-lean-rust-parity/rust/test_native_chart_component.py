#!/usr/bin/env python3
"""Bounded CHART adapter controls, including independent compiler rejection."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ADAPTER = HERE / "native_chart_component.py"
COMMON = HERE / "native_component.py"
FIXTURES = HERE.parent / "design/chart-fixtures"
SCHEMA = "rust_natural_cell_component_result_v1"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    binary = args.binary.resolve()
    fixtures = args.output / "fixtures"
    fixtures.mkdir()
    fixture_names = {
        "sat": "chart_two_tip_typed_cells.req",
        "parallel": "chart_parallel_original_occurrences.req",
        "unsat": "chart_shared_edge_contradiction.req",
        "unknown": "chart_projection_limit.req",
        "invalid": "chart_bad_root_lsa.req",
    }
    paths, fixture_sources = {}, []
    for name, source_name in fixture_names.items():
        source = FIXTURES / source_name
        path = fixtures / (name + ".rc1")
        path.write_bytes(source.read_bytes())
        paths[name] = path
        fixture_sources.append({"id": name, "source": str(source), "sha256": digest(source)})
    paths["affine"] = fixtures / "affine.rc1"
    paths["affine"].write_bytes(b"RC1 AFFINE 1 1 1\nLE 0/1 1/1\n")
    accepted = subprocess.run([str(binary)], input=paths["sat"].read_bytes(),
                              capture_output=True, check=True).stdout

    def forged_witness(raw):
        lines = raw.splitlines(keepends=True)
        index = next(i for i, line in enumerate(lines) if line.startswith(b"WITNESS "))
        fields = lines[index].rstrip(b"\n").split(b" ")
        fields[2] = b"0/1"  # Violates the independently supplied root-age equality.
        lines[index] = b" ".join(fields) + b"\n"
        return b"".join(lines)

    def forged_matrix(raw):
        lines = raw.splitlines(keepends=True)
        index = next(i for i, line in enumerate(lines) if line.startswith(b"MATRIX ")) + 1
        fields = lines[index].rstrip(b"\n").split(b" ")
        fields[1] = b"1/1"  # Alter an emitted row while retaining the request and witness.
        lines[index] = b" ".join(fields) + b"\n"
        return b"".join(lines)

    def fake(name, certificate=None, exit_code=0, checker_accept=True):
        path = fixtures / name
        if certificate is None:
            path.write_bytes(b"not an executable\n")
        else:
            checker_bytes = b"RC1 CHECK ACCEPT\n" if checker_accept else b"RC1 CHECK REJECT\n"
            path.write_text("#!/usr/bin/python3\nimport sys\n"
                            "if len(sys.argv)>1:\n"
                            f"    sys.stdout.buffer.write({checker_bytes!r})\n"
                            f"    sys.exit({0 if checker_accept else 1})\n"
                            f"sys.stdout.buffer.write({certificate!r})\nsys.exit({exit_code})\n")
        path.chmod(0o700)
        return path

    bad_launch = fake("cannot-launch")
    bad_exit = fake("post-start-failure", b"", 7)
    bad_pair = fake("wrong-producer-exit", accepted, 2)
    bad_witness = fake("forged-witness", forged_witness(accepted))
    bad_matrix = fake("forged-matrix", forged_matrix(accepted))
    bad_gate = fake("promoted-source-gate", accepted.replace(
        b"GATE SOURCE_ADMISSION_NOT_ESTABLISHED\n", b"GATE SOURCE_ADMISSION_ESTABLISHED\n"))
    bad_other = fake("other-chart", accepted)
    bad_checker = fake("checker-rejects", accepted, checker_accept=False)
    cases = [
        ("ordinary_observed_identity", "sat", binary, [], "MATRIX_WITNESS", 0, True, True, True),
        ("parallel_expected_pin", "parallel", binary, ["--expected-binary-sha256", digest(binary)],
         "MATRIX_WITNESS", 0, True, True, True),
        ("shared_edge_exclusion", "unsat", binary, [], "MATRIX_EXCLUSION", 0, True, True, True),
        ("projection_unknown", "unknown", binary, [], "UNKNOWN", 2, True, False, False),
        ("non_lsa_graph_refusal", "invalid", binary, [], "REFUSED_REQUEST", 1, False, False, False),
        ("affine_operation_refusal", "affine", binary, [], "REFUSED_REQUEST", 1, False, False, False),
        ("binary_pin_refusal", "sat", binary, ["--expected-binary-sha256", "0" * 64],
         "REFUSED_REQUEST", 1, False, False, False),
        ("launch_failure", "sat", bad_launch, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, False, False, False),
        ("post_start_failure", "sat", bad_exit, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("status_exit_mismatch", "sat", bad_pair, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("forged_witness", "sat", bad_witness, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True),
        ("forged_matrix", "sat", bad_matrix, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True),
        ("source_gate_promotion", "sat", bad_gate, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("other_original_chart", "parallel", bad_other, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, False, False),
        ("native_checker_rejection", "sat", bad_checker, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True),
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
        passed = (process.returncode == expected_exit and result["schema"] == SCHEMA
                  and result["status"] == expected and result["solver_called"] == solver
                  and result["checker_called"] == checker and result["fraction_checker_called"] == fraction
                  and result["source_admission_verified"] is False
                  and result["source_witness_certified"] is False
                  and result["unrestricted_exclusion_certified"] is False
                  and result["source_admission"] == "SOURCE_ADMISSION_NOT_ESTABLISHED"
                  and result["certificate_checked"] == (expected in ("MATRIX_WITNESS", "MATRIX_EXCLUSION")))
        if name == "ordinary_observed_identity":
            passed &= result["binary_pin_verification"] == "NOT_REQUESTED_OBSERVED_HASH_ONLY"
        if name == "parallel_expected_pin":
            passed &= result["binary_pin_verification"] == "EXPECTED_PIN_MATCHED"
        if expected in ("MATRIX_WITNESS", "MATRIX_EXCLUSION", "UNKNOWN"):
            identities = json.loads((output / "SOURCE-IDENTITIES.json").read_text())
            helper_pins = identities["fraction_checker_sources"]
            passed &= len(helper_pins) == 2 and all(
                digest(HERE.parents[2] / entry["path"]) == entry["sha256"] for entry in helper_pins)
            passed &= digest(output / "component/native/certificate_check.py") == result["fraction_checker_staged_sha256"]
        records.append({"id": name, "pass": bool(passed), "expected_status": expected,
                        "actual_status": result["status"], "exit_code": process.returncode,
                        "command": command, "solver_called": result["solver_called"],
                        "checker_called": result["checker_called"], "fraction_checker_called": result["fraction_checker_called"]})

    preserved = args.output / "parallel_expected_pin"
    before = (preserved / "RESULT.json").read_bytes()
    process = subprocess.run([sys.executable, "-B", str(ADAPTER), "--request", str(paths["unsat"]),
                              "--output", str(preserved), "--binary", str(binary)],
                             capture_output=True, timeout=10, check=False)
    records.append({"id": "fresh_output_preservation", "pass": process.returncode == 1
                    and (preserved / "RESULT.json").read_bytes() == before})
    summary = {"schema": "native_natural_cell_component_controls_v1",
               "status": "PASS" if all(r["pass"] for r in records) else "FAILED",
               "case_count": len(records), "cases": records, "fixture_sources": fixture_sources,
               "binary_sha256": digest(binary), "adapter_sha256": digest(ADAPTER),
               "common_adapter_sha256": digest(COMMON),
               "scope": "Literal shared-bank chart compilation, exact certificates and bounded provenance. Source admission remains false."}
    (args.output / "TEST-RESULT.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": summary["status"], "cases": len(records),
                      "failures": [r["id"] for r in records if not r["pass"]]}))
    raise SystemExit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
