#!/usr/bin/env python3
"""Production LAW adapter controls, including balanced false-law rejection."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ADAPTER = HERE / "native_law_component.py"
FIXTURES = HERE.parent / "design/law-fixtures"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    binary = args.binary.resolve()
    fixtures = args.output / "fixtures"
    fixtures.mkdir()
    names = {"table": "law_three_tip.req", "parallel": "law_parallel_four_independent.req",
             "unknown": "law_history_limit_zero.req", "invalid": "law_bad_parent_alias.req"}
    paths, sources = {}, []
    for name, source_name in names.items():
        source = FIXTURES / source_name
        path = fixtures / (name + ".rc1")
        path.write_bytes(source.read_bytes())
        paths[name] = path
        sources.append({"id": name, "source": str(source), "sha256": digest(source)})
    paths["wrong_operation"] = fixtures / "wrong-operation.rc1"
    paths["wrong_operation"].write_bytes(b"RC1 COUNT 1/1 1/1 1/1 0/1\n")
    table = subprocess.run([str(binary)], input=paths["table"].read_bytes(), capture_output=True, check=True).stdout
    # Shift equal and opposite mass between discordant rooted outcomes. The
    # formal total and unrooted pushforward stay correct; only the independent
    # inherited full-law comparison can reject this forged law.
    forged = table.replace(b"TERM 1/3 ", b"TERM 1/2 ", 1)
    forged = forged.replace(b"TERM 1/3 ", b"TERM 1/6 ", 1)
    assert forged != table

    def fake(name, raw=None, code=0, checker_accept=True):
        path = fixtures / name
        if raw is None:
            path.write_bytes(b"cannot execute these bytes\n")
        else:
            checker = b"RC1 CHECK ACCEPT\n" if checker_accept else b"RC1 CHECK REJECT\n"
            path.write_text("#!/usr/bin/python3\nimport sys\n"
                            "if len(sys.argv)>1:\n"
                            f"    sys.stdout.buffer.write({checker!r})\n"
                            f"    sys.exit({0 if checker_accept else 1})\n"
                            f"sys.stdout.buffer.write({raw!r})\nsys.exit({code})\n")
        path.chmod(0o700)
        return path

    failures = [
        ("launch_failure", fake("not-executable"), "table", False, False, False),
        ("post_start_failure", fake("crashes", b"", 7), "table", True, False, False),
        ("table_exit2", fake("status-exit-mismatch", table, 2), "table", True, False, False),
        ("balanced_forged_law", fake("balanced-forgery", forged), "table", True, True, True),
        ("promoted_source_gate", fake("false-admission", table.replace(
            b"GATE SOURCE_ADMISSION_NOT_ESTABLISHED", b"GATE SOURCE_ADMISSION_ESTABLISHED")), "table", True, False, False),
        ("other_source_request", fake("other-request", table), "parallel", True, False, False),
        ("native_replay_rejects", fake("replay-reject", table, checker_accept=False), "table", True, True, True),
    ]
    cases = [
        ("table_observed_identity", binary, "table", [], "FORMAL_GENEALOGY_TABLE", 0, True, True, True),
        ("parallel_pinned_identity", binary, "parallel", ["--expected-binary-sha256", digest(binary)],
         "FORMAL_GENEALOGY_TABLE", 0, True, True, True),
        ("history_unknown", binary, "unknown", [], "UNKNOWN", 2, True, False, False),
        ("invalid_structure", binary, "invalid", [], "REFUSED_REQUEST", 1, False, False, False),
        ("wrong_operation", binary, "wrong_operation", [], "REFUSED_REQUEST", 1, False, False, False),
        ("binary_pin_mismatch", binary, "table", ["--expected-binary-sha256", "0"*64],
         "REFUSED_REQUEST", 1, False, False, False),
    ]
    cases += [(name, executable, request, [], "RESOURCE_OR_EXECUTION_FAILURE", 1, solver, native, reference)
              for name, executable, request, solver, native, reference in failures]
    records = []
    for name, executable, input_name, extra, expected, exit_code, solver, native, reference in cases:
        output = args.output / name
        command = [sys.executable, "-B", str(ADAPTER), "--request", str(paths[input_name]),
                   "--output", str(output), "--binary", str(executable), *extra]
        process = subprocess.run(command, capture_output=True, timeout=70, check=False)
        (args.output / (name + ".stdout")).write_bytes(process.stdout)
        (args.output / (name + ".stderr")).write_bytes(process.stderr)
        result = json.loads((output / "RESULT.json").read_text())
        passed = (process.returncode == exit_code and result["schema"] == "rust_genealogy_law_component_result_v1"
                  and result["status"] == expected and result["solver_called"] == solver
                  and result["checker_called"] == native and result["reference_checker_called"] == reference
                  and result["fraction_checker_called"] == reference
                  and result["native_checker_algorithm_independent"] is False
                  and result["certificate_checked"] is False
                  and result["source_admission_verified"] is False
                  and result["physical_survival_image_verified"] is False
                  and result["statistical_confidence_verified"] is False
                  and result["source_admission"] == "SOURCE_ADMISSION_NOT_ESTABLISHED"
                  and result["formal_table_checked"] == (expected == "FORMAL_GENEALOGY_TABLE"))
        if expected == "FORMAL_GENEALOGY_TABLE":
            passed &= result["inherited_baseline_all_coefficients_checked"] is True
            runtime = result["scientific_runtime_observed"]
            passed &= runtime["sympy"]["version"] == "1.14.0" and runtime["mpmath"]["version"] == "1.3.0"
            passed &= digest(output / "component/native/law_check.py") == result["staged_law_checker_sha256"]
            identities = json.loads((output / "SOURCE-IDENTITIES.json").read_text())
            passed &= len(identities["law_checker_provider_sources"]) == 4
        if name == "table_observed_identity":
            passed &= result["binary_pin_verification"] == "NOT_REQUESTED_OBSERVED_HASH_ONLY"
        if name == "parallel_pinned_identity":
            passed &= result["binary_pin_verification"] == "EXPECTED_PIN_MATCHED"
        if name == "balanced_forged_law":
            rejection = (output / "component/reference-checker.stdout").read_text()
            passed &= "differ from pinned inherited source compiler" in rejection
        records.append({"id": name, "pass": bool(passed), "expected_status": expected,
                        "actual_status": result["status"], "exit_code": process.returncode,
                        "solver_called": result["solver_called"], "checker_called": result["checker_called"],
                        "reference_checker_called": result["reference_checker_called"], "command": command})
    preserved = args.output / "parallel_pinned_identity"
    before = (preserved / "RESULT.json").read_bytes()
    process = subprocess.run([sys.executable, "-B", str(ADAPTER), "--request", str(paths["table"]),
                              "--output", str(preserved), "--binary", str(binary)],
                             capture_output=True, timeout=10, check=False)
    records.append({"id": "fresh_output_preservation", "pass": process.returncode == 1
                    and (preserved / "RESULT.json").read_bytes() == before})
    summary = {"schema": "native_law_component_controls_v1", "status": "PASS" if all(r["pass"] for r in records) else "FAILED",
               "cases": records, "case_count": len(records), "fixture_sources": sources,
               "adapter_sha256": digest(ADAPTER), "binary_sha256": digest(binary),
               "scope": "Bounded formal joint genealogy tables and captured inherited-coefficient comparison. All scientific admission/confidence flags false."}
    (args.output / "TEST-RESULT.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": summary["status"], "cases": len(records), "failures": [r["id"] for r in records if not r["pass"]]}))
    raise SystemExit(0 if summary["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
