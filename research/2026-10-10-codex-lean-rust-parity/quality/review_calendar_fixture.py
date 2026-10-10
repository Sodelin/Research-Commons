#!/usr/bin/env python3
"""Bind checked Lean evaluations to the earlier actual Rust application outputs."""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, identity, read


def canonical_payload(result):
    variables = result["variables"]
    rows, seen = [], set()
    for row in result["rows"]:
        key = json.dumps(row["view"], sort_keys=True, separators=(",", ":"))
        if key in seen:
            raise ValueError("Duplicate full view")
        seen.add(key)
        coefficients, exponents = [], set()
        for exponent, wire in row["coefficients"]:
            if len(exponent) != len(variables) or not all(type(x) is int and x >= 0 for x in exponent):
                raise ValueError("Invalid exponent vector")
            power = tuple(exponent)
            if power in exponents:
                raise ValueError("Duplicate monomial")
            exponents.add(power)
            value = Fraction(wire)
            if not value or wire != f"{value.numerator}/{value.denominator}":
                raise ValueError("Noncanonical coefficient")
            coefficients.append((exponent, wire))
        rows.append((key, {"view": row["view"], "coefficients": sorted(coefficients)}))
    value = {"request": result["request"], "variables": variables,
             "rows": [row for _, row in sorted(rows)]}
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def main():
    proof = read(PACKET / "quality/CALENDAR-FIXTURE-PROOF-REVIEW.json")
    execution = read(PACKET / "quality/CALENDAR-LEAN-EXECUTION-REVIEW.json")
    result = read(PACKET / "lean/ORIGINAL-CALENDAR-LEAN-EVALUATOR-RESULT.json")
    lean_dir = PACKET / "lean" / result["evidence"]
    independent_path = PACKET / "rust/evidence/calendar-original-lean-rust-review-1/RECEIPT.json"
    independent = read(independent_path)
    rust_path = PACKET / "rust/evidence/calendar-completed-application-1/RECEIPT.json"
    rust = read(rust_path)
    cases, errors = [], []
    for case in independent["cases"]:
        name = case["fixture"]
        lean_path = lean_dir / (name + ".lean.stdout")
        table_path = rust_path.parent / "cases" / name / "component/TABLE.json"
        lean, native = read(lean_path), read(table_path)["word_result"]
        left, right = canonical_payload(lean), canonical_payload(native)
        valid = (left == right and case["status"] == "PASS"
                 and case["actual_complete_coefficient_maps_equal"]
                 and identity(lean_path)["sha256"] == case["Lean_stdout_sha256"]
                 and identity(table_path)["sha256"] == case["rust_original_table_sha256"]
                 and case["saved_Rust_native_execution_reused"] and not case["Lean_execution_by_this_reviewer"])
        origin = PACKET / "design/evidence/calendar-original-input-freeze-1" / (name + ".request.json")
        valid &= identity(origin)["sha256"] == case["request_sha256"]
        cases.append({"fixture": name, "pass": valid, "full_views": len(lean["rows"]),
                      "terms": sum(len(row["coefficients"]) for row in lean["rows"]),
                      "canonical_mathematical_payload_sha256": hashlib.sha256(left).hexdigest(),
                      "literal_witness_validation": case["review"]})
        if not valid:
            errors.append(name)
    checks = {
        "root_proof_and_actual_execution": proof["pass"] and execution["pass"],
        "same_actual_Lean_receipt": independent["actual_Lean_evaluator_execution_receipt_sha256"]
            == result["driver_receipt_sha256"] == execution["comparison"]["sha256"],
        "same_saved_Rust_execution": identity(rust_path)["sha256"]
            == independent["saved_Rust_application_receipt_sha256"],
        "independent_review_complete": independent["status"] == "PASS" and independent["cases_passed"] == 3
            and independent["full_view_rows"] == 38 and independent["terms"] == 66
            and independent["exact_context_source_count"] == 200 and independent["owned_imported_artifacts_rehashed"] == 209
            and independent["identities_before"] == independent["identities_after"],
        "whole_canonical_tables": len(cases) == 3 and sum(c["full_views"] for c in cases) == 38
            and sum(c["terms"] for c in cases) == 66,
        "no_unneeded_native_rerun": independent["native_or_Lean_processes_started_by_this_reviewer"] == 0
            and not independent["old117_or_broader_suites_rerun"],
        "scope_preserved": not independent["specific_physical_calendar_phase_instances_checked"]
            and not independent["general_native_calendar_refinement_claim"]
            and not independent["source_admission_verified"] and not independent["Lean_standalone_ELF_claim"],
    }
    errors.extend(k for k, passed in checks.items() if not passed)
    answer = {"schema": "completed_literal_word_actual_Lean_saved_Rust_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "cases": cases, "independent_review": identity(independent_path),
        "Lean_execution_review": identity(PACKET / "quality/CALENDAR-LEAN-EXECUTION-REVIEW.json"),
        "Rust_application_receipt": identity(rust_path), "reviewer": identity(Path(__file__)),
        "scope": "Three original completed literal-word Lean evaluations match earlier actual Rust calendar/completion outputs at all38 ordered full views and66 terms. Canonical mathematical table payloads agree byte-for-byte after explicit normalization; whole producer envelopes and witness choices are not asserted identical. Witnesses are independently checked. Specific finite calendar phase/physical composition, generic parser/encoder refinement and source admission remain separate. No solver rerun here.",
        "source_admission_verified": False, "master_complete": False}
    (PACKET / "quality/CALENDAR-FIXTURE-REVIEW.json").write_text(json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "cases": len(cases), "views": 38, "terms": 66}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
