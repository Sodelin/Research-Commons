#!/usr/bin/env python3
"""Check the saved population proof and three-way execution evidence."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def canonical(data):
    # List order is irrelevant for finite rows; every field and multiplicity stays.
    result = {key: data[key] for key in ("schema", "fixture", "context")}
    for key in ("rows", "unordered"):
        result[key] = sorted(json.dumps(row, sort_keys=True) for row in data[key])
    return result


def main():
    result_path = PACKET / "lean/POPULATION-FIXTURE-RESULT.json"
    result = read(result_path)
    certificate = read(PACKET / "lean/POPULATION-FIXTURE-CERTIFICATE.json")
    evidence = PACKET / "lean" / result["evidence"]
    target = read(evidence / "targets/extraction_original-population-fixture/RESULT.json")
    audit_path = Path(target["audit_receipt"]["audit_output"])
    audit_relative = audit_path.relative_to(Path(result["actual_run"]))
    audit = read(evidence / audit_relative)
    errors, preserved = [], []
    for pin in result["preserved_files"]:
        observed = identity(evidence / pin["path"])
        passed = observed == {key: pin[key] for key in ("bytes", "sha256")}
        preserved.append({"path": pin["path"], **observed, "pass": passed})
        if not passed:
            errors.append("Preserved artifact: " + pin["path"])
    final = result["final_receipt"]
    conditions = {
        "target_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "complete_ownership": len(audit["selected_modules"]) == target["closure_modules"] == 108 and not audit["missing_modules"],
        "counts_match": audit["declaration_count"] == target["declarations"] == 3741 and audit["theorem_declaration_count"] == target["theorems"] == 2052,
        "no_owned_or_nonstandard_axioms": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"],
        "fresh_aggregate_and_audit": all(target[name]["status"] == "PASS_FRESH_KERNEL_CHECK" and target[name]["exit_code"] == 0 and target[name]["source_and_imports_stable"] for name in ("aggregate_receipt", "audit_receipt")),
        "trust_zero_and_stable_runtime": final["trust_level"] == 0 and final["kernel_checking"] and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "freshness_disclosed": final["counts"] == {"cache_reuse": 94, "fresh_components": 14} and not final["fresh_all_sources_claimed"],
    }
    sources = {}
    for module, expected in (
        ("G7EffectiveCoefficientSupport", certificate["proof_sources"]["arbitrary_fuel_support"]),
        ("G7EncodedMergerSupport", certificate["proof_sources"]["canonical_encoding_image"]),
        ("G7OriginalPopulationFixture", certificate["fixture_source_sha256"]),
    ):
        source = PACKET / "reuse/sources" / (module + ".lean")
        receipt = next(row for row in target["component_receipts"] if row["module"] == module)
        observed = identity(source)
        passed = observed["sha256"] == expected == receipt["source_sha256"] and receipt["status"] == "PASS_FRESH_KERNEL_CHECK" and receipt["source_and_imports_stable"]
        sources[module] = {**observed, "pass": passed}
        if not passed:
            errors.append("Current proof/fixture source: " + module)
    review_path = Path(certificate["independent_review"]["receipt_path"])
    review = read(review_path)
    conditions["review_certificate_identity"] = identity(review_path)["sha256"] == certificate["independent_review"]["receipt_sha256"]
    conditions["eight_actual_comparisons"] = review["pass"] and review["cases_passed"] == review["cases_total"] == 8 and review["languages_executed"] == ["rust", "lean"]
    conditions["execution_modes_disclosed"] = review["execution_modes"] == {"lean": "compiled_lean_evaluator_not_standalone_elf", "rust": "standalone_executable"}
    conditions["inputs_and_binaries_stable"] = review["observed_input_pins_before"] == review["observed_input_pins_after"] and review["binary_pins_before"] == review["binary_pins_after"]
    cases = []
    for case in review["cases"]:
        name = case["fixture"]
        expected = read(review_path.parent / (name + ".expected.json"))
        compared = []
        for language in ("lean", "rust"):
            output = review_path.parent / (name + "." + language + ".stdout")
            process = case["process_runs"][language]
            passed = (process["process_started"] and process["exit_code"] == 0 and not process["timed_out"]
                      and identity(output)["sha256"] == process["stdout_sha256"]
                      and canonical(read(output)) == canonical(expected))
            compared.append(passed)
        passed = all(compared) and case["pass"] and not case["errors"]
        cases.append({"fixture": name, "pass": passed,
                      "literal_rows": len(expected["rows"]), "unordered_rows": len(expected["unordered"])})
        if not passed:
            errors.append("Captured exact coefficient comparison: " + name)
    errors += [key for key, passed in conditions.items() if not passed]
    receipt = {
        "schema": "source_population_static_quality_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "conditions": conditions,
        "preserved_artifacts": preserved, "current_sources": sources, "cases": cases,
        "result": identity(result_path), "comparison_receipt": identity(review_path),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Independent saved-artifact identity and captured coefficient-table comparison. Uses the recorded kernel audit and spectral expected tables; no new compiler or oracle execution, universal refinement, source admission or empirical claim."
    }
    (PACKET / "quality/SOURCE-POPULATION-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors,
                      "preserved_artifacts": len(preserved), "cases": len(cases)}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
