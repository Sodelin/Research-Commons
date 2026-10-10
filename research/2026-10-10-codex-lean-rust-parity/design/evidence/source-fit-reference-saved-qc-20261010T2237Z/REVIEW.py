"""Independent saved-artifact review; stdlib only, no producer/provider launches."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

HERE = Path(__file__).resolve().parent
PACKET = HERE.parents[2]
SOURCE = PACKET / "rust/evidence/source-fit-saved-reference-20261010T223418.843872Z"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value, reason):
    if not value:
        raise ValueError(reason)


def read(path):
    return json.loads(path.read_bytes())


def polynomial(row):
    return {tuple(p): Fraction(q) for p, q in row["edge_polynomial"]}


def sum_polynomials(rows):
    total = {}
    for row in rows:
        for p, q in polynomial(row).items():
            total[p] = total.get(p, Fraction(0)) + q
    return {p: q for p, q in total.items() if q}


def evaluate(poly, values):
    total = Fraction(0)
    for p, q in poly.items():
        for exponent, value in zip(p, values, strict=True):
            q *= value ** exponent
        total += q
    return total


def main():
    outer = read(SOURCE / "FINAL-RECEIPT.json")
    review = read(SOURCE / "review/RECEIPT.json")
    manifest = read(SOURCE / "PRESERVATION-MANIFEST.json")
    total_bytes = 0
    for item in manifest["preserved_files"]:
        path = SOURCE / item["relative_path"]
        require(sha(path) == item["sha256"], "preserved SHA mismatch: " + str(path))
        require(path.stat().st_size == item["bytes"], "preserved length mismatch")
        total_bytes += item["bytes"]
    require(outer["review_receipt_sha256"] == sha(SOURCE / "review/RECEIPT.json"), "inner binding")
    for path, digest in outer["pin_rechecks"].items():
        require(sha(Path(path)) == digest, "current source/runtime pin mismatch: " + path)
    require(outer["exit_code"] == 0 and outer["monitor_error"] is None, "outer execution failure")
    require(review["status"] == "PASS" and outer["passed"] == review["passed"] == 14, "not all fourteen")
    require(outer["native_processes_started"] == outer["compiler_processes_started"] == 0, "unexpected producer start")
    require(review["native_processes_started"] == review["lean_compiler_processes_started"] == 0, "unexpected inner start")
    false_flags = ("source_admission_verified", "source_observation_fit_verified", "source_provenance_verified",
        "timed_readout_verified", "universal_native_refinement_verified", "full_solver_verified", "full_code_evaluated",
        "bank_metadata_independently_checked", "provider_work_checked", "resource_exhaustion_verified", "certificate_valid")
    mathematical_flags = ("baseline_called", "independent_all_coefficients_checked",
        "independent_probabilities_checked", "supplied_trace_arithmetic_checked")
    for control in review["controls"]:
        directory = SOURCE / "review" / control["case"]
        require(control["pass"] is True, "control failed")
        require(sha(directory / "REQUEST.json") == control["request_sha256"], "control request binding")
        require(sha(directory / "RESPONSE.json") == control["response_sha256"], "control response binding")
        verification = read(directory / "VERIFICATION.json")
        if control["accepted"]:
            require(verification["result_valid"] is True and verification["status"] == control["status"], "accepted status")
            require(verification["request_sha256"] == control["request_sha256"], "verified request binding")
            require(verification["response_sha256"] == control["response_sha256"], "verified response binding")
            require(all(verification[k] is False for k in false_flags), "scope promotion")
            require(all(verification[k] is (control["status"] == "TABLE") for k in mathematical_flags), "math flag qualification")
        else:
            require(verification["rejected"] is True and verification["error"] == control["error"], "rejection binding")
    rows = terms = 0
    for name in ("hybrid-common-sat", "hybrid-independent-sat", "hybrid-common-permuted"):
        response = read(SOURCE / "review" / name / "RESPONSE.json")
        values = [Fraction(v["value"]) for v in response["bank_result"]["request"]["values"]]
        edge_count = len(response["bank_result"]["request"]["context"]["edges"])
        outcomes = response["mixture"]
        require(sum_polynomials(outcomes) == {(0,) * edge_count: Fraction(1)}, "whole polynomial mass")
        require(sum(Fraction(r["probability"]) for r in outcomes) == 1, "rational mass")
        for row in outcomes:
            require(evaluate(polynomial(row), values[:edge_count]) == Fraction(row["probability"]), "exact polynomial evaluation")
        rows += len(outcomes)
        terms += sum(len(r["edge_polynomial"]) for r in outcomes)
    correct = read(SOURCE / "review/hybrid-common-sat/RESPONSE.json")
    forged = read(SOURCE / "review/balanced_zero_at_assignment_polynomial/RESPONSE.json")
    require(sum_polynomials(correct["mixture"]) == sum_polynomials(forged["mixture"]), "forgery did not preserve polynomial mass")
    values = [Fraction(v["value"]) for v in correct["bank_result"]["request"]["values"][:5]]
    changes = 0
    for before, after in zip(correct["mixture"], forged["mixture"], strict=True):
        require(before["tree"] == after["tree"] and before["probability"] == after["probability"], "forgery did not preserve probabilities")
        require(evaluate(polynomial(after), values) == Fraction(after["probability"]), "forged polynomial changes fitted probability")
        changes += polynomial(before) != polynomial(after)
    require(changes == 2, "wrong balanced forgery scope")
    result = {"schema": "source_fit_reference_saved_independent_review_v1", "status": "PASS",
        "source_evidence": str(SOURCE), "reviewer_sha256": sha(Path(__file__)),
        "outer_receipt_sha256": sha(SOURCE / "FINAL-RECEIPT.json"),
        "inner_receipt_sha256": sha(SOURCE / "review/RECEIPT.json"),
        "preservation_manifest_sha256": sha(SOURCE / "PRESERVATION-MANIFEST.json"),
        "preserved_files_checked": len(manifest["preserved_files"]), "preserved_bytes_checked": total_bytes,
        "current_source_runtime_input_pins_checked": len(outer["pin_rechecks"]), "bound_controls_checked": 14,
        "saved_native_rows_checked": rows, "saved_native_terms_checked": terms,
        "balanced_forgery_changed_rows": changes, "exact_mass_and_probability_arithmetic_checked": True,
        "provider_execution_repeated": False, "native_processes_started": 0, "compiler_processes_started": 0,
        "scope": "Saved byte/process/result binding review and independent Fraction arithmetic. Original compiler execution reused from scheduler receipt.",
        "source_admission_verified": False, "source_observation_fit_verified": False,
        "bank_metadata_independently_checked": False, "provider_work_checked": False,
        "resource_exhaustion_verified": False, "timed_readout_verified": False,
        "universal_native_refinement_verified": False, "full_solver_verified": False}
    with (HERE / "RECEIPT.json").open("x") as stream:
        json.dump(result, stream, sort_keys=True, indent=2)
        stream.write("\n")
    print(json.dumps({k: result[k] for k in ("status", "preserved_files_checked", "bound_controls_checked", "saved_native_rows_checked", "saved_native_terms_checked")}))


if __name__ == "__main__":
    main()
