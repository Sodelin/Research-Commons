#!/usr/bin/env python3
"""Review preserved inherited-provider executions without rerunning a provider."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("evidence", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    evidence = args.evidence.resolve()
    manifest_raw = (evidence / "PRESERVATION-MANIFEST.json").read_bytes()
    manifest = json.loads(manifest_raw)
    require(Path(manifest["evidence"]).resolve() == evidence, "Evidence location changed")
    work = Path(manifest["workspace"])
    seen = set()
    total = 0
    for row in manifest["preserved_files"]:
        relative = Path(row["relative_path"])
        require(not relative.is_absolute() and ".." not in relative.parts
                and str(relative) not in seen, "Invalid or duplicate saved path")
        seen.add(str(relative))
        original = Path(row["original_path"])
        require(original.is_relative_to(work), "Original is outside declared scratch context")
        saved = (evidence / relative).read_bytes()
        require(len(saved) == row["bytes"] and sha(saved) == row["sha256"]
                and saved == original.read_bytes(), "Saved/original identity mismatch: " + str(relative))
        total += len(saved)
    final_raw = (evidence / "FINAL-RECEIPT.json").read_bytes()
    final = json.loads(final_raw)
    review_raw = (evidence / "review/RECEIPT.json").read_bytes()
    receipt = json.loads(review_raw)
    require(sha(final_raw) == manifest["final_receipt_sha256"], "Final receipt changed")
    require(sha(review_raw) == manifest["review_receipt_sha256"] == final["review_receipt_sha256"],
            "Provider review receipt changed")
    require(final["status"] == "PASS_FOURTEEN_SAVED_OUTPUT_REFERENCE_CONTROLS"
            and final["exit_code"] == 0 and final["monitor_error"] is None
            and receipt["status"] == "PASS", "Run did not pass")
    require(final["passed"] == receipt["passed"] == len(receipt["controls"]) == 14,
            "Incomplete selected controls")
    require(final["saved_native_rows"] == receipt["saved_native_rows"] == 9
            and final["saved_native_terms"] == receipt["saved_native_terms"] == 27
            and receipt["saved_native_cases"] == 3, "Saved table coverage changed")
    require(final["native_processes_started"] == final["compiler_processes_started"]
            == receipt["native_processes_started"] == receipt["lean_compiler_processes_started"] == 0,
            "Unexpected native/compiler execution")
    require(manifest["original_bytes_unchanged"] and manifest["saved_native_outputs_not_rerun"]
            and manifest["native_ELF_distributed"] is False, "Preservation scope changed")
    for path, digest in final["pin_rechecks"].items():
        require(sha(Path(path).read_bytes()) == digest, "Execution source/runtime pin changed: " + path)
    for row in receipt["source_pins"]:
        raw = Path(row["path"]).read_bytes()
        require(sha(raw) == row["sha256"] and len(raw) == row["bytes"], "Provider source pin changed")
    require(receipt["source_pins_stable"], "Provider reported unstable inputs")
    controls = {}
    for row in receipt["controls"]:
        name = row["case"]
        require(name not in controls and row["pass"] is True, "Duplicate/failed control")
        controls[name] = row
        case = evidence / "review" / name
        require(sha((case / "REQUEST.json").read_bytes()) == row["request_sha256"]
                and sha((case / "RESPONSE.json").read_bytes()) == row["response_sha256"],
                "Control input/output binding changed: " + name)
    require(controls["balanced_zero_at_assignment_polynomial"]["accepted"] is False
            and controls["balanced_probability_only"]["accepted"] is False,
            "Balanced law/probability forgery was accepted")
    original = json.loads((evidence / "review/hybrid-common-sat/RESPONSE.json").read_bytes())
    forged = json.loads((evidence / "review/balanced_zero_at_assignment_polynomial/RESPONSE.json").read_bytes())
    require([r["probability"] for r in original["mixture"]]
            == [r["probability"] for r in forged["mixture"]]
            and original["mixture"] != forged["mixture"], "Polynomial forgery did not preserve reported probabilities")
    for name in ("source_admission_verified", "timed_readout_verified",
                 "universal_native_refinement_verified", "full_solver_verified"):
        require(final[name] is False and receipt[name] is False, "Unestablished scientific gate promoted")
    require(final["peak_nonreclaimable_bytes"] < 16106127360
            and final["peak_native_allocated_bytes"] < 973078528, "Approved resource limit crossed")
    result = {"schema": "saved_source_fit_reference_root_review_v1", "status": "PASS",
              "observed_utc": datetime.now(timezone.utc).isoformat(),
              "reviewer_sha256": sha(Path(__file__).read_bytes()),
              "manifest_sha256": sha(manifest_raw), "final_receipt_sha256": sha(final_raw),
              "provider_receipt_sha256": sha(review_raw), "preserved_files": len(seen),
              "preserved_bytes": total, "execution_pins_rehashed": len(final["pin_rechecks"]),
              "saved_rooted_rows": 9, "saved_nonzero_terms": 27, "selected_controls": 14,
              "polynomial_forgery_preserves_reported_probabilities": True,
              "compiler_or_law_provider_called_by_this_reviewer": False,
              "source_admission_or_universal_refinement_inferred": False}
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
