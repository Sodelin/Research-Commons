#!/usr/bin/env python3
"""Authenticate the separate saved boundary-root audit, including cache reuse."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read


def main():
    stem = "WHOLE-EDGE-BOUNDARY-ROOT"
    certificate_path = PACKET / "lean" / (stem + "-CERTIFICATE.json")
    result_path = PACKET / "lean" / (stem + "-RESULT.json")
    certificate, result = read(certificate_path), read(result_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    errors = []
    for pin in result["preserved_files"]:
        if identity(evidence / pin["path"]) != {key: pin[key] for key in ("bytes", "sha256")}:
            errors.append("Preserved identity: " + pin["path"])
    name, certified = next(iter(certificate["targets"].items()))
    target = read(evidence / "targets" / name.replace("/", "_") / "RESULT.json")
    final = result["final_receipt"]
    raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
    audit = json.loads(raw)
    root = "G7OriginalEdgeBoundary"
    component = next(row for row in target["component_receipts"] if row["module"] == root)
    derivative = next(row for row in certificate["derivatives"] if row["module"] == root)
    counts = (len(audit["selected_modules"]), audit["declaration_count"],
              audit["theorem_declaration_count"])
    conditions = {
        "separate_target_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS"
            and target["status"] == "PASS" and len(certificate["targets"]) == 1,
        "preservation_binding": identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"]
            == certificate["preservation_manifest_sha256"],
        "stable_kernel_runtime": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "same_context": result["actual_run"] == certificate["actual_run"]
            and final["graph_sha256"] == certificate["graph_sha256"],
        "cache_reuse_disclosed": final["counts"] == certificate["counts"] == {"cache_reuse": 98}
            and not final["fresh_all_sources_claimed"]
            and not Path(component["receipt_directory"]).is_relative_to(Path(result["actual_run"])),
        "complete_owned_counts": counts == (98, 2739, 1760)
            == (target["closure_modules"], target["declarations"], target["theorems"])
            == (certified["closure_modules"], certified["owned_declarations"], certified["owned_theorems"])
            and len(audit["declarations"]) == audit["declaration_count"],
        "no_owned_or_nonstandard_axioms": not audit["owned_axioms"]
            and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
        "audit_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"],
        "authenticated_component_kernel_receipts": all(checked(row, final["compiler_sha256"],
            final["native_runtime_digest"]) for row in target["component_receipts"]),
        "fresh_aggregate_and_audit": all(checked(row, final["compiler_sha256"],
            final["native_runtime_digest"]) and Path(row["receipt_directory"]).is_relative_to(
                Path(result["actual_run"])) for row in
                (target["aggregate_receipt"], target["audit_receipt"])),
        "current_root_source": identity(PACKET / "quality/repairs/G7OriginalEdgeBoundary.lean")["sha256"]
            == identity(Path(derivative["source"]))["sha256"]
            == component["source_sha256"] == derivative["source_sha256"]
            == certificate["source_pins"][root],
        "no_gate_promotion": not certificate["historical_evidence_or_scientific_gates_promoted"]
            and not result["original_attempts_overwritten"],
    }
    errors.extend(key for key, passed in conditions.items() if not passed)
    receipt = {"schema": "original_boundary_root_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "conditions": conditions, "counts": counts,
        "preserved_artifacts": len(result["preserved_files"]),
        "certificate": identity(certificate_path), "result": identity(result_path),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helper_sha256": identity(Path(__file__).with_name("review_support_join.py"))["sha256"],
        "scope": "Saved source, kernel receipt and complete owned audit review for the separate boundary98 root. All 98 component contexts reused; aggregate and audit fresh. No acceptance of the pending whole-edge gathering chain, generated raw calendar support, native equivalence or full G7."}
    (PACKET / "quality/BOUNDARY-ROOT-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": not errors, "errors": errors,
                      "preserved_artifacts": receipt["preserved_artifacts"], "counts": counts}))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
