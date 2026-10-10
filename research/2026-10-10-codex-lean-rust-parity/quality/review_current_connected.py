#!/usr/bin/env python3
"""Independently audit preserved fresh public-union evidence and distribution."""
import gzip
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]


def identity(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def read(path):
    return json.loads(path.read_bytes())


def main():
    certificate_path = PACKET / "lean/CURRENT-CONNECTED-CERTIFICATE.json"
    certificate = read(certificate_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    errors = []
    for pin in certificate["copied_evidence_files"]:
        observed = identity(evidence / pin["path"])
        if observed != {key: pin[key] for key in ("bytes", "sha256")}:
            errors.append("Preserved identity: " + pin["path"])
    final_path = evidence / "run/FINAL-RECEIPT.json"
    final = read(final_path)
    target_path = evidence / "run/targets/current_connected/RESULT.json"
    target = read(target_path)
    graph_path = evidence / "run/DEPENDENCY-GRAPH.json"
    graph = read(graph_path)
    selected = graph["targets"]["current/connected"]
    closure_path = evidence / "SOURCE-IMPORT-CLOSURE.json"
    closure = read(closure_path)
    source_errors = []
    for row in closure["modules"]:
        frozen = evidence / row["evidence_path"]
        current = PACKET / "lean/source-store" / (row["source_sha256"] + ".lean")
        model = selected["modules"][row["module"]]
        if (identity(frozen)["sha256"] != row["source_sha256"]
                or identity(current)["sha256"] != row["source_sha256"]
                or row["source_sha256"] != model["sha256"]
                or row["imports"] != model["imports"]):
            source_errors.append(row["module"])
    manifest_path = evidence / certificate["compressed_distributions_manifest"]
    manifest = read(manifest_path)
    assert len(manifest["distributions"]) == 1
    distribution = manifest["distributions"][0]
    archive = evidence / distribution["path"]
    assert distribution["encoding"] == "gzip"
    decoded = gzip.decompress(archive.read_bytes())
    decoded_sha = hashlib.sha256(decoded).hexdigest()
    audit = json.loads(decoded)
    original_audit = Path(certificate["actual_run"]) / distribution["restored_path"].removeprefix("run/")
    conditions = {
        "certificate_pass": certificate["status"] == "PASS_1340_FRESH_COMPONENTS_AND_COMPLETE_OWNED_AUDIT",
        "final_and_target_pass": final["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "all_1340_fresh": final["counts"] == {"fresh_components": 1340} and final["fresh_every_selected_component_context_in_this_run"] and certificate["cache_or_prior_component_reuse"] == 0,
        "complete_exact_context": len(closure["modules"]) == len(selected["order"]) == target["closure_modules"] == 1340 and audit["selected_modules"] == selected["order"] and not audit["missing_modules"],
        "sources_and_imports_match": not source_errors,
        "saved_receipt_and_graph_pins": identity(final_path)["sha256"] == certificate["final_receipt_sha256"] and identity(target_path)["sha256"] == certificate["target_result_sha256"] and identity(graph_path)["sha256"] == final["graph_sha256"] == certificate["graph_sha256"] and identity(closure_path)["sha256"] == certificate["source_import_closure_sha256"],
        "fresh_component_kernel_receipts": len(target["component_receipts"]) == 1340 and all(row["status"] == "PASS_FRESH_KERNEL_CHECK" and row["exit_code"] == 0 and row["source_and_imports_stable"] and row["source_sha256"] == selected["modules"][row["module"]]["sha256"] and "-t0" in row["command"] and "-Ddebug.skipKernelTC=false" in row["command"] for row in target["component_receipts"]),
        "fresh_aggregate_and_audit": all(target[key]["status"] == "PASS_FRESH_KERNEL_CHECK" and target[key]["exit_code"] == 0 and target[key]["source_and_imports_stable"] for key in ("aggregate_receipt", "audit_receipt")),
        "trust_zero_and_stable_runtime": final["trust_level"] == 0 and final["kernel_checking"] and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"] and final["compiler_sha256"] == final["compiler_final_sha256"] == certificate["compiler_sha256"],
        "complete_audit_counts": audit["declaration_count"] == target["declarations"] == certificate["owned_declarations"] == 97493 and audit["theorem_declaration_count"] == target["theorems"] == certificate["owned_theorems"] == 89658,
        "no_owned_or_nonstandard_axioms": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"],
        "lossless_distribution_matches_original": manifest["status"] == "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION" and identity(manifest_path)["sha256"] == certificate["compressed_distributions_manifest_sha256"] and identity(archive) == {key: distribution[key] for key in ("bytes", "sha256")} and len(decoded) == distribution["restored_bytes"] == certificate["complete_owned_audit_raw_bytes"] and decoded_sha == distribution["restored_sha256"] == certificate["complete_owned_audit_raw_sha256"] == identity(original_audit)["sha256"],
    }
    errors += [key for key, passed in conditions.items() if not passed]
    receipt = {
        "schema": "fresh_current_union_static_quality_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "conditions": conditions,
        "preserved_artifacts_checked": len(certificate["copied_evidence_files"]),
        "exact_source_versions_checked": len(closure["modules"]),
        "source_errors": source_errors, "certificate": identity(certificate_path),
        "audit_raw_bytes": len(decoded), "audit_raw_sha256": decoded_sha,
        "audit_gzip": identity(archive), "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Independent static verification of the completed fresh 1340-component environment, preserved sources/receipts and lossless full audit. No new compiler execution, later1433/53-profile reproduction, universal solver refinement or scientific closure claim."
    }
    (PACKET / "quality/CURRENT-CONNECTED-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "errors", "preserved_artifacts_checked", "exact_source_versions_checked")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
