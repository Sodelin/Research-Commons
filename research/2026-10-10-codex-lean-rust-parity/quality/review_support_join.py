#!/usr/bin/env python3
"""Review preserved kernel evidence for the three new support/join roots.

This is a saved-evidence review. It does not run Lean or a Rust oracle.
"""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def identity(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def checked(receipt, compiler, runtime):
    return (receipt["status"] == "PASS_FRESH_KERNEL_CHECK"
            and receipt["exit_code"] == 0
            and receipt["source_and_imports_stable"]
            and receipt["compiler_sha256"] == compiler
            and receipt["native_runtime_digest"] == runtime
            and "-t0" in receipt["command"]
            and "-Ddebug.skipKernelTC=false" in receipt["command"])


def main():
    certificate_path = PACKET / "lean/SUPPORT-JOIN-CERTIFICATE.json"
    result_path = PACKET / "lean/SUPPORT-JOIN-RESULT.json"
    certificate, result = read(certificate_path), read(result_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    errors, preserved, targets = [], [], []
    for pin in result["preserved_files"]:
        observed = identity(evidence / pin["path"])
        passed = observed == {key: pin[key] for key in ("bytes", "sha256")}
        preserved.append({"path": pin["path"], **observed, "pass": passed})
        if not passed:
            errors.append("Preserved artifact: " + pin["path"])
    final = result["final_receipt"]
    conditions = {
        "result_and_certificate_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS"
            and certificate["status"] == "PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS",
        "preservation_manifest_identity": identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"]
            == certificate["preservation_manifest_sha256"],
        "stable_kernel_and_runtime": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
            and certificate["compiler_and_native_final_stable"],
        "same_context": result["actual_run"] == certificate["actual_run"]
            and final["graph_sha256"] == certificate["graph_sha256"],
        "freshness_disclosed": final["counts"] == certificate["counts"]
            == {"fresh_components": 3, "cache_reuse": 354}
            and not final["fresh_all_sources_claimed"],
        "no_compiled_distribution_or_gate_promotion": not result["compiled_artifact_bytes_distributed"]
            and not result["original_attempts_overwritten"]
            and not certificate["historical_evidence_or_scientific_gates_promoted"],
    }
    expected_counts = {
        "G7ConstructivePanelJoin": (117, 3210, 2025),
        "G7PopulationSelectedSupport": (120, 3318, 2097),
        "G7EffectivePanelJoin": (120, 3323, 2104),
    }
    derivative_pins = {row["module"]: row for row in certificate["derivatives"]}
    for name, certified in certificate["targets"].items():
        root = certified["roots"][0]
        target = read(evidence / "targets" / name.replace("/", "_") / "RESULT.json")
        raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
        audit = json.loads(raw)
        aggregate, audit_receipt = target["aggregate_receipt"], target["audit_receipt"]
        component = next(row for row in target["component_receipts"] if row["module"] == root)
        source = PACKET / "reuse/sources" / (root + ".lean")
        counts = (len(audit["selected_modules"]), audit["declaration_count"],
                  audit["theorem_declaration_count"])
        checks = {
            "pass": target["status"] == "PASS",
            "complete_owned_counts": counts == expected_counts[root]
                == (target["closure_modules"], target["declarations"], target["theorems"])
                == (certified["closure_modules"], certified["owned_declarations"], certified["owned_theorems"]),
            "complete_declaration_inventory": len(audit["declarations"]) == audit["declaration_count"]
                and len(set(audit["selected_modules"])) == len(audit["selected_modules"]),
            "no_owned_or_nonstandard_axioms": not audit["owned_axioms"]
                and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
            "raw_audit_identity": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"]
                == audit_receipt["auxiliary_outputs"][0]["sha256"],
            "fresh_aggregate_audit_and_root": all(checked(row, final["compiler_sha256"],
                final["native_runtime_digest"]) for row in (aggregate, audit_receipt, component))
                and Path(component["receipt_directory"]).is_relative_to(Path(result["actual_run"])),
            "current_root_source_identity": identity(source)["sha256"]
                == derivative_pins[root]["source_sha256"] == certificate["source_pins"][root]
                == component["source_sha256"],
            "aggregate_audit_source_identity": aggregate["source_sha256"]
                == certified["aggregate_source_sha256"] and audit_receipt["source_sha256"]
                == certified["audit_source_sha256"],
        }
        targets.append({"root": root, "counts": counts, "checks": checks,
                        "pass": all(checks.values())})
        errors.extend(root + ": " + key for key, passed in checks.items() if not passed)
    errors.extend(key for key, passed in conditions.items() if not passed)
    receipt = {
        "schema": "support_join_saved_evidence_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "conditions": conditions,
        "targets": targets, "preserved_artifacts": preserved,
        "certificate": identity(certificate_path), "result": identity(result_path),
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Preserved-byte identity, complete overlapping owned audits, fresh root/aggregate/audit kernel receipts and current root sources. No compiler rerun, general Rust refinement, source admission or master closure."
    }
    (PACKET / "quality/SUPPORT-JOIN-REVIEW.json").write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": not errors, "errors": errors,
                      "preserved_artifacts": len(preserved), "targets": len(targets)}))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
