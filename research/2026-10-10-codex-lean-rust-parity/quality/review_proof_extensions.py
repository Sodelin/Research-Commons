#!/usr/bin/env python3
"""Check saved full-epoch and original-population composition receipts."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read


def review(stem, expected, freshness):
    certificate_path = PACKET / "lean" / (stem + "-CERTIFICATE.json")
    result_path = PACKET / "lean" / (stem + "-RESULT.json")
    certificate, result = read(certificate_path), read(result_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    final = result["final_receipt"]
    errors, targets = [], []
    for pin in result["preserved_files"]:
        if identity(evidence / pin["path"]) != {key: pin[key] for key in ("bytes", "sha256")}:
            errors.append("Preserved identity: " + pin["path"])
    conditions = {
        "all_requested_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS",
        "preservation_binding": identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"]
            == certificate["preservation_manifest_sha256"],
        "stable_kernel_runtime": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "same_context": result["actual_run"] == certificate["actual_run"]
            and final["graph_sha256"] == certificate["graph_sha256"],
        "freshness": final["counts"] == certificate["counts"] == freshness
            and not final["fresh_all_sources_claimed"],
        "no_gate_promotion": not certificate["historical_evidence_or_scientific_gates_promoted"],
    }
    pins = {row["module"]: row for row in certificate["derivatives"]}
    for name, certified in certificate["targets"].items():
        root = certified["roots"][0]
        target = read(evidence / "targets" / name.replace("/", "_") / "RESULT.json")
        raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
        audit = json.loads(raw)
        component = next(row for row in target["component_receipts"] if row["module"] == root)
        counts = (len(audit["selected_modules"]), audit["declaration_count"], audit["theorem_declaration_count"])
        conditions_for_root = {
            "target_pass": target["status"] == "PASS",
            "complete_owned_counts": counts == expected[root]
                == (target["closure_modules"], target["declarations"], target["theorems"])
                and len(audit["declarations"]) == audit["declaration_count"],
            "no_owned_or_nonstandard_axioms": not audit["owned_axioms"]
                and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
            "audit_distribution_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"],
            "fresh_root_aggregate_and_audit": all(checked(row, final["compiler_sha256"],
                final["native_runtime_digest"]) for row in
                (component, target["aggregate_receipt"], target["audit_receipt"]))
                and Path(component["receipt_directory"]).is_relative_to(Path(result["actual_run"])),
            "current_root_source": identity(PACKET / "reuse/sources" / (root + ".lean"))["sha256"]
                == component["source_sha256"] == pins[root]["source_sha256"]
                == certificate["source_pins"][root],
        }
        errors.extend(root + ": " + key for key, passed in conditions_for_root.items() if not passed)
        targets.append({"root": root, "counts": counts, "conditions": conditions_for_root})
    errors.extend(key for key, passed in conditions.items() if not passed)
    return {"pass": not errors, "errors": errors, "conditions": conditions,
        "preserved_artifacts": len(result["preserved_files"]), "targets": targets,
        "certificate": identity(certificate_path), "result": identity(result_path)}


def main():
    epoch = review("FULL-EPOCH-SUPPORT", {"G7FullEpochSupport": (124, 3398, 2161)},
                   {"cache_reuse": 123, "fresh_components": 1})
    population = review("ORIGINAL-POPULATION", {
        "G6OriginalPopulationExposure": (88, 2355, 1453),
        "G6OriginalPopulationSpectralSupport": (88, 2359, 1457)},
        {"cache_reuse": 174, "fresh_components": 2})
    receipt = {"schema": "original_source_composition_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": epoch["pass"] and population["pass"],
        "full_epoch": epoch, "original_population": population,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helper_sha256": identity(Path(__file__).with_name("review_support_join.py"))["sha256"],
        "scope": "Saved kernel/audit/current source identity review for exact composition statements. Counts overlap. No new compiler invocation, runtime equivalence, source admission or full G6/G7 master certificate."}
    (PACKET / "quality/PROOF-EXTENSION-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "epoch_errors": epoch["errors"], "population_errors": population["errors"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
