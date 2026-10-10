#!/usr/bin/env python3
"""Authenticate new source consumers without running Lean or native solvers."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read


def review(certificate_name, result_name, roots, freshness):
    certificate_path = PACKET / "lean" / certificate_name
    result_path = PACKET / "lean" / result_name
    certificate, result = read(certificate_path), read(result_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    final = result["final_receipt"]
    errors, targets = [], []
    for pin in result["preserved_files"]:
        if identity(evidence / pin["path"]) != {k: pin[k] for k in ("bytes", "sha256")}:
            errors.append("Preserved identity: " + pin["path"])
    conditions = {
        "requested_targets_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS"
            and certificate["status"] == "PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS",
        "manifest_bound": identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"]
            == certificate["preservation_manifest_sha256"],
        "same_run_graph_and_runtime": result["actual_run"] == certificate["actual_run"]
            and final["graph_sha256"] == certificate["graph_sha256"]
            and final["compiler_sha256"] == certificate["compiler_sha256"]
            and final["native_runtime_digest"] == certificate["native_runtime_digest"],
        "stable_kernel_runtime": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
            and certificate["compiler_and_native_final_stable"],
        "freshness_disclosed": final["counts"] == certificate["counts"] == freshness
            and not final["fresh_all_sources_claimed"],
        "history_and_science_preserved": not result["compiled_artifact_bytes_distributed"]
            and not result["original_attempts_overwritten"]
            and not certificate["historical_evidence_or_scientific_gates_promoted"],
    }
    pins = {row["module"]: row for row in certificate["derivatives"]}
    observed_roots = set()
    for name, certified in certificate["targets"].items():
        root = certified["roots"][0]
        observed_roots.add(root)
        source_name, source_hash, expected_counts = roots[root]
        target = read(evidence / "targets" / name.replace("/", "_") / "RESULT.json")
        raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
        audit = json.loads(raw)
        component = next(row for row in target["component_receipts"] if row["module"] == root)
        fresh = [component, target["aggregate_receipt"], target["audit_receipt"]]
        counts = (len(audit["selected_modules"]), len(audit["declarations"]),
                  sum(row["kind"] == "theorem" for row in audit["declarations"]))
        checks = {
            "target_pass": target["status"] == "PASS",
            "complete_owned_counts": counts == expected_counts
                == (target["closure_modules"], target["declarations"], target["theorems"])
                == (certified["closure_modules"], certified["owned_declarations"], certified["owned_theorems"])
                == (len(audit["selected_modules"]), audit["declaration_count"], audit["theorem_declaration_count"]),
            "unique_inventory": len(set(audit["selected_modules"])) == counts[0]
                and len({row["name"] for row in audit["declarations"]}) == counts[1],
            "no_owned_nonstandard_or_missing": not audit["owned_axioms"]
                and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
            "audit_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"]
                == target["audit_receipt"]["auxiliary_outputs"][0]["sha256"],
            "all_exact_components_checked": len(target["component_receipts"]) == counts[0]
                and {row["module"] for row in target["component_receipts"]} == set(audit["selected_modules"])
                and all(checked(row, final["compiler_sha256"], final["native_runtime_digest"])
                        and row["source_sha256"] == certificate["source_pins"][row["module"]]
                        for row in target["component_receipts"]),
            "fresh_root_aggregate_and_audit": all(
                checked(row, final["compiler_sha256"], final["native_runtime_digest"])
                and Path(row["receipt_directory"]).is_relative_to(Path(result["actual_run"]))
                for row in fresh),
            "exact_current_source": identity(PACKET / source_name)["sha256"] == source_hash
                == component["source_sha256"] == pins[root]["source_sha256"]
                == certificate["source_pins"][root],
            "aggregate_audit_source_binding": target["aggregate_receipt"]["source_sha256"]
                == certified["aggregate_source_sha256"] and target["audit_receipt"]["source_sha256"]
                == certified["audit_source_sha256"],
        }
        errors.extend(root + ": " + key for key, value in checks.items() if not value)
        targets.append({"root": root, "counts": counts, "checks": checks})
    conditions["all_expected_roots"] = observed_roots == set(roots)
    errors.extend(key for key, value in conditions.items() if not value)
    return {"pass": not errors, "errors": errors, "conditions": conditions,
            "targets": targets, "preserved_artifacts": len(result["preserved_files"]),
            "certificate": identity(certificate_path), "result": identity(result_path)}


def write_review(output_name, schema, proof, scope, reviewer):
    receipt = {"schema": schema, "observed_utc": datetime.now(timezone.utc).isoformat(),
               "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
               "scope": scope, "reviewer": identity(reviewer),
               "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                           ("review_saved_consumers.py", "review_support_join.py")},
               "general_native_refinement_inferred": False, "source_admission_verified": False,
               "master_complete": False}
    (PACKET / "quality" / output_name).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": receipt["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]
