#!/usr/bin/env python3
"""Review the recovered semantic context and exact ancestral completion bridge."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, checked, identity, read


def semantic():
    certificate_path = PACKET / "lean/SEMANTIC-RANK-RECOVERY-CERTIFICATE.json"
    result_path = PACKET / "lean/SEMANTIC-RANK-RECOVERY-RESULT.json"
    certificate, result = read(certificate_path), read(result_path)
    evidence = PACKET / "lean" / certificate["evidence"]
    final = result["final_receipt"]
    certified = certificate["targets"]["recovery/g7-semantic-rank"]
    target = read(evidence / "targets/recovery_g7-semantic-rank/RESULT.json")
    raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
    audit = json.loads(raw)
    roots = {"G7ExactLawResourceGame", "G7ActualExactLawResponses", "G7ExactLawRankCompression",
             "G7OriginalFamilyStrategy", "G7OriginalCarrierCoverage"}
    errors = []
    for row in result["preserved_files"]:
        if identity(evidence / row["path"]) != {key: row[key] for key in ("bytes", "sha256")}:
            errors.append("Preserved artifact: " + row["path"])
    component_by_name = {row["module"]: row for row in target["component_receipts"]}
    for root in roots:
        source = evidence.parent / "sources" / (root + ".lean")
        if identity(source)["sha256"] != certificate["source_pins"][root] or component_by_name[root]["source_sha256"] != certificate["source_pins"][root]:
            errors.append("Root source/receipt identity: " + root)
    for derivative in certificate["derivatives"]:
        if identity(Path(derivative["source"]))["sha256"] != derivative["source_sha256"]:
            errors.append("Current derivative identity: " + derivative["module"])
    checks = {
        "all_five_roots": roots == set(certified["roots"]) and target["roots"] == len(roots)
            and roots <= set(component_by_name),
        "complete_owned_audit": (len(audit["selected_modules"]), audit["declaration_count"],
            audit["theorem_declaration_count"]) == (191, 5130, 3221)
            and len(audit["declarations"]) == 5130
            and (target["closure_modules"], target["declarations"], target["theorems"]) == (191, 5130, 3221),
        "no_owned_nonstandard_axioms_or_missing": not audit["owned_axioms"]
            and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
        "decoded_audit_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"],
        "same_graph_and_actual_run": final["graph_sha256"] == certificate["graph_sha256"]
            and result["actual_run"] == certificate["actual_run"],
        "stable_checked_kernel": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
            and all(checked(row, final["compiler_sha256"], final["native_runtime_digest"])
                    for row in (*target["component_receipts"], target["aggregate_receipt"], target["audit_receipt"])),
        "fresh_carrier_aggregate_and_audit": Path(component_by_name["G7OriginalCarrierCoverage"]["receipt_directory"])
            .is_relative_to(Path(result["actual_run"]))
            and final["counts"] == certificate["counts"] == {"cache_reuse": 190, "fresh_components": 1}
            and not final["fresh_all_sources_claimed"],
        "result_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "preservation_manifest_bound": identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"]
            == certificate["preservation_manifest_sha256"],
        "no_gate_promotion": not certificate["historical_evidence_or_scientific_gates_promoted"],
    }
    errors.extend(key for key, passed in checks.items() if not passed)
    return {"pass": not errors, "errors": errors, "checks": checks,
            "preserved_artifacts": len(result["preserved_files"]),
            "certificate": identity(certificate_path), "result": identity(result_path)}


def main():
    game = semantic()
    completion = review("EFFECTIVE-COMPLETION", {"G7EffectiveAncestralCompletion": (140, 3635, 2353)},
                       {"cache_reuse": 139, "fresh_components": 1})
    receipt = {
        "schema": "g7_semantic_and_completion_saved_proof_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": game["pass"] and completion["pass"], "semantic_context": game,
        "ancestral_completion": completion,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Five recovered semantic roots in one191-module complete ownership audit, plus the separate140-module recurrence/support/selected ancestral infinite-limit bridge. Prior failures retained, freshness disclosed. No new compilation, effective QE/Pareto/source-census algorithm or generic native refinement/master closure inferred.",
    }
    (PACKET / "quality/SEMANTIC-COMPLETION-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "semantic_errors": game["errors"],
                      "completion_errors": completion["errors"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
