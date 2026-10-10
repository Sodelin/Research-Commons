#!/usr/bin/env python3
"""Check the saved 1433-module composition without rerunning its compiler."""
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read


def main():
    certificate_path = PACKET / "lean/LATEST-PUBLIC-UNION-CERTIFICATE.json"
    certificate = read(certificate_path)
    result = read(PACKET / "lean/LATEST-PUBLIC-UNION-RESULT.json")
    evidence = PACKET / "lean" / certificate["evidence"]
    sources = PACKET / "lean" / certificate["source_evidence"]
    target = read(evidence / "targets/current_latest-public-union/RESULT.json")
    graph = read(evidence / "DEPENDENCY-GRAPH.json")
    selected = graph["targets"]["current/latest-public-union"]
    closure = read(sources / "SOURCE-IMPORT-CLOSURE.json")
    final = result["final_receipt"]
    errors = []
    spec = importlib.util.spec_from_file_location("frozen_import_parser", sources / "IMPORT-PARSER.py")
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    for row in result["preserved_files"]:
        if identity(evidence / row["path"]) != {key: row[key] for key in ("bytes", "sha256")}:
            errors.append("Saved run identity: " + row["path"])
    manifest = read(sources / "SOURCE-PRESERVATION-MANIFEST.json")
    for row in manifest["files"]:
        if identity(sources / row["path"]) != {key: row[key] for key in ("bytes", "sha256")}:
            errors.append("Saved source identity: " + row["path"])
    for row in closure["modules"]:
        model = selected["modules"][row["module"]]
        source = sources / row["evidence_path"]
        if (identity(source)["sha256"] != row["source_sha256"]
                or row["source_sha256"] != model["sha256"]
                or row["imports"] != model["imports"]
                or parser.imports(source.read_text()) != row["imports"]):
            errors.append("Exact source/import context: " + row["module"])
    components = {row["module"]: row for row in target["component_receipts"]}
    for module, row in components.items():
        if not checked(row, final["compiler_sha256"], final["native_runtime_digest"]):
            errors.append("Original component kernel receipt: " + module)
        if row["source_sha256"] != selected["modules"][module]["sha256"]:
            errors.append("Original component source: " + module)
        for imported in selected["modules"][module]["imports"]:
            if imported in components and row["direct_import_sha256"].get(imported) != components[imported]["object_sha256"]:
                errors.append("Internal compiled import: " + module + " -> " + imported)
    distribution = certificate["complete_owned_audit"]
    archive = evidence / distribution["path"]
    raw = gzip.decompress(archive.read_bytes())
    audit = json.loads(raw)
    conditions = {
        "certificate_and_run_pass": certificate["status"] == "PASS_1433_AUTHENTICATED_COMPONENTS_AND_FRESH_COMPLETE_OWNED_AUDIT"
                                    and result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "exact_complete_1433_context": len(components) == len(closure["modules"]) == len(selected["order"])
                                       == target["closure_modules"] == certificate["closure_modules"] == 1433
                                       and audit["selected_modules"] == selected["order"],
        "freshness_explicit": final["counts"] == {"cache_reuse": 1433}
                              and certificate["authenticated_exact_component_admissions"] == 1433
                              and certificate["fresh_components_in_this_run"] == 0
                              and not certificate["fresh_all_sources_claimed"],
        "fresh_aggregate_full_audit": all(checked(target[key], final["compiler_sha256"], final["native_runtime_digest"])
                                         and Path(target[key]["receipt_directory"]).is_relative_to(Path(certificate["actual_run"]))
                                         for key in ("aggregate_receipt", "audit_receipt")),
        "stable_kernel": final["trust_level"] == 0 and final["kernel_checking"]
                         and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "no_missing_or_nonstandard_axioms": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"]
                                            and not audit["missing_modules"],
        "full_owned_counts": audit["declaration_count"] == len(audit["declarations"])
                             == target["declarations"] == certificate["owned_declarations"] == 98330
                             and audit["theorem_declaration_count"] == target["theorems"]
                             == certificate["owned_theorems"] == 90253,
        "lossless_audit": identity(archive) == {key: distribution[key] for key in ("bytes", "sha256")}
                          and len(raw) == distribution["restored_bytes"]
                          and hashlib.sha256(raw).hexdigest() == distribution["restored_sha256"],
        "saved_graph_and_source_manifest": identity(evidence / "DEPENDENCY-GRAPH.json")["sha256"]
                                           == certificate["graph_sha256"] == closure["graph_sha256"]
                                           and identity(sources / "SOURCE-IMPORT-CLOSURE.json")["sha256"] == certificate["source_import_closure_sha256"]
                                           and identity(sources / "SOURCE-PRESERVATION-MANIFEST.json")["sha256"] == certificate["source_preservation_manifest_sha256"],
        "earlier_receipts_retained": certificate["current_fresh_1340_context_retained"]
                                     and not certificate["historical_graphs_or_receipts_overwritten"],
    }
    errors.extend(key for key, passed in conditions.items() if not passed)
    receipt = {"schema": "latest_1433_union_saved_quality_review_v1",
               "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
               "errors": errors, "conditions": conditions,
               "sources_checked": len(closure["modules"]), "run_files_checked": len(result["preserved_files"]),
               "source_files_checked": len(manifest["files"]), "certificate": identity(certificate_path),
               "reviewer_sha256": identity(Path(__file__))["sha256"],
               "helper_sha256": identity(Path(__file__).with_name("review_support_join.py"))["sha256"],
               "import_parser_sha256": identity(sources / "IMPORT-PARSER.py")["sha256"],
               "scope": "Saved exact-source/import/component-context and complete ownership review. All1433 components are authenticated earlier checks; aggregate/audit fresh. No new compiler invocation, allfresh claim, native Rust refinement or missing scientific/master endpoint inferred."}
    (PACKET / "quality/LATEST-UNION-REVIEW.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors[:20], "sources": len(closure["modules"])}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
