#!/usr/bin/env python3
"""Authenticate the saved1463-module union without compiling its sources again."""
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read


def main():
    cp = PACKET / "lean/COHERENT-UNION-1463-CERTIFICATE.json"
    rp = PACKET / "lean/COHERENT-UNION-1463-RESULT.json"
    cert, result = read(cp), read(rp)
    evidence = PACKET / "lean" / cert["evidence"]
    graph = read(evidence / "DEPENDENCY-GRAPH.json")
    selected = graph["targets"]["current/connected"]
    target = read(evidence / "targets/current_connected/RESULT.json")
    final = result["final_receipt"]
    certified = cert["targets"]["current/connected"]
    preparation = read(evidence.parent / "PREPARATION.json")
    old = read(PACKET / "lean/LATEST-PUBLIC-UNION-CERTIFICATE.json")
    parser_path = PACKET / "lean" / old["source_evidence"] / "IMPORT-PARSER.py"
    old_review = read(PACKET / "quality/LATEST-UNION-REVIEW.json")
    errors = []
    if identity(parser_path)["sha256"] != old_review["import_parser_sha256"]:
        raise ValueError("Frozen original import parser changed")
    spec = importlib.util.spec_from_file_location("frozen_union_import_parser", parser_path)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    for row in result["preserved_files"]:
        if identity(evidence / row["path"]) != {k: row[k] for k in ("bytes", "sha256")}:
            errors.append("preserved artifact: " + row["path"])
    components = {row["module"]: row for row in target["component_receipts"]}
    for name, model in selected["modules"].items():
        source = evidence.parent / "sources" / (name.replace(".", "/") + ".lean")
        row = components[name]
        if (identity(source)["sha256"] != model["sha256"] or model["sha256"] != cert["source_pins"][name]
                or parser.imports(source.read_text()) != model["imports"]):
            errors.append("source/import context: " + name)
        if not checked(row, final["compiler_sha256"], final["native_runtime_digest"]):
            errors.append("earlier component kernel check: " + name)
        if row["source_sha256"] != model["sha256"]:
            errors.append("component source: " + name)
        for imported in model["imports"]:
            if imported in components and row["direct_import_sha256"].get(imported) != components[imported]["object_sha256"]:
                errors.append("compiled import: " + name + " -> " + imported)
    raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
    audit = json.loads(raw)
    checks = {
        "all_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "complete_coherent_context": len(components) == len(selected["order"]) == len(selected["modules"])
            == target["closure_modules"] == 1463 and audit["selected_modules"] == selected["order"]
            and len(set(audit["selected_modules"])) == 1463,
        "full_owned_counts": audit["declaration_count"] == len(audit["declarations"])
            == target["declarations"] == certified["owned_declarations"] == 99149
            and audit["theorem_declaration_count"] == target["theorems"] == certified["owned_theorems"] == 90822,
        "no_owned_nonstandard_or_missing": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"]
            and not audit["missing_modules"],
        "exact_audit_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"]
            == target["audit_receipt"]["auxiliary_outputs"][0]["sha256"],
        "fresh_aggregate_and_audit": all(checked(target[k], final["compiler_sha256"], final["native_runtime_digest"])
            and Path(target[k]["receipt_directory"]).is_relative_to(Path(result["actual_run"]))
            for k in ("aggregate_receipt", "audit_receipt")),
        "explicit_component_reuse": final["counts"] == cert["counts"] == {"cache_reuse": 1463}
            and not final["fresh_all_sources_claimed"],
        "stable_kernel_runtime": final["trust_level"] == 0 and final["kernel_checking"]
            and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "context_and_preservation": cert["actual_run"] == result["actual_run"]
            and identity(evidence / "DEPENDENCY-GRAPH.json")["sha256"] == cert["graph_sha256"] == final["graph_sha256"]
            and identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"] == cert["preservation_manifest_sha256"],
        "strict_core_retained": preparation["builder_sha256"] == "13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc"
            and preparation["audit_template_sha256"] == "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
            and not preparation["namespace_adapter_derivation"]["compiler_kernel_cache_and_resource_policies_changed"],
        "no_historical_or_scientific_promotion": not cert["historical_evidence_or_scientific_gates_promoted"]
            and not result["original_attempts_overwritten"] and not result["compiled_artifact_bytes_distributed"],
    }
    errors.extend(k for k, passed in checks.items() if not passed)
    answer = {"schema": "coherent1463_saved_root_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "source_modules_checked": 1463,
        "preserved_artifacts_checked": len(result["preserved_files"]), "declarations": 99149,
        "theorem_declarations": 90822, "certificate": identity(cp), "result": identity(rp),
        "reviewer": identity(Path(__file__)), "import_parser": identity(parser_path),
        "scope": "One coherent1463-module source/import/artifact context with authenticated earlier kernel components and a fresh aggregate and complete ownership audit. Earlier1433 and all-fresh1340 evidence remains separate. No compiler rerun, native Rust theorem, source admission or G6/G7 master closure is inferred.",
        "source_admission_verified": False, "master_complete": False}
    (PACKET / "quality/COHERENT-UNION-REVIEW.json").write_text(json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors[:20], "source_modules": 1463,
                      "preserved_artifacts": len(result["preserved_files"])}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
