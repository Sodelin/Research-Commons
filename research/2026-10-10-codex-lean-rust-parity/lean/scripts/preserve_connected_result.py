#!/usr/bin/env python3
"""Preserve a completed fresh current-union run without duplicating raw logs.

All source bodies, kernel receipts, stdout/stderr, selected declaration audit
and actual import bindings are copied into reviewable packet evidence. Native
loader bytes remain in scratch and their verified lossless archive manifest is
bound separately. No compiled artifact bytes or historical pass are substituted.
"""
from __future__ import annotations
import argparse
import datetime
import json
from pathlib import Path
from check_core import COMPILER, save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", type=Path)
    args = parser.parse_args()
    run = args.run.resolve()
    final = json.loads((run / "FINAL-RECEIPT.json").read_bytes())
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
    assert final["targets_passed"] == ["current/connected"]
    assert final["compiler_sha256"] == final["compiler_final_sha256"] == COMPILER
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    assert final["counts"] == {"fresh_components": 1340}
    assert final["fresh_every_selected_component_context_in_this_run"]
    target_path = run / "targets/current_connected/RESULT.json"
    target = json.loads(target_path.read_bytes())
    assert target["status"] == "PASS" and target["closure_modules"] == 1340
    for key in ["aggregate_receipt", "audit_receipt"]:
        assert target[key]["status"] == "PASS_FRESH_KERNEL_CHECK"
    audit_path = Path(target["audit_receipt"]["audit_output"])
    audit = json.loads(audit_path.read_bytes())
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    graph = json.loads((run / "DEPENDENCY-GRAPH.json").read_bytes())
    selected = graph["targets"]["current/connected"]
    assert audit["selected_modules"] == selected["order"]
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/current-connected" / stamp
    evidence.mkdir(parents=True)
    files = []
    for source in sorted(run.rglob("*")):
        if not source.is_file() or source.is_symlink():
            continue
        rel = source.relative_to(run)
        if "objects" in rel.parts or source.suffix in {".olean", ".ilean", ".ir", ".private", ".server"}:
            continue
        if source.name.startswith("NATIVE-LOADER."):
            continue
        files.append(distribute_file(source, evidence, Path("run") / rel))
    sources = []
    for module in selected["order"]:
        row = selected["modules"][module]
        source = ROOT / "source-store" / (row["sha256"] + ".lean")
        assert sha(source) == row["sha256"]
        destination = evidence / "sources" / (module.replace(".", "/") + ".lean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())
        sources.append({"module": module, "source_sha256": row["sha256"],
                        "imports": row["imports"], "evidence_path": str(destination.relative_to(evidence))})
    source_closure = {"status": "EXACT_CHECKED_SOURCE_AND_IMPORT_CLOSURE",
                      "graph_sha256": final["graph_sha256"], "modules": sources}
    save(evidence / "SOURCE-IMPORT-CLOSURE.json", source_closure)
    distributions = [row for row in files if row.get("encoding") == "gzip"]
    save(evidence / "COMPRESSED-DISTRIBUTIONS.json", {
        "status": "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION", "distributions": distributions,
        "original_run_unchanged": True,
        "restore_command": "python3 scripts/restore_distributed_evidence.py MANIFEST --output DESTINATION"})
    certificate = {"status": "PASS_1340_FRESH_COMPONENTS_AND_COMPLETE_OWNED_AUDIT",
                   "actual_run": str(run), "evidence": str(evidence.relative_to(ROOT)),
                   "final_receipt_sha256": sha(evidence / "run/FINAL-RECEIPT.json"),
                   "target_result_sha256": sha(evidence / "run" / target_path.relative_to(run)),
                   "graph_sha256": final["graph_sha256"], "compiler_sha256": COMPILER,
                   "mathlib_commit": final["mathlib_commit"], "native_runtime_digest": final["native_runtime_digest"],
                   "compiler_and_native_final_rehash_stable": True,
                   "fresh_components": 1340, "cache_or_prior_component_reuse": 0,
                   "owned_declarations": audit["declaration_count"],
                   "owned_theorems": audit["theorem_declaration_count"],
                   "owned_axioms": [], "nonstandard_axiom_rows": [], "missing_modules": [],
                   "trust_level": 0, "kernel_checking": True,
                   "source_import_closure_sha256": sha(evidence / "SOURCE-IMPORT-CLOSURE.json"),
                   "compressed_distributions_manifest": "COMPRESSED-DISTRIBUTIONS.json",
                   "compressed_distributions_manifest_sha256": sha(evidence / "COMPRESSED-DISTRIBUTIONS.json"),
                   "complete_owned_audit_raw_sha256": sha(audit_path),
                   "complete_owned_audit_raw_bytes": audit_path.stat().st_size,
                   "copied_evidence_files": files, "sources_and_imports_changed": False,
                   "compiled_artifact_bytes_distributed": False,
                   "native_loader_logs": "Original exact hashes in invocation receipts; separate lossless archive manifest is required before raw diagnostic space reclamation.",
                   "scope": "Exact additive public1340 environment and all original theorem assumptions. This is neither the separately frozen53-profile release replay nor the prepared latest1433 composition, and it does not close unresolved source/coverage master obligations."}
    save(evidence / "CERTIFICATE.json", certificate)
    save(ROOT / "CURRENT-CONNECTED-CERTIFICATE.json", certificate)
    print(json.dumps({k: certificate[k] for k in ["status", "fresh_components", "owned_declarations", "owned_theorems", "evidence"]}))


if __name__ == "__main__":
    main()
