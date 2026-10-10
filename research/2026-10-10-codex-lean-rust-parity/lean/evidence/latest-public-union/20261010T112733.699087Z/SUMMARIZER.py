#!/usr/bin/env python3
"""Freeze the exact latest composition and its separately checked full audit.

The current run authenticates component artifacts from their exact earlier
contexts. Its aggregate and ownership audit are fresh. Historical graphs,
sources, receipts and the original 1340 fresh-run certificate stay intact.
"""
from __future__ import annotations
import gzip
import hashlib
import json
from pathlib import Path
import shutil
from assemble_public import imports as lean_imports
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
TARGET = "current/latest-public-union"


def main():
    result_path = ROOT / "LATEST-PUBLIC-UNION-RESULT.json"
    result = json.loads(result_path.read_bytes())
    final = result["final_receipt"]
    work = Path(result["workspace"])
    evidence = ROOT / result["evidence"]
    source_evidence = evidence.parent
    prep_path = work / "PREPARATION.json"
    prep = json.loads(prep_path.read_bytes())
    graph_path = work / "DEPENDENCY-GRAPH.json"
    graph = json.loads(graph_path.read_bytes())
    selected = graph["targets"][TARGET]
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
    assert final["targets_passed"] == final["targets_requested"] == [TARGET]
    assert final["counts"] == {"cache_reuse": 1433}
    assert not final["fresh_all_sources_claimed"]
    assert final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"]
    assert final["compiler_sha256"] == final["compiler_final_sha256"] == COMPILER
    assert final["graph_sha256"] == prep["graph_sha256"] == sha(graph_path)
    assert len(selected["order"]) == len(selected["modules"]) == 1433
    rows = {r.get("restored_path", r["path"]): r for r in result["preserved_files"]}

    def read(relative):
        row = rows[relative]
        path = evidence / row["path"]
        assert sha(path) == row["sha256"] and path.stat().st_size == row["bytes"]
        data = path.read_bytes()
        if row.get("encoding") == "gzip":
            data = gzip.decompress(data)
        assert len(data) == row.get("restored_bytes", row["bytes"])
        assert hashlib.sha256(data).hexdigest() == row.get("restored_sha256", row["sha256"])
        return data

    # Verify the entire portable preservation inventory, including restored
    # native-loader and complete audit identities before issuing acceptance.
    for relative in rows:
        read(relative)
    target_path = "targets/current_latest-public-union/RESULT.json"
    checked = json.loads(read(target_path))
    assert checked["status"] == "PASS" and checked["closure_modules"] == 1433
    for name in ["aggregate_receipt", "audit_receipt"]:
        receipt = checked[name]
        assert receipt["status"] == "PASS_FRESH_KERNEL_CHECK" and receipt["exit_code"] == 0
        assert receipt["compiler_sha256"] == COMPILER
        assert receipt["source_and_imports_stable"] and receipt["native_runtime_stat_stable"]
        assert receipt["native_initialized_libraries_bound"]
        assert "-t0" in receipt["command"] and "-Ddebug.skipKernelTC=false" in receipt["command"]
        imported = set(receipt["direct_import_artifacts"])
        expected = set(selected["order"])
        if name == "audit_receipt":
            expected.add("Lean.Util.CollectAxioms")
        assert imported == expected
    audit_relative = str(Path(checked["audit_receipt"]["audit_output"]).relative_to(Path(result["actual_run"])))
    audit = json.loads(read(audit_relative))
    assert audit["selected_modules"] == selected["order"]
    assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
    assert audit["declaration_count"] == checked["declarations"] == 98330
    assert audit["theorem_declaration_count"] == checked["theorems"] == 90253
    components = {r["module"]: r for r in checked["component_receipts"]}
    assert set(components) == set(selected["order"])
    origins = {r["module"]: r for r in prep["source_context_inventory"]}
    sources = []
    for module in selected["order"]:
        row = selected["modules"][module]
        receipt = components[module]
        assert receipt["status"] == "PASS_FRESH_KERNEL_CHECK"
        assert receipt["source_sha256"] == row["sha256"] == origins[module]["sha256"]
        assert receipt["cached_object"] and receipt["source_and_imports_stable"]
        source = work / "source-store" / (row["sha256"] + ".lean")
        assert sha(source) == row["sha256"]
        imports = lean_imports(source.read_text())
        assert imports == row["imports"] == origins[module]["imports"]
        destination = source_evidence / "source-store" / source.name
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            assert sha(destination) == row["sha256"]
        else:
            shutil.copyfile(source, destination)
        sources.append({"module": module, "source_sha256": row["sha256"], "imports": imports,
            "evidence_path": str(destination.relative_to(source_evidence)),
            "original_contexts": origins[module]["origins"]})
    closure = {"status": "EXACT_ACCEPTED_1433_SOURCE_AND_IMPORT_CLOSURE",
        "graph_sha256": final["graph_sha256"], "modules": sources,
        "source_bodies_or_imports_changed": False, "historical_contexts_remain_isolated": True}
    save(source_evidence / "SOURCE-IMPORT-CLOSURE.json", closure)
    shutil.copyfile(Path(__file__), source_evidence / "SUMMARIZER.py")
    import_parser = ROOT / "scripts/assemble_public.py"
    shutil.copyfile(import_parser, source_evidence / "IMPORT-PARSER.py")
    copied = [{"path": str(path.relative_to(source_evidence)), "sha256": sha(path), "bytes": path.stat().st_size}
        for path in sorted((source_evidence / "source-store").glob("*.lean"))]
    save(source_evidence / "SOURCE-PRESERVATION-MANIFEST.json", {"status": "PASS_EXACT_SOURCE_BYTE_FREEZE",
        "files": copied, "module_count": 1433, "source_import_closure_sha256": sha(source_evidence / "SOURCE-IMPORT-CLOSURE.json")})
    certificate = {"status": "PASS_1433_AUTHENTICATED_COMPONENTS_AND_FRESH_COMPLETE_OWNED_AUDIT",
        "workspace": str(work), "actual_run": result["actual_run"], "evidence": result["evidence"],
        "source_evidence": str(source_evidence.relative_to(ROOT)),
        "graph_sha256": final["graph_sha256"], "compiler_sha256": COMPILER,
        "mathlib_commit": final["mathlib_commit"], "native_runtime_digest": final["native_runtime_digest"],
        "compiler_and_native_final_rehash_stable": True, "trust_level": 0, "kernel_checking": True,
        "closure_modules": 1433, "authenticated_exact_component_admissions": 1433,
        "fresh_components_in_this_run": 0, "fresh_aggregate_and_complete_audit": True,
        "owned_declarations": audit["declaration_count"], "owned_theorems": audit["theorem_declaration_count"],
        "owned_axioms": [], "nonstandard_axiom_rows": [], "missing_modules": [],
        "current_fresh_1340_context_retained": True, "additional_published_modules": prep["additional_published_modules"],
        "later_current_modules_outside_frozen_canonical": prep["later_current_modules_outside_frozen_canonical"],
        "original_current_graph_sha256": prep["original_current_graph_sha256"],
        "original_published_graph_sha256": prep["original_published_graph_sha256"],
        "preparation_sha256": sha(prep_path), "preserved_result_sha256": sha(result_path),
        "source_import_closure_sha256": sha(source_evidence / "SOURCE-IMPORT-CLOSURE.json"),
        "source_preservation_manifest_sha256": sha(source_evidence / "SOURCE-PRESERVATION-MANIFEST.json"),
        "preservation_manifest_sha256": sha(evidence / "PRESERVATION-MANIFEST.json"),
        "final_receipt_sha256": sha(evidence / "FINAL-RECEIPT.json"), "target_result_sha256": sha(evidence / target_path),
        "complete_owned_audit": rows[audit_relative], "sources_and_imports_changed": False,
        "summarizer_sha256": sha(Path(__file__)), "import_parser_sha256": sha(import_parser),
        "compiled_artifact_bytes_distributed": False,
        "fresh_all_sources_claimed": False, "historical_graphs_or_receipts_overwritten": False,
        "scope": "A new coherent composition of the earlier fresh1340 and published canonical1411 exact public sources, with authenticated component artifacts and a fresh combined aggregate plus full owned audit. The frozen53 historical-profile replay and its bounded resource exception stay separately attributed. This is compilation and proof-context integration, not missing scientific providers, generic Rust refinement or G1-G7 master closure."}
    save(source_evidence / "CERTIFICATE.json", certificate)
    save(ROOT / "LATEST-PUBLIC-UNION-CERTIFICATE.json", certificate)
    print(json.dumps({k: certificate[k] for k in ["status", "closure_modules", "owned_declarations", "owned_theorems", "source_evidence"]}))


if __name__ == "__main__":
    main()
