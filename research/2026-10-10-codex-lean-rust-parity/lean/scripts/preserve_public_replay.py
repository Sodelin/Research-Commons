#!/usr/bin/env python3
"""Preserve a completed exact published profile replay, including failures.

This distributes literal source versions, complete owned audits, generated
audit sources, compiler receipts, import bindings and losslessly compressed
loader evidence. Compiled objects and the original run remain in scratch.
"""
from __future__ import annotations
import argparse
import datetime
import json
from pathlib import Path
from check_core import COMPILER, save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = "7ccbd4bca21115de3918331e9b5ea24ab47b610d98f0236b0f1b241d130f309a"
CORE = "f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--base-resource-exception", action="store_true",
                        help="Preserve the separately attributed unchanged337 context retry.")
    args = parser.parse_args()
    work, run = args.workspace.resolve(), args.run.resolve()
    assert run.is_relative_to(work / ".build/runs")
    final_path = run / "FINAL-RECEIPT.json"
    final = json.loads(final_path.read_bytes())
    assert final["status"] in {"INCOMPLETE_TARGET_FAILURES_PRESERVED", "PASS_ALL_REQUESTED_TARGETS"}
    assert final["compiler_sha256"] == COMPILER and final["native_runtime_final_rehash_stable"]
    if args.base_resource_exception:
        identity = json.loads((run / "BASE-RESOURCE-EXCEPTION-IDENTITY.json").read_bytes())
        assert identity["unchanged_published_wrapper_sha256"] == sha(work / "scripts/build_resource_qualified.py") == WRAPPER
        assert identity["new_wrapper_sha256"] == sha(run / "BASE-RESOURCE-EXCEPTION-WRAPPER.py")
        assert identity["graph_sha256"] == final["graph_sha256"] == sha(run / "DEPENDENCY-GRAPH.json")
        assert final["targets_requested"] == ["825/base"] and identity["modules"] == 337
        assert not identity["source_or_import_or_audit_coverage_changes"]
        assert not identity["original_frozen_53_replay_status_overwritten"]
        assert sha(Path(identity["old_failed_receipt"])) == identity["old_failed_receipt_sha256"]
        expected_profiles = 1
    else:
        identity = json.loads((run / "RESOURCE-QUALIFIED-IDENTITY.json").read_bytes())
        assert identity["wrapper_sha256"] == sha(run / "RESOURCE-WRAPPER.py") == WRAPPER
        assert identity["core_builder_sha256"] == CORE
        assert identity["portable_graph_sha256"] == final["graph_sha256"] == sha(run / "DEPENDENCY-GRAPH.json")
        assert identity["required_targets"] == final["targets_requested"]
        expected_profiles = 53
    assert sha(run / "BUILDER.py") == CORE
    assert len(final["targets_requested"]) == expected_profiles
    assert sha(Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")) == COMPILER
    graph = json.loads((run / "DEPENDENCY-GRAPH.json").read_bytes())
    profiles, selected = [], {}
    for name in final["targets_requested"]:
        item = graph["targets"][name]
        target = run / "targets" / name.replace("/", "_") / "RESULT.json"
        result = json.loads(target.read_bytes())
        assert result["target"] == name
        for module in item["order"]:
            row = item["modules"][module]
            key = (module, row["sha256"])
            if key in selected:
                assert selected[key]["imports"] == row["imports"]
            else:
                selected[key] = row
        profile = {"target": name, "status": result["status"], "modules": len(item["order"]),
                   "target_result_path": str(target.relative_to(run)), "target_result_sha256": sha(target)}
        if name in final["targets_passed"]:
            assert result["status"] == "PASS"
            for key in ("aggregate_receipt", "audit_receipt"):
                assert result[key]["status"] == "PASS_FRESH_KERNEL_CHECK"
                assert result[key]["source_and_imports_stable"]
                assert result[key]["native_initialized_libraries_bound"]
            audit_path = Path(result["audit_receipt"]["audit_output"])
            audit = json.loads(audit_path.read_bytes())
            assert audit["selected_modules"] == item["order"]
            assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
            profile.update({"owned_declarations": audit["declaration_count"],
                            "owned_theorems": audit["theorem_declaration_count"],
                            "complete_audit_path": str(audit_path.relative_to(run)),
                            "complete_audit_sha256": sha(audit_path),
                            "complete_audit_raw_bytes": audit_path.stat().st_size,
                            "aggregate_memory_mib": result["aggregate_receipt"]["cap_memory_mib"],
                            "audit_memory_mib": result["audit_receipt"]["cap_memory_mib"]})
        else:
            assert result["status"] == "FAILED_OR_BLOCKED"
            profile["failure"] = result["error"]
        profiles.append(profile)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / ("evidence/published53-resource-exception" if args.base_resource_exception else "evidence/published53") / stamp
    evidence.mkdir(parents=True)
    files = []
    protected = {p: sha(p) for p in run.rglob("*") if p.is_file() and
                 p.name in {"receipt.json", "RESULT.json", "FINAL-RECEIPT.json"}}
    for source in sorted(run.rglob("*")):
        if not source.is_file() or source.is_symlink():
            continue
        relative = source.relative_to(run)
        if "objects" in relative.parts or source.suffix in {".olean", ".ilean", ".ir", ".private", ".server"}:
            continue
        files.append(distribute_file(source, evidence, Path("run") / relative,
            force_gzip=source.name.startswith("NATIVE-LOADER.") or source.name in {
                "AUDIT-RESULT.json", "ACTUAL-IMPORTED-ARTIFACTS.json"}
                or (source.name == "RESULT.json" and source.stat().st_size > 1_000_000)))
    source_rows = []
    for (module, digest), row in sorted(selected.items()):
        source = work / "source-store" / (digest + ".lean")
        assert sha(source) == digest
        relative = Path("sources") / (digest + ".lean")
        destination = evidence / relative
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(source.read_bytes())
        assert sha(destination) == digest
        source_rows.append({"module": module, "source_sha256": digest, "imports": row["imports"],
                            "path": str(relative)})
    assert all(sha(path) == digest for path, digest in protected.items())
    assert sha(Path("/workspace/toolchains/lean-4.33.1-linux/bin/lean")) == COMPILER
    save(evidence / "SOURCE-IMPORT-CLOSURE.json", {"status": "EXACT_REQUIRED_PROFILE_SOURCE_VERSIONS",
         "graph_sha256": final["graph_sha256"], "module_source_pairs": source_rows})
    distributions = [row for row in files if row.get("encoding") == "gzip"]
    save(evidence / "COMPRESSED-DISTRIBUTIONS.json", {"status": "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION",
         "distributions": distributions, "original_run_unchanged": True,
         "restore_command": "python3 scripts/restore_distributed_evidence.py MANIFEST --output DESTINATION"})
    status = "PARTIAL_ORIGINAL_POLICY_REPLAY" if len(final["targets_passed"]) < expected_profiles else "PASS_ORIGINAL_POLICY_53_PROFILE_REPLAY"
    if args.base_resource_exception:
        status = "PASS_EXACT_337_CONTEXT_WITH_SEPARATE_6GIB_EXCEPTION" if final["targets_passed"] == ["825/base"] else "INCOMPLETE_EXCEPTION_FAILURE_PRESERVED"
    certificate = {"status": status, "actual_run": str(run),
         "workspace": str(work), "evidence": str(evidence.relative_to(ROOT)),
         "original_final_status": final["status"], "required_profiles": expected_profiles,
         "passed_profiles": len(final["targets_passed"]), "profile_results": profiles,
         "component_events": final["counts"], "unique_required_module_source_pairs": len(source_rows),
         "counts_not_additive_across_overlapping_profiles": True,
         "graph_sha256": final["graph_sha256"], "compiler_sha256": COMPILER,
         "mathlib_commit": final["mathlib_commit"], "native_runtime_digest": final["native_runtime_digest"],
         "qualified_wrapper_sha256": WRAPPER, "core_builder_sha256": CORE,
         "final_receipt_sha256": sha(final_path), "copied_evidence_files": files,
         "compressed_distributions_manifest_sha256": sha(evidence / "COMPRESSED-DISTRIBUTIONS.json"),
         "source_import_closure_sha256": sha(evidence / "SOURCE-IMPORT-CLOSURE.json"),
         "original_receipt_and_result_bytes_final_stable": True,
         "compiled_artifact_bytes_distributed": False, "resource_policy_changed": args.base_resource_exception,
         "resource_identity": identity, "preserver_sha256": sha(Path(__file__)),
         "scope": "Exact published required53 source contexts under the unchanged original qualified policy. Failed profiles remain failed here; a later separately attributed resource retry cannot overwrite this status. Historical and current cached components are identified individually, so this is not an all-source-fresh claim or scientific master closure."}
    save(evidence / "CERTIFICATE.json", certificate)
    save(ROOT / ("BASE-RESOURCE-EXCEPTION-CERTIFICATE.json" if args.base_resource_exception else "PUBLISHED53-CERTIFICATE.json"), certificate)
    print(json.dumps({k: certificate[k] for k in ["status", "passed_profiles", "required_profiles", "component_events", "evidence"]}))


if __name__ == "__main__":
    main()
