#!/usr/bin/env python3
"""Authenticate the expanded library context and exact storage transport."""
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path

from review_support_join import PACKET, checked, identity, read

CORE = "13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc"
AUDIT = "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
PREPARER = "5f5a4c31e04b9d3a87f4e2fb2384e23a7cf5a4b5a531024a35caa0b2a00f45c6"
EXCLUDED = {"G6RationalCompressionCertificateFixtureMain", "G7OriginalCompletedCalendarFixtureMain"}
ROOTS = {
    "G6RationalCompressionCertificate": "RATIONAL-COMPRESSION-CERTIFICATE.json",
    "G6RationalCompressionCertificateFixture": "RATIONAL-COMPRESSION-FIXTURE-CERTIFICATE.json",
    "G6RationalCompressionCertificateFacts": "RATIONAL-COMPRESSION-FACTS-CERTIFICATE.json",
    "G6RationalCompressionCheckedRows": "RATIONAL-COMPRESSION-CHECKED-ROWS-CERTIFICATE.json",
    "G7OriginalCompletedCalendarFixture": "ORIGINAL-CALENDAR-FIXTURE-CERTIFICATE.json",
    "G7OriginalCompletedCalendarPhases": "ORIGINAL-CALENDAR-PHASES-CERTIFICATE.json",
    "G7OriginalCompletedCalendarRoot": "ORIGINAL-CALENDAR-ROOT-CERTIFICATE.json",
    "G7OriginalCompletedCalendarLaw": "ORIGINAL-CALENDAR-LAW-CERTIFICATE.json",
    "G7NamedCalendarSourceAdmission": "NAMED-CALENDAR-SOURCE-ADMISSION-CERTIFICATE.json",
}


def main():
    cp = PACKET / "lean/INTEGRATED-MODULAR-UNION-CERTIFICATE.json"
    rp = PACKET / "lean/INTEGRATED-MODULAR-UNION-RESULT.json"
    cert, result = read(cp), read(rp)
    evidence = PACKET / "lean" / cert["evidence"]
    graph = read(evidence / "DEPENDENCY-GRAPH.json")
    selected = graph["targets"]["current/connected"]
    target = read(evidence / "targets/current_connected/RESULT.json")
    final, certified = result["final_receipt"], cert["targets"]["current/connected"]
    preparation = read(evidence.parent / "PREPARATION.json")
    old = read(PACKET / "lean/COHERENT-UNION-1463-CERTIFICATE.json")
    public = read(PACKET / "lean/LATEST-PUBLIC-UNION-CERTIFICATE.json")
    parser_path = PACKET / "lean" / public["source_evidence"] / "IMPORT-PARSER.py"
    assert identity(parser_path)["sha256"] == read(PACKET / "quality/LATEST-UNION-REVIEW.json")["import_parser_sha256"]
    spec = importlib.util.spec_from_file_location("frozen_union_parser", parser_path)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    errors = []
    for row in result["preserved_files"]:
        if identity(evidence / row["path"]) != {k: row[k] for k in ("bytes", "sha256")}:
            errors.append("Preserved artifact: " + row["path"])
    components = {row["module"]: row for row in target["component_receipts"]}
    for name, model in selected["modules"].items():
        source = evidence.parent / "sources" / (name.replace(".", "/") + ".lean")
        row = components[name]
        if identity(source)["sha256"] != model["sha256"] or model["sha256"] != cert["source_pins"][name] or parser.imports(source.read_text()) != model["imports"]:
            errors.append("Source/import context: " + name)
        if not checked(row, final["compiler_sha256"], final["native_runtime_digest"]) or row["source_sha256"] != model["sha256"]:
            errors.append("Authenticated component: " + name)
        for imported in model["imports"]:
            if imported in components and row["direct_import_sha256"].get(imported) != components[imported]["object_sha256"]:
                errors.append("Compiled import: " + name + " -> " + imported)
    raw = gzip.decompress((evidence / certified["audit_distribution"]).read_bytes())
    audit = json.loads(raw)
    expected_root_pins = {name: read(PACKET / "lean" / filename)["source_pins"][name] for name, filename in ROOTS.items()}
    checks = {
        "all_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "complete_coherent_library_context": len(components) == len(target["component_receipts"]) == len(selected["order"]) == len(selected["modules"]) == target["closure_modules"] == 1487
            and audit["selected_modules"] == selected["order"] and len(set(audit["selected_modules"])) == 1487,
        "complete_unique_owned_inventory": audit["declaration_count"] == len(audit["declarations"]) == len({r["name"] for r in audit["declarations"]}) == target["declarations"] == certified["owned_declarations"]
            and audit["theorem_declaration_count"] == sum(r["kind"] == "theorem" for r in audit["declarations"]) == target["theorems"] == certified["owned_theorems"]
            and all(r["module"] in components for r in audit["declarations"]),
        "no_owned_nonstandard_or_missing": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
        "audit_binding": hashlib.sha256(raw).hexdigest() == certified["audit_raw_sha256"] == target["audit_receipt"]["auxiliary_outputs"][0]["sha256"],
        "fresh_aggregate_and_audit": all(checked(target[k], final["compiler_sha256"], final["native_runtime_digest"])
            and Path(target[k]["receipt_directory"]).is_relative_to(Path(result["actual_run"])) for k in ("aggregate_receipt", "audit_receipt")),
        "all_prior1463_sources_retained": all(cert["source_pins"].get(name) == pin for name, pin in old["source_pins"].items()),
        "all_new_accepted_library_roots_retained": all(cert["source_pins"].get(name) == pin for name, pin in expected_root_pins.items()),
        "separate_global_entrypoints_excluded": not (EXCLUDED & set(components)),
        "explicit_reuse_only": final["counts"] == cert["counts"] == {"cache_reuse": 1487} and not final["fresh_all_sources_claimed"],
        "stable_kernel_runtime": final["trust_level"] == 0 and final["kernel_checking"] and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "context_preservation_binding": cert["actual_run"] == result["actual_run"] and identity(evidence / "DEPENDENCY-GRAPH.json")["sha256"] == cert["graph_sha256"] == final["graph_sha256"]
            and identity(evidence / "PRESERVATION-MANIFEST.json")["sha256"] == cert["preservation_manifest_sha256"],
        "strict_core_and_namespace_policy": preparation["builder_sha256"] == CORE and preparation["audit_template_sha256"] == AUDIT
            and not preparation["namespace_adapter_derivation"]["compiler_kernel_cache_and_resource_policies_changed"]
            and preparation["namespace_adapter_derivation"]["exact_owned_mathlib_source_pins"] == read(PACKET / "lean/INTEGRATION_CONNECTED-1489-COPY-ISOLATED-PREPARATION.json")["namespace_adapter_derivation"]["exact_owned_mathlib_source_pins"],
        "history_and_science_not_promoted": not cert["historical_evidence_or_scientific_gates_promoted"] and not result["original_attempts_overwritten"] and not result["compiled_artifact_bytes_distributed"],
    }
    errors.extend(name for name, ok in checks.items() if not ok)
    transport = review_transport(preparation, final)
    errors.extend(transport["errors"])
    failed_path = PACKET / "lean/INTEGRATED-MODULAR-UNION-1489-FAILED-RESULT.json"
    failed = read(failed_path)
    assert identity(failed_path)["sha256"] == "f7702651e818e6118e87d9b9277ad628e2848d3641544b388a81a3dd3ce2b8b5"
    failed_evidence = PACKET / "lean" / failed["evidence"]
    for row in failed["preserved_files"]:
        if identity(failed_evidence / row["path"]) != {k: row[k] for k in ("bytes", "sha256")}:
            errors.append("Failed1489 evidence: " + row["path"])
    answer = {"schema": "integrated1487_library_saved_root_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "transport": transport,
        "source_modules_checked": len(components), "preserved_artifacts_checked": len(result["preserved_files"]),
        "declarations": audit["declaration_count"], "theorem_declarations": audit["theorem_declaration_count"],
        "accepted_new_root_pins": expected_root_pins, "certificate": identity(cp), "result": identity(rp),
        "failed1489_result": identity(failed_path), "failed1489_artifacts_checked": len(failed["preserved_files"]),
        "reviewer": identity(Path(__file__)), "import_parser": identity(parser_path),
        "scope": "One coherent1487-module library source/import/artifact context, prior1463 sources unchanged, nine new accepted library roots retained. Components use authenticated earlier kernel checks; aggregate and complete ownership audit are fresh. Storage aliases preserve exact receipt paths/bytes/keys and original, staged and installed companions. The two fixture executables retain separate accepted proof/evaluation contexts because their global main names collide. No universal native refinement, full source census, timed-observation theorem or G6/G7 master closure is inferred.",
        "master_complete": False, "general_native_refinement_inferred": False}
    (PACKET / "quality/INTEGRATED-LIBRARY-UNION-REVIEW.json").write_text(json.dumps(answer, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors[:20], "modules": len(components), "declarations": answer["declarations"], "theorems": answer["theorem_declarations"], "transport_files_rehashed": transport["files_rehashed"]}))
    return not answer["pass"]


def review_transport(preparation, final):
    derivation = preparation["cache_install_transport_derivation"]
    ev = PACKET / "lean" / derivation["evidence"]
    errors = []
    pins = {"PREPARER.py": derivation["preparer_sha256"], "ORIGINAL-NAMESPACE-OVERLAY.py": derivation["original_namespace_wrapper_sha256"],
        "ORIGINAL-AUTHENTICATED-OVERLAY.py": derivation["original_authenticated_wrapper_sha256"], "DERIVED-NAMESPACE-OVERLAY.py": derivation["derived_namespace_wrapper_sha256"],
        "DERIVED-AUTHENTICATED-OVERLAY.py": derivation["derived_authenticated_wrapper_sha256"], "CACHE-INSTALL-ALIASES.json": derivation["alias_manifest_sha256"]}
    for name, pin in pins.items():
        if identity(ev / name)["sha256"] != pin:
            errors.append("Transport derivation: " + name)
    tree = ast.parse((ev / "PREPARER.py").read_text())
    constants = {node.targets[0].id: ast.literal_eval(node.value) for node in tree.body
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name) and isinstance(node.value, ast.Constant)}
    assert derivation["preparer_sha256"] == PREPARER
    before = (ev / "ORIGINAL-NAMESPACE-OVERLAY.py").read_text()
    start, end = before.index("    def install(self, base, out, expected):"), before.index("    def dependencies(")
    expected = before[:start] + constants["INSTALL_METHOD"] + before[end:]
    expected = expected.replace("sha = lambda p:", "CACHE_INSTALL_MANIFEST_SHA = " + repr(derivation["alias_manifest_sha256"]) + "\nsha = lambda p:")
    assert expected == (ev / "DERIVED-NAMESPACE-OVERLAY.py").read_text()
    assert (ev / "ORIGINAL-AUTHENTICATED-OVERLAY.py").read_text().replace(derivation["original_namespace_wrapper_sha256"], derivation["derived_namespace_wrapper_sha256"]) == (ev / "DERIVED-AUTHENTICATED-OVERLAY.py").read_text()
    assert derivation["core_builder_sha256"] == CORE and derivation["audit_template_sha256"] == AUDIT
    assert not any(derivation[k] for k in ("original_paths_keys_receipt_bytes_changed", "source_or_namespace_guards_changed", "kernel_compiler_flags_caps_or_audit_policy_changed", "native_or_global_mathlib_files_changed"))
    aliases = read(ev / "CACHE-INSTALL-ALIASES.json")
    post_path = PACKET / "lean/CACHE-TRANSPORT-POST-RUN-REHASH.json"
    post = read(post_path)
    assert post["run"] == final["run"] and post["graph_sha256"] == final["graph_sha256"]
    assert post["install_alias_manifest_sha256"] == derivation["alias_manifest_sha256"]
    assert post["status"] == "PASS_POST_BUILDER_ORIGINAL_STAGED_INSTALLED_CACHE_REHASH"
    assert len(post["records"]) == post["selected_modules_verified"] == len(aliases["entries"]) == 1487
    records = {r["module"]: r for r in post["records"]}
    assert len(records) == 1487 and set(records) == {r["module"] for r in aliases["entries"]}
    seen = {}

    def rehash(path, pin):
        path = Path(path)
        if path not in seen:
            seen[path] = identity(path)["sha256"]
        if seen[path] != pin:
            errors.append("Original/staged/installed companion: " + str(path))

    suffixes = [".olean", ".olean.private", ".olean.server", ".ilean", ".ir"]
    for entry in aliases["entries"]:
        record = records[entry["module"]]
        rehash(entry["original_receipt"], entry["receipt_sha256"])
        rehash(entry["staged_receipt"], entry["receipt_sha256"])
        receipt = read(Path(entry["original_receipt"]))
        assert receipt["cached_object"] == entry["original_cached_object"] and receipt["object_artifacts"] == entry["object_artifacts"]
        assert record["cache_key"] == entry["cache_key"] and record["object_artifacts"] == entry["object_artifacts"]
        assert record["original_cached_object"] == entry["original_cached_object"] and record["staged_cached_object"] == entry["staged_cached_object"]
        for base in (entry["original_cached_object"], entry["staged_cached_object"], record["installed_object"]):
            root = str(base)[:-len(".olean")]
            for suffix in suffixes:
                candidate = Path(root + suffix)
                if suffix in entry["object_artifacts"]:
                    rehash(candidate, entry["object_artifacts"][suffix])
                elif candidate.exists():
                    errors.append("Unexpected companion: " + str(candidate))
    return {"pass": not errors, "errors": errors, "files_rehashed": len(seen), "modules_checked": 1487,
        "derivation": identity(ev / "RECEIPT.json"), "post_run_receipt": identity(post_path),
        "only_exact_storage_install_method_changed": True, "original_receipt_paths_bytes_and_cache_keys_retained": True}


if __name__ == "__main__":
    raise SystemExit(main())
