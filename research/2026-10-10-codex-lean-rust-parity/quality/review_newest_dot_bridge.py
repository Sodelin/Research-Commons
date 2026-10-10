#!/usr/bin/env python3
"""Check the public source/audit lineage; do not reuse projected host receipts."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path

from review_support_join import PACKET, identity, read

REPO = PACKET.parents[1]
DOT = REPO / "research/2026-10-10-dot-modular-lean-reuse-handoff-1448z/g3-fixed-residue-critical-bridge-1522z"
COMPILER = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"


def main():
    manifest = read(DOT / "PUBLICATION-MANIFEST.json")
    source_manifest = read(DOT / "SOURCE-MANIFEST.json")
    additive = read(DOT / "ADDITIVE-PROFILE.json")
    selected = additive["source_scope"]
    result = read(DOT / "evidence/RESULT.json")
    audit_path = DOT / "evidence/AUDIT-RESULT.json"
    audit = read(audit_path)
    parser_certificate = read(PACKET / "lean/LATEST-PUBLIC-UNION-CERTIFICATE.json")
    parser_path = PACKET / "lean" / parser_certificate["source_evidence"] / "IMPORT-PARSER.py"
    assert identity(parser_path)["sha256"] == read(PACKET / "quality/LATEST-UNION-REVIEW.json")["import_parser_sha256"]
    spec = importlib.util.spec_from_file_location("frozen_dot_import_parser", parser_path)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    errors, sources = [], []
    for row in manifest["files"]:
        path = DOT / row["path"]
        observed = identity(path)
        if observed["bytes"] != row["bytes"] or observed["sha256"] != row["sha256"]:
            errors.append("Published bytes: " + row["path"])
        blob = hashlib.sha1(b"blob " + str(row["bytes"]).encode() + b"\0" + path.read_bytes()).hexdigest()
        if blob != row["git_blob_sha"]:
            errors.append("Published Git blob: " + row["path"])
    receipts = {row["module"]: row for row in result["component_receipts"]}
    for row in source_manifest["modules"]:
        source = row["source"]
        path = REPO / source.split("/blob/", 1)[1].split("/", 1)[1] if source.startswith("https://github.com/") else DOT / source
        data = path.read_bytes()
        model = selected["modules"][row["module"]]
        receipt = receipts[row["module"]]
        if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"] or model["sha256"] != row["sha256"] or receipt["source_sha256"] != row["sha256"]:
            errors.append("Source identity: " + row["module"])
        if parser.imports(data.decode()) != row["imports"] or model["imports"] != row["imports"]:
            errors.append("Literal imports: " + row["module"])
        for imported in row["imports"]:
            if imported in receipts and receipt["direct_import_sha256"].get(imported) != receipts[imported]["object_sha256"]:
                errors.append("Projected owned object binding: " + row["module"] + " -> " + imported)
        sources.append({"module": row["module"], "new_source": row["new_source"], "source": identity(path)})
    theorem = "GProgram.G3.CriticalCertificates.actual_fixed_residue_strict_critical_finite"
    declarations = {row["name"]: row for row in audit["declarations"]}
    checks = {
        "public_artifact_count": len(manifest["files"]) == 106,
        "complete_source_graph": source_manifest["source_count"] == len(sources) == len(receipts) == len(result["component_receipts"]) == len(selected["modules"]) == result["closure_modules"] == 70,
        "sixty_four_new_sources": source_manifest["new_source_count"] == sum(row["new_source"] for row in sources) == 64,
        "exact_selected_owned_audit": audit["selected_modules"] == selected["order"] and len(declarations) == len(audit["declarations"]) == audit["declaration_count"] == result["declarations"] == 1087,
        "theorem_count": sum(row["kind"] == "theorem" for row in audit["declarations"]) == audit["theorem_declaration_count"] == result["theorems"] == 788,
        "no_owned_nonstandard_or_missing": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
        "exact_audit_binding": identity(audit_path)["sha256"] == manifest["exact_audit_sha256"] == result["audit_receipt"]["auxiliary_outputs"][0]["sha256"],
        "original_profile_entries_preserved": additive["all_original_profiles_unchanged"],
        "actual_source_theorem_present": theorem in declarations and declarations[theorem]["kind"] == "theorem",
        "projected_kernel_receipt_flags": all(row["status"] == "PASS_FRESH_KERNEL_CHECK" and row["exit_code"] == 0 and row["source_and_imports_stable"] and row["compiler_sha256"] == COMPILER and row["mathlib_commit"] == MATHLIB and row["cap_memory_mib"] == 4096 and row["cap_seconds"] == 180 and "-Ddebug.skipKernelTC=false" in row["command"] and "-t0" in row["command"] for row in [*receipts.values(), result["aggregate_receipt"], result["audit_receipt"]]),
    }
    errors.extend(name for name, ok in checks.items() if not ok)
    answer = {"schema": "newest_dot_public_source_audit_lineage_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "published_files_checked": len(manifest["files"]), "sources": sources,
        "certificate_manifest": identity(DOT / "PUBLICATION-MANIFEST.json"), "selected_profile": identity(DOT / "ADDITIVE-PROFILE.json"),
        "projected_result": identity(DOT / "evidence/RESULT.json"), "exact_owned_audit": identity(audit_path), "reviewer": identity(Path(__file__)),
        "counts": {"modules": 70, "declarations": 1087, "theorem_declarations": 788}, "observed_receipt_status_counts": dict(Counter(row["status"] for row in receipts.values())),
        "scope": "Independent byte/source/literal-import/owned-audit and projected receipt-lineage review of DOT's fixed-residue actual-source theorem. Receipt component statuses describe their original checks; the final DOT run reports9fresh/61authenticated reuse. Projected operational paths, a different host runtime digest and undistributed compiled objects are not usable local cache entries. No local compiler/native run or canonical-union acceptance is inferred. The theorem supplies strict fixed-residue finiteness, not effective critical-point enumeration, source acquisition, general G3/G4 or G6/G7 master closure.",
        "compiler_executed": False, "projected_host_receipts_accepted_as_local_cache": False, "master_complete": False}
    (PACKET / "quality/NEWEST-DOT-BRIDGE-REVIEW.json").write_text(json.dumps(answer, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors[:15], "sources": len(sources), "public_files": len(manifest["files"])}))
    return int(not answer["pass"])


if __name__ == "__main__":
    raise SystemExit(main())
