#!/usr/bin/env python3
"""Review the preserved 53-profile replay and separate exact-context retry."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def identity(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": digest(raw)}


def review(name, original_policy):
    certificate_path = PACKET / "lean" / name
    certificate = json.loads(certificate_path.read_text())
    evidence = PACKET / "lean" / certificate["evidence"]
    distributions = json.loads((evidence / "COMPRESSED-DISTRIBUTIONS.json").read_text())["distributions"]
    lookup = {row["restored_path"]: row for row in distributions}
    errors, profiles = [], []

    def raw(relative):
        path = evidence / relative
        if path.is_file():
            return path.read_bytes()
        return gzip.decompress((evidence / lookup[relative]["path"]).read_bytes())

    for pin in certificate["copied_evidence_files"]:
        if identity(evidence / pin["path"]) != {key: pin[key] for key in ("bytes", "sha256")}:
            errors.append("Copied identity: " + pin["path"])
    for row in distributions:
        decoded = gzip.decompress((evidence / row["path"]).read_bytes())
        if len(decoded) != row["restored_bytes"] or digest(decoded) != row["restored_sha256"]:
            errors.append("Lossless distribution: " + row["path"])
    restored = 0
    if original_policy:
        manifest_path = evidence / "RESTORE-MANIFEST.json"
        if identity(manifest_path)["sha256"] != certificate["restore_manifest_sha256"]:
            errors.append("Restore manifest identity")
        restore = json.loads(manifest_path.read_text())
        for row in restore["files"]:
            distribution = row["distribution"]
            content = (evidence / distribution["path"]).read_bytes()
            if distribution.get("encoding") == "gzip":
                content = gzip.decompress(content)
            if len(content) != row["original_bytes"] or digest(content) != row["original_sha256"]:
                errors.append("Original snapshot restoration: " + row["original_path"])
            restored += 1
        if restored != restore["original_snapshot_files"]:
            errors.append("Incomplete original snapshot restoration")
        if identity(evidence / "ORIGINAL-CERTIFICATE.json")["sha256"] != certificate["original_certificate_sha256"]:
            errors.append("Original certificate identity")
    closure_path = evidence / "SOURCE-IMPORT-CLOSURE.json"
    if identity(closure_path)["sha256"] != certificate["source_import_closure_sha256"]:
        errors.append("Source/import closure identity")
    closure = json.loads(closure_path.read_text())
    for source in closure["module_source_pairs"]:
        if digest((evidence / source["path"]).read_bytes()) != source["source_sha256"]:
            errors.append("Frozen source identity: " + source["module"])
    final_raw = raw("run/FINAL-RECEIPT.json")
    final = json.loads(final_raw)
    if digest(final_raw) != certificate["final_receipt_sha256"]:
        errors.append("Final receipt identity")
    if not (final["kernel_checking"] and final["trust_level"] == 0
            and final["native_runtime_final_rehash_stable"]
            and final["compiler_sha256"] == certificate["compiler_sha256"]
            and not final["fresh_all_sources_claimed"]):
        errors.append("Kernel/runtime/freshness conditions")
    for profile in certificate["profile_results"]:
        target_raw = raw("run/" + profile["target_result_path"])
        target = json.loads(target_raw)
        checks = {"target_identity": digest(target_raw) == profile["target_result_sha256"],
                  "status": target["status"] == profile["status"]}
        if profile["status"] == "PASS":
            audit_raw = raw("run/" + profile["complete_audit_path"])
            audit = json.loads(audit_raw)
            checks.update({
                "audit_identity": digest(audit_raw) == profile["complete_audit_sha256"],
                "complete_owned_counts": len(audit["selected_modules"]) == profile["modules"]
                    == target["closure_modules"] and audit["declaration_count"]
                    == profile["owned_declarations"] == target["declarations"]
                    and audit["theorem_declaration_count"] == profile["owned_theorems"] == target["theorems"],
                "no_owned_or_nonstandard_axioms": not audit["owned_axioms"]
                    and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
                "fresh_checked_aggregate_and_audit": all(row["status"] == "PASS_FRESH_KERNEL_CHECK"
                    and row["exit_code"] == 0 and row["source_and_imports_stable"]
                    and "-t0" in row["command"] and "-Ddebug.skipKernelTC=false" in row["command"]
                    and row["compiler_sha256"] == certificate["compiler_sha256"]
                    for row in (target["aggregate_receipt"], target["audit_receipt"])),
            })
        else:
            checks["original_failure_preserved"] = original_policy and profile["target"] == "825/base"
        errors.extend(profile["target"] + ": " + key for key, passed in checks.items() if not passed)
        profiles.append({"target": profile["target"], "status": profile["status"],
                         "modules": profile["modules"], "checks": checks})
    statuses = {row["target"]: row["status"] for row in profiles}
    expected_status = "PARTIAL_ORIGINAL_POLICY_REPLAY" if original_policy else "PASS_EXACT_337_CONTEXT_WITH_SEPARATE_6GIB_EXCEPTION"
    if certificate["status"] != expected_status:
        errors.append("Policy status")
    if original_policy and not (certificate["required_profiles"] == 53
            and certificate["passed_profiles"] == 52 and statuses["825/base"] == "FAILED_OR_BLOCKED"
            and not certificate["resource_policy_changed"]):
        errors.append("Original 52/53 policy boundary")
    if not original_policy:
        target = json.loads(raw("run/targets/825_base/RESULT.json"))
        if not (certificate["required_profiles"] == certificate["passed_profiles"] == 1
                and target["closure_modules"] == 337 and certificate["resource_policy_changed"]
                and all(row["cap_memory_mib"] == 6144 and row["cap_seconds"] == 180
                        for row in (target["aggregate_receipt"], target["audit_receipt"]))):
            errors.append("Separate exact 337 resource exception")
    return {"certificate": identity(certificate_path), "pass": not errors, "errors": errors,
            "copied_identities": len(certificate["copied_evidence_files"]),
            "lossless_distributions": len(distributions), "original_files_restorable": restored,
            "source_versions_checked": len(closure["module_source_pairs"]), "profiles": profiles}


def main():
    original = review("PUBLISHED53-PORTABLE-CERTIFICATE.json", True)
    retry = review("BASE-RESOURCE-EXCEPTION-CERTIFICATE.json", False)
    receipt = {"schema": "published53_saved_evidence_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": original["pass"] and retry["pass"], "original_policy": original,
        "separate_337_exception": retry, "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Independent preserved/distributed byte, source, kernel receipt and complete owned-audit review. Original policy remains 52/53; the last exact context passes a separate6GiB retry. No new compiler run, fresh-all-component claim or G6/G7 master closure."}
    (PACKET / "quality/PUBLISHED53-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "original_errors": original["errors"],
        "retry_errors": retry["errors"], "original_files_restorable": original["original_files_restorable"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
