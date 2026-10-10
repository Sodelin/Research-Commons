#!/usr/bin/env python3
"""Independently inspect the saved full-epoch proof repair and audit identities."""
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
COMMONS = PACKET.parents[1]


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def declarations(text):
    # These provider files have no nested block comments or declaration strings.
    # This is a textual preservation check, separate from the kernel receipt.
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    pattern = r"^(?:noncomputable\s+)?(?:private\s+)?(def|theorem|lemma)\s+(\w+)\b"
    matches = list(re.finditer(pattern, text, flags=re.M))
    result = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        body = text[match.start():end]
        # Namespace endings after the last declaration are not definition code.
        body = re.split(r"^end(?:\s|$)", body, maxsplit=1, flags=re.M)[0]
        if match[1] != "def":
            body = body.split(":=", 1)[0]
        result[(match[1], match[2])] = body.strip()
    return result


def main():
    result_path = PACKET / "lean/COEFFICIENT-RECOVERY-RESULT.json"
    result = json.loads(result_path.read_text())
    provenance = json.loads((PACKET / "reuse/G7-FULL-EPOCH-REPAIR.json").read_text())
    evidence = PACKET / "lean" / result["evidence"]
    target_path = evidence / "targets/candidate_g7-coefficients/RESULT.json"
    target = json.loads(target_path.read_text())
    errors = []
    checked = []
    for pin in result["preserved_files"]:
        path = evidence / pin["path"]
        observed = identity(path)
        passed = observed == {key: pin[key] for key in ("bytes", "sha256")}
        checked.append({"path": pin["path"], **observed, "pass": passed})
        if not passed:
            errors.append("Preserved identity: " + pin["path"])
    original = COMMONS / provenance["original_source"]
    derivative = COMMONS / provenance["derivative_source"]
    before, after = declarations(original.read_text()), declarations(derivative.read_text())
    changed = [kind + " " + name for (kind, name), body in before.items()
               if after.get((kind, name)) != body]
    if changed:
        errors.append("Changed executable definition or original theorem statement: " + ", ".join(changed))
    root = next(row for row in target["component_receipts"]
                if row["module"] == "G7EffectiveFullEpochCoefficients")
    audit_path = evidence / "attempts/00003-OwnedAudit/work/AUDIT-RESULT.json"
    audit = json.loads(audit_path.read_text())
    final = result["final_receipt"]
    conditions = {
        "target_pass": result["status"] == "PASS_ALL_REQUESTED_TARGETS" and target["status"] == "PASS",
        "current_derivative_matches_fresh_root": identity(derivative)["sha256"] == root["source_sha256"] == provenance["derivative_sha256"],
        "original_source_identity": identity(original)["sha256"] == provenance["original_sha256"],
        "root_fresh_kernel_pass": root["status"] == "PASS_FRESH_KERNEL_CHECK" and root["exit_code"] == 0 and root["source_and_imports_stable"],
        "fresh_aggregate_and_audit": all(target[name]["status"] == "PASS_FRESH_KERNEL_CHECK" and target[name]["source_and_imports_stable"] and target[name]["exit_code"] == 0 for name in ("aggregate_receipt", "audit_receipt")),
        "complete_ownership": len(audit["selected_modules"]) == target["closure_modules"] == 118 and not audit["missing_modules"],
        "no_owned_or_nonstandard_axioms": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"],
        "audit_counts_match": audit["declaration_count"] == target["declarations"] and audit["theorem_declaration_count"] == target["theorems"],
        "trust_zero_kernel_checking": final["trust_level"] == 0 and final["kernel_checking"],
        "stable_compiler_runtime": final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
        "freshness_disclosed": final["counts"] == {"cache_reuse": 117, "fresh_components": 1} and not final["fresh_all_sources_claimed"],
    }
    errors += [name for name, passed in conditions.items() if not passed]
    receipt = {
        "schema": "full_epoch_repair_static_quality_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "conditions": conditions,
        "recorded_result": {"path": str(result_path.relative_to(COMMONS)), **identity(result_path)},
        "original": {"path": provenance["original_source"], **identity(original)},
        "derivative": {"path": provenance["derivative_source"], **identity(derivative)},
        "preserved_artifacts_checked": checked,
        "original_executable_definitions_compared": sum(kind == "def" for kind, name in before),
        "original_theorem_statements_compared": sum(kind != "def" for kind, name in before),
        "declarations": target["declarations"], "theorems": target["theorems"],
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "scope": "Static independent comparison of saved exact artifact identities, textual original definitions/statements and the completed kernel/audit receipts. No competing Lean compiler invocation; no codegen or universal Rust refinement claim."
    }
    output = PACKET / "quality/COEFFICIENT-RECOVERY-REVIEW.json"
    output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "errors", "original_executable_definitions_compared", "original_theorem_statements_compared", "declarations", "theorems")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
