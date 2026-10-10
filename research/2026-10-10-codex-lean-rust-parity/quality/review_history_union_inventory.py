#!/usr/bin/env python3
"""Check the new owned inventory against its actual complete audit and root review."""
from collections import Counter
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, identity, read


def main():
    certificate_path = PACKET / "lean/HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json"
    inventory_path = PACKET / "lean/HISTORY-ACCEPTED-UNION-1497-OWNED-INVENTORY.json"
    review_path = PACKET / "quality/HISTORY-ACCEPTED-UNION-1497-REVIEW.json"
    certificate, inventory, review = read(certificate_path), read(inventory_path), read(review_path)
    target = certificate["targets"]["current/connected"]
    raw = gzip.decompress((PACKET / "lean" / certificate["evidence"] / target["audit_distribution"]).read_bytes())
    audit = json.loads(raw)
    kinds = Counter(row["kind"] for row in audit["declarations"])
    modules = {name: Counter() for name in audit["selected_modules"]}
    for row in audit["declarations"]:
        modules[row["module"]][row["kind"]] += 1
    checks = {
        "actual_audit_binding": hashlib.sha256(raw).hexdigest() == target["audit_raw_sha256"] == inventory["audit_raw_sha256"],
        "inventory_certificate_binding": identity(certificate_path)["sha256"] == inventory["certificate_sha256"],
        "complete_actual_counts": len(audit["selected_modules"]) == inventory["selected_modules"] == 1497 and len(audit["declarations"]) == inventory["unique_declarations"] == 100764 and kinds["theorem"] == inventory["theorem_declarations"] == 91540,
        "actual_kind_counts": dict(kinds) == inventory["kind_counts"] and dict(modules) == inventory["module_kind_counts"],
        "independently_reviewed_prior_metadata": review["pass"] and review["prior_owned_declarations_compared"] == inventory["prior1487_owned_declarations_checked"] == 100217
            and review["added_owned_declaration_names"] == inventory["added_owned_declarations"] == 547,
        "canonical_prior_subset_identity": inventory["prior1487_canonical_owned_inventory_sha256"] == inventory["current_prior1487_subset_canonical_inventory_sha256"]
            and inventory["prior1487_declaration_names_module_kind_axiom_and_reference_multisets_unchanged"],
        "no_axiom_or_missing_promotion": not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
    }
    errors = [name for name, ok in checks.items() if not ok]
    answer = {"schema": "history1497_owned_inventory_saved_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "certificate": identity(certificate_path), "inventory": identity(inventory_path),
        "root_saved_review": identity(review_path), "kind_counts": dict(kinds), "reviewer": identity(Path(__file__)),
        "scope": "All declaration and per-module kind counts are recomputed from the complete exact audit, including empty owned modules. Prior1487 metadata equality is bound to the independently executed root review. The earlier inventory's pending-review field is historical; this separate result supplies actual independent review without rewriting it. No compiler/native run or master closure follows."}
    (PACKET / "quality/HISTORY-UNION-INVENTORY-REVIEW.json").write_text(json.dumps(answer, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "modules": len(modules), "declarations": len(audit["declarations"])}))
    return int(not answer["pass"])


if __name__ == "__main__":
    raise SystemExit(main())
