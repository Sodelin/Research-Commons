#!/usr/bin/env python3
"""Independently compare all prior owned declarations with the expanded audit."""
from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path

from review_support_join import PACKET, identity, read


def load_audit(name):
    path = PACKET / "lean" / name
    certificate = read(path)
    target = certificate["targets"]["current/connected"]
    raw = gzip.decompress((PACKET / "lean" / certificate["evidence"] / target["audit_distribution"]).read_bytes())
    assert hashlib.sha256(raw).hexdigest() == target["audit_raw_sha256"]
    audit = json.loads(raw)
    return path, audit


def main():
    old_path, old = load_audit("COHERENT-UNION-1463-CERTIFICATE.json")
    new_path, new = load_audit("INTEGRATED-MODULAR-UNION-CERTIFICATE.json")
    prior = {r["name"]: r for r in old["declarations"]}
    current = {r["name"]: r for r in new["declarations"]}
    errors = []
    for name, row in prior.items():
        observed = current.get(name)
        if observed is None:
            errors.append("Missing prior declaration: " + name)
            continue
        if set(observed) != set(row) or any(
            Counter(row[k]) != Counter(observed[k]) if isinstance(row[k], list) else row[k] != observed[k]
            for k in row):
            errors.append("Prior declaration metadata changed: " + name)
    kinds = Counter(r["kind"] for r in new["declarations"])
    module_kinds = defaultdict(Counter)
    for row in new["declarations"]:
        module_kinds[row["module"]][row["kind"]] += 1
    supplement_path = PACKET / "lean/INTEGRATED-MODULAR-UNION-OWNED-INVENTORY.json"
    supplement = read(supplement_path)
    checks = {
        "unique_complete_old_and_new_names": len(prior) == len(old["declarations"]) == 99149
            and len(current) == len(new["declarations"]) == 100217,
        "prior_metadata_retained": not errors,
        "kind_inventory_matches_actual_audit": dict(kinds) == supplement["kind_counts"]
            and kinds["theorem"] == new["theorem_declaration_count"] == 91274,
        "module_kind_inventory_matches_actual_audit": dict(module_kinds) == supplement["module_kind_counts"],
        "supplement_binds_certificate_and_root_review": supplement["certificate_sha256"] == identity(new_path)["sha256"]
            and supplement["root_independent_review_sha256"] == identity(PACKET / "quality/INTEGRATED-LIBRARY-UNION-REVIEW.json")["sha256"],
    }
    errors.extend(k for k, ok in checks.items() if not ok)
    answer = {"schema": "expanded_union_prior_owned_inventory_saved_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "prior_declarations_checked": len(prior),
        "current_declarations_checked": len(current), "added_declaration_names": len(set(current) - set(prior)),
        "kind_counts": dict(kinds), "old_certificate": identity(old_path), "new_certificate": identity(new_path),
        "supplement": identity(supplement_path), "reviewer": identity(Path(__file__)),
        "scope": "Exact names, module/kind and every recorded metadata field are compared across the old and new owned audits; reference/axiom lists are compared as multisets preserving multiplicity. Raw source, object and kernel bindings remain supplied by the separate accepted root union review. No compiler/native execution, proof completion percentage or master closure is inferred."}
    (PACKET / "quality/UNION-INVENTORY-DELTA-REVIEW.json").write_text(json.dumps(answer, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors[:10], "prior": len(prior), "current": len(current), "added": answer["added_declaration_names"]}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
