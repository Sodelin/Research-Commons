#!/usr/bin/env python3
"""Recheck historical audit pins at their declared snapshot and current providers."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

from review_support_join import PACKET, identity, read

REPO = PACKET.parents[1]
SNAPSHOT = "a8308ca9428ee1234dd86db8ab6e390f79d51e83"


def main():
    design_path = PACKET / "design/HISTORY-ASSEMBLY-AUDIT-20261010T2040Z.json"
    rust_path = PACKET / "rust/evidence/history-runtime-assembly-audit-1/RECEIPT.json"
    design, rust = read(design_path), read(rust_path)
    errors, records, checked = [], [], {}
    rows = [*design["inspected_source_and_evidence_pins"], *rust["files"]]
    for row in rows:
        key = (row["path"], row["sha256"])
        if key in checked:
            continue
        data = (REPO / row["path"]).read_bytes()
        source = "current_file"
        if hashlib.sha256(data).hexdigest() != row["sha256"]:
            # A later upstream merge/navigation revision does not rewrite a dated audit.
            old = subprocess.run(["git", "show", SNAPSHOT + ":" + row["path"]], cwd=REPO, capture_output=True)
            if old.returncode:
                errors.append("No matching historical source: " + row["path"])
                continue
            data, source = old.stdout, "declared_historical_git_snapshot"
        good = len(data) == row["bytes"] and hashlib.sha256(data).hexdigest() == row["sha256"]
        if not good:
            errors.append("Audit source pin: " + row["path"])
        checked[key] = good
        records.append({"path": row["path"], "sha256": row["sha256"], "bytes": len(data), "binding": source, "pass": good})
    for row in [*design["provider_file_hash_bindings"], *design["frozen_map_guards"]]:
        if identity(REPO / row["path"])["sha256"] != row["expected_sha256"] or not row["match"]:
            errors.append("Current provider/frozen map: " + row["path"])
    for name, receipt in [("design", design), ("rust", rust)]:
        if identity(REPO / receipt["note"])["sha256"] != receipt["note_sha256"]:
            errors.append("Audit note identity: " + name)
    checks = {
        "design_static_pass": design["pass"],
        "all65_existing_ids": design["obligation_rows_reviewed"] == len(design["obligation_ids"]) == len(set(design["obligation_ids"])) == 65,
        "all100_provider_bindings_match": design["provider_file_hash_bindings_checked"] == design["provider_hash_matches"] == len(design["provider_file_hash_bindings"]) == 100,
        "rust_static_pass": rust["status"] == "PASS_STATIC_SOURCE_AND_RECEIPT_BINDINGS" and all(row["pass"] for row in rust["static_checks"]),
        "no_historical_execution_reissued": design["compiler_processes_started"] == design["solver_or_native_processes_started"] == design["backend_queries_started"] == 0
            and not rust["execution"]["Lean_execution"] and not rust["execution"]["application_execution"] and not rust["execution"]["builds"] and rust["execution"]["ELF_copies"] == 0,
    }
    errors.extend(name for name, ok in checks.items() if not ok)
    answer = {"schema": "historical_assembly_audit_independent_saved_review_v1", "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "checks": checks, "unique_inspected_file_pins_rechecked": len(records), "records": records,
        "provider_bindings_rechecked": 100, "frozen_maps_rechecked": len(design["frozen_map_guards"]),
        "design_receipt": identity(design_path), "rust_receipt": identity(rust_path), "reviewer": identity(Path(__file__)),
        "scope": "Source hashes and bounded static audit claims are independently rechecked. Historical snapshot bindings are explicitly distinguished from current files changed by later upstream publication/navigation. Every100mapped provider and frozen guard is still required at current exact bytes. This is history/source reconciliation, not re-execution, proof acceptance, complete corpus body coverage or G6/G7 master closure."}
    (PACKET / "quality/HISTORY-RECONCILIATION-REVIEW.json").write_text(json.dumps(answer, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors[:15], "unique_inspected_pins": len(records), "provider_bindings": 100}))
    return int(not answer["pass"])


if __name__ == "__main__":
    raise SystemExit(main())
