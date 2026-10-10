#!/usr/bin/env python3
"""Independently recount delivered audit JSON and verify packet identities.

This performs static integrity/consistency checks. It does not execute Lean,
authenticate unavailable raw receipts, or establish scientific master closure.
"""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(packet):
    manifest = json.loads((packet / "MANIFEST.json").read_text())
    count = 0
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe manifest path: {relative}")
        path = packet / relative
        content = path.read_bytes()
        assert len(content) == entry["bytes"], path
        assert hashlib.sha256(content).hexdigest() == entry["sha256"], path
        if "git_blob_sha1" in entry:
            blob = b"blob " + str(len(content)).encode() + b"\0" + content
            assert hashlib.sha1(blob).hexdigest() == entry["git_blob_sha1"], path
        count += 1
    return count


def recount_audit(path):
    audit = json.loads(path.read_text())
    rows = audit["declarations"]
    names = [row["name"] for row in rows]
    modules = set(audit["selected_modules"])
    assert len(modules) == len(audit["selected_modules"]), path
    assert len(set(names)) == len(names), path
    assert len(rows) == audit["declaration_count"], path
    assert sum(row["kind"] == "theorem" for row in rows) == audit["theorem_declaration_count"], path
    assert not audit["owned_axioms"], path
    assert not audit["nonstandard_axiom_rows"], path
    assert not audit["missing_modules"], path
    assert all(row["module"] in modules for row in rows), path
    for row in rows:
        assert row["kind"] != "axiom", row["name"]
        assert set(row["axioms"]) <= ALLOWED_AXIOMS, row["name"]
    return {
        "path": str(path.relative_to(ROOT)),
        "sha256": digest(path),
        "modules": len(modules),
        "declarations": len(rows),
        "theorems": sum(row["kind"] == "theorem" for row in rows),
        "owned_axioms": 0,
        "nonstandard_axiom_rows": 0,
        "unique_owned_names": True,
    }


def check_connected():
    packet = ROOT / "research/2026-10-10-dot-connected-53-qualified-certificate-0842z"
    certificate = json.loads((packet / "CERTIFICATE.json").read_text())
    pins = json.loads((packet / "TARGET-RESULT-PINS.json").read_text())
    rows = pins["rows"]
    assert certificate["required_targets"] == pins["target_count"] == len(rows) == 53
    assert sum(certificate["union_partition"]) == len(rows)
    assert len({row["target"] for row in rows}) == len(rows)
    assert pins["original_final_reauthentication_sha256"] == certificate["final_reauthentication_sha256"]
    assert all(row["status"] == "PASS" for row in rows)
    assert certificate["owned_axioms"] == certificate["nonstandard_axiom_rows"] == certificate["missing_selected_modules"] == 0
    assert not certificate["single_fresh_invocation_claimed"]
    assert not certificate["fresh_public_layout_reproduction_claimed"]
    for row in rows:
        assert row["current_target_run_fresh_components"] + row["authenticated_other_run_components"] == row["component_count"], row["target"]
        for kind in ("aggregate", "complete_owned_audit"):
            operation = row[kind]
            assert operation["exit_code"] == 0, row["target"]
            assert "-t0" in operation["kernel_flags"], row["target"]
            assert "-Ddebug.skipKernelTC=false" in operation["kernel_flags"], row["target"]
    return {"required_profiles": len(rows), "certificate_sha256": digest(packet / "CERTIFICATE.json"), "target_pins_sha256": digest(packet / "TARGET-RESULT-PINS.json"), "verification": "STATIC_RECOUNT_OF_PUBLISHED_RECEIPT_PROJECTIONS"}


def main():
    cell = ROOT / "research/2026-10-10-dot-g6-completed-cell-tv-0258z"
    bridge = ROOT / "research/2026-10-10-dot-g6-protected-bin-bridge-0912z"
    result = {
        "status": "STATIC_BASELINE_REVIEW_PASS",
        "scope": "Published file identities, declaration/axiom census and receipt consistency only; no compiler replay or master closure.",
        "connected": check_connected(),
        "manifest_files_checked": {cell.name: check_manifest(cell), bridge.name: check_manifest(bridge)},
        "audits": [recount_audit(cell / "evidence/cell/AUDIT-RESULT.json"), recount_audit(cell / "evidence/tv/AUDIT-RESULT.json"), recount_audit(bridge / "evidence/bridge/AUDIT-RESULT.json")],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
