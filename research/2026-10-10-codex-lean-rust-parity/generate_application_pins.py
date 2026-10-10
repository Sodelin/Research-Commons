#!/usr/bin/env python3
"""Record byte identity of the current application derivative; no proof claims."""
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[1]
PREVIOUS = ROOT / "research/2026-10-09-codex-conditional-bridge-1630z/BRIDGE-MANIFEST.json"


def identity(path):
    data = path.read_bytes()
    return {"path": str(path.relative_to(ROOT)), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def main():
    old = json.loads(PREVIOUS.read_text())
    derivative_names = {"applications/practical-solver/run.py",
                        "applications/practical-solver/README.md"}
    # This navigation file changed on main before this task's baseline.
    # Record that known inherited update explicitly, rather than reassigning
    # the historical manifest's hashes to current bytes.
    baseline_updates = {"START-HERE.md"}
    files = {ROOT / name for name in derivative_names}
    files.add(ROOT / "applications/practical-solver/examples/natural-cell.rc1")
    files.add(ROOT / "applications/practical-solver/examples/genealogy-law.rc1")
    files.add(ROOT / "research/2026-10-01-g7-continuous-design/law_compiler.py")
    files.update(ROOT / name for name in baseline_updates)
    files.update(PACKET / name for name in (
        "rust/native_component.py", "rust/Cargo.toml", "rust/Cargo.lock",
        "rust/INHERITED-SOURCES.json", "rust/COMPONENT-PINS.json",
        "design/certificate_check.py", "design/CONTRACT.md",
        "rust/native_chart_component.py", "design/chart_check.py", "design/CHART-CONTRACT.md",
        "rust/native_law_component.py", "rust/law_component_requirements.txt",
        "design/law_check.py", "design/LAW-CONTRACT.md",
        "verify_derivative.py", "generate_application_pins.py"))
    files.update((PACKET / "rust/src").glob("*.rs"))
    pins = {
        "schema": "application_derivative_byte_pins_v1",
        "scope": "Current finite-cell and genealogy-law launcher derivative and its runtime sources",
        "inherited_manifest": identity(PREVIOUS),
        "inherited_derivatives": [
            {"path": row["path"], "previous_sha256": row["sha256"]}
            for row in old["files"] if row["path"] in derivative_names],
        "inherited_baseline_updates": [
            {"path": row["path"], "previous_sha256": row["sha256"],
             "baseline_commit": "32f1538ebcd1a80b999bb14e08df905d13184ec7",
             "change_commit": "26e592f6",
             "reason": "Published research navigation refreshed before this task"}
            for row in old["files"] if row["path"] in baseline_updates],
        "files": [identity(path) for path in sorted(files)],
        "scientific_claims_verified": False,
        "whole_solver_refinement_verified": False,
        "note": "The prior manifest remains a historical byte record. These pins do not certify a supplied binary or establish source-model admission."
    }
    (PACKET / "APPLICATION-DERIVATIVE-PINS.json").write_text(
        json.dumps(pins, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pinned_files": len(pins["files"]),
                      "inherited_derivatives": len(pins["inherited_derivatives"])}))


if __name__ == "__main__":
    main()
