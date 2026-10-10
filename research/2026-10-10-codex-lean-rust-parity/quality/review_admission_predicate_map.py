#!/usr/bin/env python3
"""Authenticate the static decoder/validator map; do not promote admission."""
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from review_support_join import PACKET, identity


def main():
    note = PACKET / "rust/notes/ORIGINAL-ADMISSION-PREDICATE-MAP-20261010T1720Z.md"
    text = note.read_text()
    labels = ["G7OriginalAdmission.lean", "G7OriginalFiniteEncoding.lean",
        "G7FiniteReachability.lean", "natural_cell.rs", "source_population.rs",
        "source_calendar.rs", "calendar-cli/src/request.rs", "G5CalendarRoutes.lean",
        "NativePairClockLaw.lean", "NativeIndependentPairMixture.lean"]
    links = dict(re.findall(r"\[([^\]]+)\]\(([^)]+)\)", text))
    rows, errors = [], []
    for label in labels:
        digest = re.search(r"\| `" + re.escape(label) + r"` \| `([0-9a-f]{64})` \|", text).group(1)
        paths = {(note.parent / target).resolve() for target in links.values()
                 if target.endswith("/" + label)}
        if label == "calendar-cli/src/request.rs":
            paths = {PACKET / "rust" / label}
        if len(paths) != 1:
            raise ValueError("Expected one exact source link for " + label)
        path = paths.pop()
        passed = identity(path)["sha256"] == digest
        rows.append({"file": label, "path": str(path), "sha256": digest, "unchanged": passed})
        if not passed:
            errors.append("Current identity: " + label)
    checks = {
        "exact_note": identity(note)["sha256"] == "e54faf710a27deacfad1efe16e91a9f3b0635e2d834d3c770e8487baaa23b862",
        "distinct_directed_dominance_and_undirected_edge_bridge":
            "**undirected**" in text and "optionally deletes a vertex" in text,
        "native_refinement_and_labelled_planarity_remain_missing":
            "outer-labelled planarity/cofacial" in text and "native-to-code witness" in text,
        "hand_count_argument_is_labelled": "hand-derived count check" in text,
        "negative_unequal_ages_not_disallowed": "nonnegative absolute ages" in text,
    }
    errors.extend(k for k, v in checks.items() if not v)
    answer = {"schema": "original_admission_static_provider_identity_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": not errors,
        "errors": errors, "checks": checks, "source_pins": rows, "note": identity(note),
        "reviewer": identity(Path(__file__)), "source_files_rehashed": len(rows),
        "scope": "Root reread the static predicate map and existing decoder/validator bodies and rehashed ten exact source identities. BinaryValid/RegistryValid algorithmic coverage, typed native representation correspondence, cut-child and labelled-planarity admission remain distinct. This is a static source/provenance review, not a native refinement theorem or new graph test execution.",
        "native_validator_refinement_proved": False,
        "source_admission_verified": False, "master_complete": False}
    (PACKET / "quality/ADMISSION-PREDICATE-MAP-REVIEW.json").write_text(
        json.dumps(answer, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": answer["pass"], "errors": errors, "sources": len(rows)}))
    return not answer["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
