#!/usr/bin/env python3
"""Authenticate saved original phase-permutation calendar consumers."""
import json
from datetime import datetime, timezone
from pathlib import Path
from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    proof = review("CALENDAR-PHASE-CONSUMER", {
        "G7CalendarPhaseConsumers": (181, 4978, 3189)},
        {"cache_reuse": 180, "fresh_components": 1})
    receipt = {"schema": "calendar_phase_consumer_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved181-module complete kernel/ownership audit. Valid complete matching-date phase lists give raw endpoint trace/root support; phase-Perm transport supplies the original same-physical-bank PMF. This does not prove equality of independently allocated symbolic slot polynomials, numeric native chronology/parser/encoder refinement, complete source admission or master closure. No compiler/evaluator rerun."}
    (PACKET / "quality/CALENDAR-PHASE-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": receipt["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
