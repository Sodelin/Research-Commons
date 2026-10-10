#!/usr/bin/env python3
"""Authenticate the saved original completed-word fixture audits; run no compiler."""
import json
from datetime import datetime, timezone
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    proof = review("ORIGINAL-CALENDAR-FIXTURE", {
        "G7OriginalCompletedCalendarFixture": (199, 5943, 3541),
        "G7OriginalCompletedCalendarFixtureMain": (200, 5944, 3541)},
        {"cache_reuse": 397, "fresh_components": 2})
    receipt = {
        "schema": "original_completed_calendar_fixture_saved_proof_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
        "reviewer": identity(Path(__file__)),
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Separate199/200-module complete kernel and ownership audits, with exact source92dc and unchanged Main19e. Strict calendar definitions and original completed-word coefficient serializer are checked. Specific finite phase/root instances and physical calendar binding, actual evaluator agreement, universal native refinement and source admission require separate evidence. No compiler or native process is invoked by this saved-evidence review.",
        "actual_evaluator_agreement_inferred": False,
        "specific_calendar_phase_binding_inferred": False,
        "general_native_refinement_inferred": False,
        "source_admission_verified": False,
        "master_complete": False,
    }
    output = PACKET / "quality/CALENDAR-FIXTURE-PROOF-REVIEW.json"
    output.write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": proof["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
