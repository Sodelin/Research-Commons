#!/usr/bin/env python3
"""Authenticate the concrete original matching-date phase consumers."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("ORIGINAL-CALENDAR-PHASES-CERTIFICATE.json",
                   "ORIGINAL-CALENDAR-PHASES-DEF9-RESULT.json", {
        "G7OriginalCompletedCalendarPhases": (
            "design/lean/G7OriginalCompletedCalendarPhases.lean",
            "def96b4a4beabd6f5731906b13cc2b4f03db518ff1824bf6d82dd4e194527223",
            (200, 6002, 3599))}, {"cache_reuse": 199, "fresh_components": 1})
    return write_review("ORIGINAL-CALENDAR-PHASES-REVIEW.json",
        "original_calendar_finite_phases_saved_root_review_v1", proof,
        "Eighteen concrete original exit/entry List.Perm facts and nine paired matching-date "
        "phase consumers for the two-tip, negative unequal serial-tip and parallel COMMON "
        "calendar controls are kernel checked. They consume the accepted generic phase "
        "provider for same-bank physical PMF and every raw trace's phase location invariants. "
        "Separate200-module complete audit. Whole-word raw-root and completed physical "
        "calendar law composition require their separate consumers; no native parser/slot/encoder "
        "refinement, independent physical cube equality, source admission or master closure is inferred.",
        Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
