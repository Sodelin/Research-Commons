#!/usr/bin/env python3
"""Authenticate the finite whole-word raw-root consumer."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("ORIGINAL-CALENDAR-ROOT-CERTIFICATE.json",
        "ORIGINAL-CALENDAR-ROOT-1B7B-RESULT.json", {
            "G7OriginalCompletedCalendarRoot": (
                "design/lean/G7OriginalCompletedCalendarRoot.lean",
                "1b7bceddc7e1a8f2fca423388c3a6d5506c9390bd270ec5c67f287ffdc31ea42",
                (201, 6018, 3615))},
        {"cache_reuse": 200, "fresh_components": 1})
    return write_review("ORIGINAL-CALENDAR-ROOT-REVIEW.json",
        "original_completed_calendar_finite_raw_root_saved_review_v1", proof,
        "Nine public consumers give trace/root support, every raw naturally initialized "
        "row's ancestral root (including zero-polynomial branches), and completed coefficient "
        "identity for the unchanged two-tip, negative/unequal serial-tip and parallel-COMMON "
        "literal words. Old initialization/interval/phase/root providers are consumed; arbitrary "
        "duration structural support does not itself establish the complete physical-calendar "
        "PMF equality. Complete201-module audit; failed83bf/cbb4 versions preserved. No Lean "
        "or native solver is rerun here.", Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
