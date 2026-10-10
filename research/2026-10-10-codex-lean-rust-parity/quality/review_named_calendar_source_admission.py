#!/usr/bin/env python3
"""Authenticate the exact named decoder/registry consumer, without executing Lean."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("NAMED-CALENDAR-SOURCE-ADMISSION-CERTIFICATE.json",
        "NAMED-CALENDAR-SOURCE-ADMISSION-7C36-RESULT.json", {
            "G7NamedCalendarSourceAdmission": (
                "reuse/sources/G7NamedCalendarSourceAdmission.lean",
                "7c365d3d7d7c75a7b592443fb82d68a89a8df7000347dcbb8352b988b47f780e",
                (172, 5301, 3089))},
        {"cache_reuse": 171, "fresh_components": 1})
    return write_review("NAMED-CALENDAR-SOURCE-ADMISSION-REVIEW.json",
        "named_calendar_source_admission_saved_review_v1", proof,
        "Ten public heads bind the literal N2 fork decoder to the existing N2 source "
        "and empty original registry, and expose the already accepted NP decoder, "
        "registry and parallel parent occurrence identities. The explicit dependent "
        "registry cast is checked by the kernel. This is admission of those fixed "
        "codes under BinaryValid/RegistryValid/CutChild, not a general native parser "
        "or Rust validator refinement, labelled planarity, a source census or a new "
        "calendar law. The failed51e transport attempt remains preserved. "
        "Complete172-module ownership audit; no compiler or native solver rerun here.",
        Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
