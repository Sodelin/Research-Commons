#!/usr/bin/env python3
"""Authenticate reuse of listed outcomes through the full original-row theorem."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("RATIONAL-COMPRESSION-CHECKED-ROWS-CERTIFICATE.json",
        "RATIONAL-COMPRESSION-CHECKED-ROWS-BC68-RESULT.json", {
            "G6RationalCompressionCheckedRows": (
                "reuse/sources/G6RationalCompressionCheckedRows.lean",
                "bc68357fc0061f5cf1cd4016935b9e34fb2e582ed0a1eec2343972bb83417015",
                (101, 2695, 1683))},
        {"cache_reuse": 100, "fresh_components": 1})
    return write_review("RATIONAL-COMPRESSION-CHECKED-ROWS-REVIEW.json",
        "rational_compression_listed_uniform_original_rows_saved_review_v1", proof,
        "The existing List.all_eq_true projects the separate accepted ground Facts theorem. "
        "Any listed positive typed check then supplies CertificateHolds and the existing uniform "
        "full original-Code population compression conclusion under co-location/live-cap premises. "
        "The list stores names and Booleans, not uniquely recoverable input data; independent "
        "literal/JSON provenance is separately bound by the accepted chain review. No finite data, "
        "algorithm or evaluator is added. Complete101-module audit, no solver rerun here.",
        Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
