#!/usr/bin/env python3
"""Authenticate the supplied-rational-certificate source transfer."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("RATIONAL-COMPRESSION-CERTIFICATE.json",
                   "RATIONAL-COMPRESSION-CERTIFICATE-RESULT.json", {
        "G6RationalCompressionCertificate": (
            "reuse/sources/G6RationalCompressionCertificate.lean",
            "353521bc18e3fab1fce6fe6141bc4d5006ceb3d07cc27b9728d66b921abedd3e",
            (98, 2647, 1672))}, {"cache_reuse": 97, "fresh_components": 1})
    return write_review("RATIONAL-COMPRESSION-PROOF-REVIEW.json",
        "rational_compression_certificate_saved_root_review_v1", proof,
        "The executable typed rational checker implies the supplied positive original-index "
        "mass/tail certificate and, after casting, accepted B's uniform full original Code-row "
        "compression under co-location/live-cap premises. One common certificate precedes every "
        "source/sample/state/population row. Separate98-module complete audit; no compiler rerun, "
        "concrete evaluator agreement, native parser/RREF refinement, source-factor realization, "
        "arbitrary-real extraction or master closure is inferred.", Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
