#!/usr/bin/env python3
"""Authenticate the saved finite certificate fixture contexts."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("RATIONAL-COMPRESSION-FIXTURE-CERTIFICATE.json",
        "RATIONAL-COMPRESSION-FIXTURE-CDDC-RESULT.json", {
            "G6RationalCompressionCertificateFixture": (
                "reuse/sources/G6RationalCompressionCertificateFixture.lean",
                "cddca5b3f2ff85f174c0c547d2698c177c1fb9758cc7d98f34a0f004395120a6",
                (99, 2689, 1678)),
            "G6RationalCompressionCertificateFixtureMain": (
                "reuse/sources/G6RationalCompressionCertificateFixtureMain.lean",
                "993a59ac5cd535324d03fa74e88cf63d370aa64baf531328886619dd60aab1b5",
                (100, 2691, 1678))},
        {"cache_reuse": 197, "fresh_components": 2})
    return write_review("RATIONAL-COMPRESSION-FIXTURE-PROOF-REVIEW.json",
        "rational_compression_finite_fixture_saved_root_review_v1", proof,
        "Complete separate99/100-module audits of the exact finite fixture and Main sources. "
        "The generic checker soundness is separately checked. Computational #guard outcomes "
        "are not themselves a kernel theorem asserting allChecksPass=true; a separate Facts "
        "proof is required for that assertion. No evaluator or native solver is rerun here.",
        Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
