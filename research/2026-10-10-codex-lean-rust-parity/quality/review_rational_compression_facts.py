#!/usr/bin/env python3
"""Authenticate the closed finite checker theorem, using kernel reduction."""
from pathlib import Path
from review_saved_consumers import review, write_review


def main():
    proof = review("RATIONAL-COMPRESSION-FACTS-CERTIFICATE.json",
        "RATIONAL-COMPRESSION-FACTS-E9E6-RESULT.json", {
            "G6RationalCompressionCertificateFacts": (
                "reuse/sources/G6RationalCompressionCertificateFacts.lean",
                "e9e6e771d1512af883137389a5e777dedde610cb19320e914137bfe9493dd91e",
                (100, 2691, 1680))},
        {"cache_reuse": 99, "fresh_components": 1})
    return write_review("RATIONAL-COMPRESSION-FACTS-REVIEW.json",
        "rational_compression_closed_finite_facts_saved_root_review_v1", proof,
        "Ordinary kernel reduction (`decide +kernel`) proves allChecksPass=true "
        "for the unchanged six finite supplied-certificate cases and three premise controls. "
        "The failed ordinary-decide attempt is preserved. Complete100-module ownership audit; "
        "no native_decide, extra axiom, resource change, compiler/evaluator rerun here, universal "
        "native parser/RREF refinement or source reconstruction is inferred.", Path(__file__))


if __name__ == "__main__":
    raise SystemExit(main())
