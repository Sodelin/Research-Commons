#!/usr/bin/env python3
"""Authenticate the saved original-row G6 generator and coarse remainder root."""
import json
from datetime import datetime, timezone
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    proof = review("G6-GENERATOR", {
        "G6OriginalPopulationGeneratorBounds": (93, 2453, 1538)},
        {"cache_reuse": 92, "fresh_components": 1})
    receipt = {
        "schema": "g6_original_generator_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved93-module complete kernel/ownership audit and exact original full-row generator consumer. Unconditional P(1)=delta and ordered half-rate Q=-P'(1), physical fuel-M law and coarse cap-only row-L1 remainder consume old recurrence/coefficient-bound/scalar-power providers. No Code-cardinality multiplier, sharper Appendix constant, positive source reconstruction, native refinement or G6 master closure inferred. No compiler/evaluator rerun.",
    }
    (PACKET / "quality/G6-GENERATOR-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": receipt["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
