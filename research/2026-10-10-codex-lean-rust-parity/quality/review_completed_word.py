#!/usr/bin/env python3
"""Authenticate the source-side conditional completed-word bridge."""
from datetime import datetime, timezone
import json
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    proof = review("EFFECTIVE-COMPLETED-WORD", {
        "G7EffectiveCompletedWordCoefficients": (166, 4599, 2887)},
        {"cache_reuse": 165, "fresh_components": 1})
    result = {"schema": "conditional_completed_word_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved166-module complete aggregate/ownership audit. Conditional and natural completed-polynomial coefficient identities retain explicit nonempty-copy, positive physical bank and EVERY raw endpoint row ancestral-root premises. No generated-calendar root-support derivation, new compiler run, universal native refinement, source admission or master closure inferred."}
    (PACKET / "quality/COMPLETED-WORD-REVIEW.json").write_text(
        json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": result["pass"], "errors": result["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not result["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
