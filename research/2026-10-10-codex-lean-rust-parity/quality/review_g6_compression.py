#!/usr/bin/env python3
"""Authenticate saved positive compression of original full-row generators."""
import json
from datetime import datetime, timezone
from pathlib import Path
from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    proof = review("G6-COMPRESSION", {
        "G6PositiveGeneratorCompression": (95, 2492, 1575)},
        {"cache_reuse": 94, "fresh_components": 1})
    receipt = {"schema": "g6_positive_generator_compression_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": proof["pass"], "errors": proof["errors"], "proof": proof,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved95-module complete kernel/ownership audit including the original privately prepared Mathlib Caratheodory provider. For M>=2, one positive list of at most M-1 supplied original atoms preserves total weight/tail moments and every original co-located capped full-Code quotient-generator row. Atom choice precedes source/sample/state/population quantifiers. Consumes accepted original spectral support and generator identity at one; no count-only or encoded-state shortcut. Noncomputable real-weight existence is not a Rust extractor, legal source-factor reconstruction or full G6 closure. No compiler/evaluator rerun."}
    (PACKET / "quality/G6-COMPRESSION-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": receipt["errors"],
                      "preserved_artifacts": proof["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
