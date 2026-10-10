#!/usr/bin/env python3
"""Review the separately preserved effective boundary proof acceptance."""
from datetime import datetime, timezone
import json
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    result = review("EFFECTIVE-BOUNDARY",
        {"G7EffectiveBoundaryCoefficients": (133, 3507, 2243)},
        {"cache_reuse": 132, "fresh_components": 1})
    receipt = {
        "schema": "effective_boundary_saved_proof_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": result["pass"], "review": result,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name))
                    for name in ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Exact saved source, imports, fresh root/aggregate/full ownership audit and kernel flags. Generic source-boundary coefficient theorem; no new compilation, Rust refinement or master closure.",
    }
    (PACKET / "quality/EFFECTIVE-BOUNDARY-REVIEW.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": result["errors"],
                      "preserved_artifacts": result["preserved_artifacts"]}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
