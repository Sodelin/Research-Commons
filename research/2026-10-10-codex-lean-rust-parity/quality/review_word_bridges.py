#!/usr/bin/env python3
"""Review saved initialization, epoch, node and concrete word bridges."""
from datetime import datetime, timezone
import json
from pathlib import Path

from review_proof_extensions import review
from review_support_join import PACKET, identity


def main():
    initialization = review("EFFECTIVE-INITIALIZATION", {
        "G7EffectiveInitializationCoefficients": (135, 3550, 2272)},
        {"cache_reuse": 134, "fresh_components": 1})
    epoch = review("SELECTED-EPOCH-UNIQUENESS", {
        "G7SelectedEpochTableUniqueness": (139, 3554, 2290)},
        {"cache_reuse": 138, "fresh_components": 1})
    generic = review("SPARSE-WORD-COMPOSITION", {
        "G7SparseWordComposition": (138, 3810, 2359)},
        {"cache_reuse": 137, "fresh_components": 1})
    node = review("EFFECTIVE-NODE", {
        "G7EffectiveNodeCoefficients": (141, 3625, 2320)},
        {"cache_reuse": 140, "fresh_components": 1})
    word = review("EFFECTIVE-WORD", {
        "G7EffectiveWordCoefficients": (150, 4051, 2526)},
        {"cache_reuse": 149, "fresh_components": 1})
    bridges = [initialization, epoch, generic, node, word]
    errors = [error for bridge in bridges for error in bridge["errors"]]
    receipt = {"schema": "natural_initialization_and_chosen_epoch_saved_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors,
        "initialization": initialization, "chosen_single_epoch": epoch,
        "generic_composition": generic, "concrete_node": node,
        "concrete_word": word,
        "reviewer_sha256": identity(Path(__file__))["sha256"],
        "helpers": {name: identity(Path(__file__).with_name(name)) for name in
                    ("review_proof_extensions.py", "review_support_join.py")},
        "scope": "Saved natural initialization135, chosen single-epoch139, generic composition138, concrete node141 and concrete word150 module audits. Exact source/receipt/artifact bindings checked; concrete providers discharge the generic step premise. Single-epoch coordinate independence supplies no shared multi-slot physical cube. No new compiler run, generated-calendar certificate, universal native refinement or master closure inferred."}
    (PACKET / "quality/WORD-BRIDGES-REVIEW.json").write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"pass": receipt["pass"], "errors": errors,
                      "preserved_artifacts": sum(bridge["preserved_artifacts"] for bridge in bridges)}))
    return not receipt["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
