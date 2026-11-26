"""Run the positive import and two negative controls from a pinned public fixture."""
import json
from pathlib import Path
import sys
import tempfile

import import_reduced as route
import linear
import premise_handoff as handoff


def smoke(lean):
    pin = "11ee5daae50ecd0f02cf7ea846e8770b47976b8e6b54498a0662aa9351c8e3ff"
    theorem = "goldbach.integer-budget-187"
    here = Path(__file__).resolve().parent
    raw = (here/"assumptions-fixture.json").read_bytes()
    previous = json.loads((here/"premise-handoff.receipt.json").read_bytes())
    accepted = previous["independent_consumer"]
    original = linear.parse(raw)
    reduced = handoff.shape(raw, pin, theorem)["reduced_certificate"]
    with tempfile.TemporaryDirectory(prefix="pb_check_import_") as d:
        root = Path(d)
        output = route.build(raw, pin, theorem, accepted, lean, root/"exact")
        module = output["standalone_module"]
        checks = {}
        bad_acceptance = {**accepted,"premise_ids":list(reversed(accepted["premise_ids"]))}
        try:
            route.build(raw, pin, theorem, bad_acceptance, lean, root/"wrong-ids")
        except ValueError as exc:
            assert "premise IDs mismatch" in str(exc) and not (root/"wrong-ids").exists()
            checks["wrong_ids"] = "rejected_before_build"
        else:
            raise AssertionError("wrong premise IDs accepted")
        # Replace the provider with a different but valid Lean theorem in a fresh
        # directory. Check the same consumer, not a deliberately broken variant.
        weaker = {**reduced, "target":{**original["target"],"le":-186}}
        wrong = root/"weaker"
        wrong.mkdir()
        p = wrong/(module+".lean")
        p.write_text(route.provider(module, weaker),encoding="ascii")
        c = wrong/"ReuseOriginal.lean"
        c.write_bytes((root/"exact"/c.name).read_bytes())
        checks["weaker_provider_valid_axioms"] = route.axioms(
            route.invoke(lean, wrong, "-o", module+".olean", p.name))
        try:
            route.invoke(lean, wrong, c.name)
        except ValueError as exc:
            assert "Type mismatch" in str(exc) and "186" in str(exc) and "187" in str(exc), str(exc)
            checks["weaker_provider_consumer"] = "rejected_by_lean_type_mismatch"
        else:
            raise AssertionError("substituted weaker provider accepted")
        return {**output, "negative_controls":checks}


if __name__ == "__main__":
    print(json.dumps(smoke(Path(sys.argv[1]).resolve(strict=True)),indent=2))
