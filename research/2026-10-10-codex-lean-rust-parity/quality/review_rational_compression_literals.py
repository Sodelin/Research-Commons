#!/usr/bin/env python3
"""Check the six frozen producer-JSON to typed-Lean translations; invoke no Lean."""
from datetime import datetime, timezone
from fractions import Fraction
import json
from pathlib import Path
import re

from review_support_join import PACKET, identity, read
from review_rational_compression_native import equations, geom, q, require


def main():
    capture_path = PACKET / "reuse/RATIONAL-COMPRESSION-EXAMPLES-CAPTURE-20261010T165956Z.json"
    capture = read(capture_path)
    source = PACKET / "reuse/sources/G6RationalCompressionCertificateFixture.lean"
    text = source.read_text()
    for row in capture["source_pins"]:
        require(identity(PACKET / row["path"])["sha256"] == row["sha256"], "typed source identity")
    require("Fin.ofNat" not in text and "native_decide" not in text, "explicit bounded indices/kernel scope")
    definitions = dict(re.findall(r"^def (\w+)(.*?)(?=^def |^/--|^#|^end |\Z)", text, re.M | re.S))
    cases = []
    for case in capture["cases"]:
        name, n, r = case["name"], case["n"], case["r"]
        for key in ("request", "result", "native_checker"):
            pin = case[key]
            require(identity(PACKET / pin["path"])["sha256"] == pin["sha256"], "saved producer data identity")
        raw = (PACKET / case["request"]["path"]).read_bytes()
        request, result = json.loads(raw), read(PACKET / case["result"]["path"])
        require(result["request_raw"].encode() == raw and result["request"] == request, "native raw/semantic binding")
        require(request["M"] == case["M"] and len(request["atoms"]) == n
                and len(result["output_atoms"]) == r, "typed dimensions")
        require([a["z"] for a in request["atoms"]] == case["z"]
                and [a["alpha"] for a in request["atoms"]] == case["alpha"]
                and [a["input_index"] for a in result["output_atoms"]] == case["atom"]
                and [a["beta"] for a in result["output_atoms"]] == case["beta"], "capture data")
        for kind, size, expected in (("z", n, case["z"]), ("alpha", n, case["alpha"]),
                                      ("beta", r, case["beta"])):
            body = definitions[name + "_" + kind]
            require(f"Fin {size}" in body, "rational finite domain")
            if size == 0:
                require("Fin.elim0" in body, "empty finite function")
                continue
            conditions = [int(x) for x in re.findall(r"if a\.val = (\d+) then", body)]
            require(conditions == list(range(size - 1)), "literal branch indices")
            values = [Fraction(int(a), int(b) if b else 1) for a, b in
                      re.findall(r"\((-?\d+) : ℚ\)(?: / (\d+))?", body)]
            require(values == [q(x) for x in expected], "exact typed rational literals")
        atom_body = definitions[name + "_atom"]
        require(f"Fin {r}" in atom_body and f"Fin {n}" in atom_body, "index finite domain")
        if r:
            require([int(x) for x in re.findall(r"if a\.val = (\d+) then", atom_body)] == list(range(r - 1)), "index branch selection")
            indices = [int(x) for x in re.findall(r"⟨(\d+), by decide⟩", atom_body)]
            require(indices == case["atom"] and all(0 <= i < n for i in indices), "unwrapped original indices")
        else:
            require("Fin.elim0" in atom_body, "empty index function")
        require(f"checkCompression {case['M']} {name}_z {name}_alpha {name}_atom {name}_beta"
                in definitions[name + "_check"], "exact checker invocation")
        actual = True
        try:
            equations(raw, result)
        except ValueError as error:
            require(name == "sameMassWrongTail" and str(error) == "common geometric moment", "independent negative diagnosis")
            actual = False
        require(actual is case["expected"], "independent expected result")
        expected = "true" if actual else "false"
        require(f'("{name}", {name}_check, {expected})' in definitions["checks"], "expected Lean check entry")
        native = read(PACKET / case["native_checker"]["path"])
        require((native["status"] == "ACCEPT") is actual and native["certificate_valid"] is actual, "saved native checker result")
        cases.append({"name": name, "M": case["M"], "original_atoms": n,
                      "selected_atoms": r, "independent_checker": actual, "pass": True})
    wrong = next(row for row in capture["cases"] if row["name"] == "sameMassWrongTail")
    require(sum((q(x) for x in wrong["alpha"]), Fraction(0))
            == sum((q(x) for x in wrong["beta"]), Fraction(0)), "negative control mass preserved")
    require(all(q(x) > 0 for x in wrong["beta"]), "negative control positivity preserved")
    require(len(cases) == capture["case_count"] == 6, "six finite cases")
    receipt = {"schema": "rational_compression_finite_literal_translation_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": True, "errors": [],
        "capture": identity(capture_path), "fixture_source": identity(source), "cases": cases,
        "reviewer": identity(Path(__file__)), "kernel_or_evaluator_executed": False,
        "kernel_truth_of_finite_outcomes_inferred": False, "general_native_parser_refinement_inferred": False,
        "scope": "Static exact translation of six saved native request/result pairs to the authored finite Lean functions, original Fin indices, checker calls and expected outcomes. Five independent moment certificates pass and one same-mass positive wrong-tail certificate fails. Compiled/kernel finite outcomes require separate scheduler evidence."}
    (PACKET / "quality/RATIONAL-COMPRESSION-LITERAL-REVIEW.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": True, "cases": len(cases), "positive": 5, "negative": 1}))


if __name__ == "__main__":
    main()
