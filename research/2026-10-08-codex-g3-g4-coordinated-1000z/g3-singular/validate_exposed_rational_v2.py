"""Exact source-mask and refusal checks of the bounded original slice recognizer."""
from fractions import Fraction as F
from pathlib import Path
import argparse
import datetime
import hashlib
from types import ModuleType
import itertools
import json
import time

HERE = Path(__file__).resolve().parent
PROGRAM = HERE / "recognize_exposed_rational.py"
with PROGRAM.open("rb") as captured_file:
    PROGRAM_BYTES = captured_file.read(65537)
assert len(PROGRAM_BYTES) <= 65536
PROGRAM_SHA = hashlib.sha256(PROGRAM_BYTES).hexdigest()
assert PROGRAM_SHA == "65dcb9e351ba27dda9173c1710d1252fc7932ffaf8bcf43edc5548e72b5f5624"
recognizer = ModuleType("exposed_recognizer_captured")
recognizer.__dict__["__file__"] = str(PROGRAM)
exec(compile(PROGRAM_BYTES.decode("utf-8"), str(PROGRAM), "exec", dont_inherit=True), recognizer.__dict__)
with recognizer.CHANNELS.open("rb") as captured_file:
    CHANNEL_BYTES = captured_file.read(65537)
assert len(CHANNEL_BYTES) <= 65536
CHANNEL_SHA = hashlib.sha256(CHANNEL_BYTES).hexdigest()
assert CHANNEL_SHA == "22548fd40b371940baf9a1b62fbcd43edbead8f9c27c75e5795032027ada27e4"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def profile(weights):
    atoms = [F(1, 8), F(1, 4), F(1, 2)]
    u1 = sum(a * w for a, w in zip(atoms, weights))
    u3 = sum(a ** 3 * w for a, w in zip(atoms, weights))
    return {"contract": recognizer.CONTRACT, "source_mode": "COMMON",
            "probabilities": {"B2": "2/3", "B3": "25/48",
                              "Q1": str(F(1, 2) + u1 / 8),
                              "Q3": str(F(1, 2) + u3 / 38), "QP": "1/2"}}

def graph_mask_law(source):
    assert all(h["lower_weight"]["type"] == "rational" for h in source["inheritance"])
    law = {}
    arcs = source["arcs"]
    for choices in itertools.product([0, 1], repeat=len(source["inheritance"])):
        parents = {}
        probability = F(1)
        for bit, hybrid in zip(choices, source["inheritance"]):
            g = F(hybrid["lower_weight"]["value"])
            parents[hybrid["hybrid"]] = hybrid["lower_parent_arc"] if bit else hybrid["upper_parent_arc"]
            probability *= g if bit else 1 - g
        value = F(1)
        vertex = "A"
        while vertex != "v":
            incoming = [arc for arc in arcs if arc["child"] == vertex]
            if vertex in parents:
                incoming = [arc for arc in incoming if arc["id"] == parents[vertex]]
            assert len(incoming) == 1
            value *= F(incoming[0]["survival"])
            vertex = incoming[0]["parent"]
        law[value] = law.get(value, F(0)) + probability
    return law

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    arguments = parser.parse_args()
    arguments.output_dir.mkdir(parents=True, exist_ok=True)
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    start = time.monotonic()
    original_no = profile([F(2, 5), F(1, 5), F(2, 5)])
    cases = [
        ("literal_rational_all_core_NO", original_no, "NO", None),
        ("sharp_two_hybrid_binomial_YES", profile([F(1, 4), F(1, 2), F(1, 4)]), "YES", 2),
        ("two_hybrid_distinct_rational_weights_YES", profile([F(1, 8), F(1, 2), F(3, 8)]), "YES", 2),
        ("two_hybrid_irrational_weights_YES", profile([F(1, 10), F(7, 10), F(1, 5)]), "YES", 2),
        ("missing_middle_one_hybrid_YES", profile([F(1, 2), F(0), F(1, 2)]), "YES", 1),
        ("ordinary_middle_atom_YES", profile([F(0), F(1), F(0)]), "YES", 0),
    ]
    changes = [
        ("uncalibrated_refusal", "probabilities", "B2", "3/4", "UNKNOWN"),
        ("interior_not_classified", "probabilities", "QP", "3/4", "UNKNOWN"),
        ("negative_exposing_expectation_NO", "probabilities", "QP", "1/4", "NO"),
        ("invalid_rational_refusal", "probabilities", "Q1", "1/0", "UNKNOWN"),
        ("binary_float_refusal", "probabilities", "Q1", 0.5375, "UNKNOWN"),
    ]
    for name, container, key, value, status in changes:
        changed = json.loads(json.dumps(original_no))
        changed[container][key] = value
        cases.append((name, changed, status, None))
    changed = json.loads(json.dumps(original_no)); changed["source_mode"] = "INDEPENDENT"
    cases.append(("INDEPENDENT_mode_refusal", changed, "UNKNOWN", None))
    changed = json.loads(json.dumps(original_no)); changed["additional_observed_rows"] = {"extra": "1/2"}
    cases.append(("richer_input_not_dropped", changed, "UNKNOWN", None))
    changed = json.loads(json.dumps(original_no)); changed["probabilities"]["Q1"] = "1/2"; changed["probabilities"]["Q3"] = "1/2"
    cases.append(("negative_atomic_mass_NO", changed, "NO", None))

    coefficients = list(map(F, json.loads(CHANNEL_BYTES.decode("utf-8"))["exposing_polynomial_coefficients_in_sparse_order"]))
    powers = [0, 1, 3, 6, 10, 15, 21]
    checks = {}
    records = []
    for name, data, expected, hybrids in cases:
        answer = recognizer.recognize(data)
        checks[f"{name}_status"] = answer["status"] == expected
        checks[f"{name}_reason_present"] = bool(answer["reason"])
        if name == "literal_rational_all_core_NO":
            checks["literal_NO_tuple"] = data["probabilities"] == {"B2": "2/3", "B3": "25/48", "Q1": "43/80", "Q3": "24389/48640", "QP": "1/2"}
            checks["literal_NO_discriminant"] = answer["decoded"]["bernoulli_discriminant"] == "-3/5"
            checks["literal_NO_full_core_exclusion"] = "all finite" in answer["exclusion"]
        if expected == "YES":
            source = answer["source"]
            checks[f"{name}_sharp_original_hybrid_count"] = answer["minimum_total_original_hybrids"] == hybrids == len(source["inheritance"])
            checks[f"{name}_one_full_shared_graph"] = source["taxon_vertices"] == ["A", "B", "C", "D"] and source["root"] == "r"
            checks[f"{name}_exact_output_reconstruction"] = all(F(answer["exact_original_probabilities"][k]) == F(data["probabilities"][k]) for k in recognizer.NAMES)
            if name == "two_hybrid_irrational_weights_YES":
                p, q = [h["lower_weight"] for h in source["inheritance"]]
                checks["irrational_coins_use_exact_root_encodings"] = p["type"] == q["type"] == "real_algebraic"
                checks["irrational_coins_correct_polynomial"] = p["polynomial_coefficients_ascending"] == q["polynomial_coefficients_ascending"] == [1, -9, 10]
                checks["irrational_coins_distinct_interior_isolations"] = p["isolating_interval"] == ["0", "9/20"] and q["isolating_interval"] == ["9/20", "1"]
            else:
                law = graph_mask_law(source)
                declared_law = dict(zip(map(F, source["survival_law_atoms"]), map(F, source["survival_law_masses"])))
                checks[f"{name}_actual_graph_mask_law"] = law == declared_law and sum(law.values()) == 1
                checks[f"{name}_exposing_expectation_zero"] = sum(w * sum(c * a ** k for c, k in zip(coefficients, powers)) for a, w in law.items()) == 0
                checks[f"{name}_source_mask_channel_moments"] = (F(1, 2) + sum(a * w for a, w in law.items()) / 8 == F(data["probabilities"]["Q1"]) and F(1, 2) + sum(a ** 3 * w for a, w in law.items()) / 38 == F(data["probabilities"]["Q3"]))
        if expected == "UNKNOWN":
            checks[f"{name}_no_promoted_NO_or_source"] = "source" not in answer and "exclusion" not in answer
        input_path = arguments.output_dir / f"{name}.input.json"
        output_path = arguments.output_dir / f"{name}.output.json"
        input_path.write_text(json.dumps(data, indent=2) + "\n")
        output_path.write_text(json.dumps(answer, indent=2) + "\n")
        records.append({"case": name, "expected": expected, "actual": answer["status"],
                        "input_file": input_path.name, "input_sha256": digest(input_path),
                        "output_file": output_path.name, "output_sha256": digest(output_path)})
    assert all(checks.values()), [name for name, passed in checks.items() if not passed]
    receipt = {"schema": "g3-exposed-rational-recognizer-validation-v2", "started_utc": started,
               "elapsed_seconds": time.monotonic() - start,
               "claim_tier": "actual exact rational slice recognizer runs and graph-mask arithmetic only; all-core correspondence is inherited hand/source proof",
               "program_sha256": PROGRAM_SHA, "test_script_sha256": digest(Path(__file__).resolve()),
               "proof_sha256": digest(recognizer.PROOF), "channel_sha256": CHANNEL_SHA,
               "cases": records, "cases_total": len(cases), "checks": checks,
               "checks_passed": sum(checks.values()), "checks_total": len(checks), "status": "PASS",
               "compiler_invocations": 0, "QE_invocations": 0, "gene_topology_simulations": 0,
               "execution_identity": "One bounded recognizer source buffer, exact fixed SHA, compile/exec ModuleType with dont_inherit=True; one captured and fixed-hash exposing-channel JSON buffer; no SourceFileLoader or provider reread hash.",
               "limits": "No new coalescent full-genealogy forward compiler or empirical validation. Rational-only implementation; algebraic-weight outputs use polynomial plus exact isolating interval. No general G3 recognition."}
    arguments.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "cases_total": len(cases), "checks_passed": sum(checks.values()), "checks_total": len(checks)}))

if __name__ == "__main__":
    main()
