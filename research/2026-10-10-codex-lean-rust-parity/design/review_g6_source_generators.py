#!/usr/bin/env python3
"""Review saved original-source rows for G6 count and generator adapters.

This executes no native producer or Lean process. The full coefficient tables
come from the preserved eight-case actual Lean/Rust population comparison.
Embedded uniform ordered mergers and scalar pure-death partial fractions are
compared to those full rows; rational affine elimination separately challenges
the positive compression contract. Finite checks are not universal proofs.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import time
import types


DESIGN = Path(__file__).resolve().parent
EXPECTED_ORACLE_SHA = "216d83a844019f115de1dfa19c12827e0570348181d380f1435dc6ee646748ff"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def read_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON field")
            result[key] = value
        return result
    def nonfinite(value):
        raise ValueError("nonfinite JSON value: " + value)
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=nonfinite)


def qwire(value):
    return f"{value.numerator}/{value.denominator}"


def death_rate(k):
    return k * (k - 1) // 2


def count_polynomial(k, j):
    """Distinct-rate pure-death partial fractions, not liftTerm recursion."""
    if k == 0:
        return {0: Fraction(1)} if j == 0 else {}
    if not 1 <= j <= k:
        return {}
    numerator = Fraction(1)
    for level in range(j + 1, k + 1):
        numerator *= death_rate(level)
    result = {}
    for level in range(j, k + 1):
        rate = death_rate(level)
        denominator = Fraction(1)
        for other in range(j, k + 1):
            if other != level:
                denominator *= death_rate(other) - rate
        result[rate] = numerator / denominator
    return result


def scaled_polynomial(poly, weight):
    return {rate: weight * value for rate, value in poly.items() if weight * value}


def encoded_poly(row):
    result = {}
    for rate, wire in row["coefficients"]:
        require(type(rate) is int and rate >= 0 and rate not in result, "bad coefficient exponent")
        value = Fraction(wire)
        require(value and qwire(value) == wire, "noncanonical rational coefficient")
        result[rate] = value
    return result


def state_of(oracle, row):
    return oracle.Snapshot(tuple((rep, oracle.freeze_tree(row["genealogy"][rep])) for rep in row["live"]))


def embedded_weights(oracle, start):
    """Literal uniform ordered mergers, preserving the first representative."""
    k = len(start.roots)
    result = {k: {start: Fraction(1)}}
    for j in range(k - 1, 0, -1):
        current = {}
        for state, weight in result[j + 1].items():
            successors = list(oracle.ordered_successors(state))
            require(len(successors) == (j + 1) * j, "ordered choice census wrong")
            for destination in successors:
                current[destination] = current.get(destination, Fraction(0)) + weight / len(successors)
        require(sum(current.values(), Fraction(0)) == 1, "embedded row not normalized")
        require(all(value > 0 for value in current.values()), "nonpositive embedded weight")
        result[j] = current
    return result


def verify_factorization(actual, weights, k):
    for j, row in weights.items():
        require(sum(row.values(), Fraction(0)) == 1 and all(w > 0 for w in row.values()),
                "conditional weights not a probability row")
        require(all(len(state.roots) == j for state in row), "conditional count support wrong")
    support = {state for row in weights.values() for state in row}
    require(support == set(actual), "literal source/embedded support differs")
    for state, polynomial in actual.items():
        j = len(state.roots)
        require(polynomial == scaled_polynomial(count_polynomial(k, j), weights[j][state]),
                "full source coefficient row does not factor by final count")


def geom(n, x):
    return sum((x ** power for power in range(n)), Fraction(0))


def reduced_generator(poly, z):
    # eval P(1) is the entering-state delta, so the constant cancels.
    return -sum((value * geom(rate, z) for rate, value in poly.items()), Fraction(0))


def generator_limit(poly):
    return -sum((value * rate for rate, value in poly.items()), Fraction(0))


def count_remainder_constant(k):
    return sum((abs(value) * rate * (rate - 1) / 2
                for j in range(0 if k == 0 else 1, k + 1)
                for rate, value in count_polynomial(k, j).items()), Fraction(0))


def verify_generator(oracle, actual, start):
    k = len(start.roots)
    literal_q = {start: Fraction(-death_rate(k))} if death_rate(k) else {}
    for destination in oracle.ordered_successors(start):
        literal_q[destination] = literal_q.get(destination, Fraction(0)) + Fraction(1, 2)
    for state, poly in actual.items():
        require(generator_limit(poly) == literal_q.get(state, Fraction(0)),
                "minus polynomial derivative is not the original half-rate generator")
        require(sum(poly.values(), Fraction(0)) == (1 if state == start else 0), "time-zero delta wrong")
    sharp = count_remainder_constant(k)
    coefficient_sharp = sum((abs(value) * rate * (rate - 1) / 2
                             for poly in actual.values() for rate, value in poly.items()), Fraction(0))
    require(coefficient_sharp == sharp, "full-row count-conditioned coefficient mass differs")
    c = death_rate(k)
    coarse = Fraction((1 + k * k) ** k * c * (c - 1), 2)
    checks = []
    for z in (Fraction(0), Fraction(1, 7), Fraction(1, 3), Fraction(2, 3), Fraction(99, 100)):
        l1 = sum((abs(reduced_generator(poly, z) - generator_limit(poly))
                  for poly in actual.values()), Fraction(0))
        require(l1 <= sharp * (1 - z) <= coarse * (1 - z), "full-row geometric remainder failed")
        checks.append({"z": qwire(z), "row_l1": qwire(l1),
                       "sharp_bound": qwire(sharp * (1 - z)), "coarse_bound": qwire(coarse * (1 - z))})
    return {"sharp_constant": qwire(sharp), "coarse_constant": qwire(coarse), "points": checks}


def coordinates(m, z):
    # Include total mass explicitly. The omitted j=2 coordinate is constant1.
    return [Fraction(1)] + [geom(death_rate(j), z) for j in range(3, m + 1)]


def vector_sum(m, atoms):
    total = [Fraction(0) for _ in range(m - 1)]
    for z, alpha in atoms:
        total = [a + alpha * b for a, b in zip(total, coordinates(m, z))]
    return total


def null_vector(matrix):
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0])
    pivots = []
    for col in range(cols):
        pivot = next((i for i in range(len(pivots), rows) if a[i][col]), None)
        if pivot is None:
            continue
        row = len(pivots)
        a[row], a[pivot] = a[pivot], a[row]
        divisor = a[row][col]
        a[row] = [value / divisor for value in a[row]]
        for other in range(rows):
            if other != row and a[other][col]:
                factor = a[other][col]
                a[other] = [x - factor * y for x, y in zip(a[other], a[row])]
        pivots.append(col)
        if len(pivots) == rows:
            break
    free = next((col for col in range(cols) if col not in pivots), None)
    require(free is not None, "no affine dependence in oversized atom family")
    direction = [Fraction(0) for _ in range(cols)]
    direction[free] = Fraction(1)
    for row, col in enumerate(pivots):
        direction[col] = -a[row][free]
    require(all(sum((x * y for x, y in zip(row, direction)), Fraction(0)) == 0 for row in matrix),
            "affine dependence is not exact")
    require(any(x > 0 for x in direction) and any(x < 0 for x in direction),
            "mass-preserving dependence must have both signs")
    return direction


def compress(m, atoms):
    result = list(atoms)
    steps = 0
    while len(result) > m - 1:
        columns = [coordinates(m, z) for z, _ in result]
        direction = null_vector([list(values) for values in zip(*columns)])
        scale = min(weight / delta for (_, weight), delta in zip(result, direction) if delta > 0)
        new = [(z, weight - scale * delta) for (z, weight), delta in zip(result, direction)]
        require(all(weight >= 0 for _, weight in new), "affine elimination made a negative weight")
        result = [(z, weight) for z, weight in new if weight]
        steps += 1
    return result, steps


def verify_compression(m, original, result):
    require(len(result) <= m - 1, "too many compressed atoms")
    require(all(0 < z < 1 and weight > 0 for z, weight in result), "compressed atoms not strictly positive/interior")
    require(all(z in {a for a, _ in original} for z, _ in result), "atom not from supplied source family")
    require(vector_sum(m, original) == vector_sum(m, result), "compression changed mass or a generator coordinate")


def reject(name, action):
    try:
        action()
    except (ValueError, TypeError, KeyError) as error:
        return {"control": name, "rejected": True, "reason": str(error)}
    raise ValueError("adversarial control accepted: " + name)


def run(args):
    evidence = args.population_evidence.resolve()
    output = args.output.resolve()
    require(not output.exists(), "review output already exists")
    output.mkdir(parents=True)
    own = Path(__file__).resolve()
    (output / own.name).write_bytes(own.read_bytes())
    oracle_path = evidence / "population_oracle.py"
    oracle_raw = oracle_path.read_bytes()
    require(hashlib.sha256(oracle_raw).hexdigest() == EXPECTED_ORACLE_SHA, "saved source oracle pin changed")
    oracle = types.ModuleType("g6_saved_population_oracle")
    oracle.__file__ = str(oracle_path)
    sys.modules[oracle.__name__] = oracle
    exec(compile(oracle_raw, str(oracle_path), "exec"), oracle.__dict__)
    receipt_path = evidence / "RECEIPT.json"
    saved = read_json(receipt_path.read_bytes())
    require(saved["pass"] is True and saved["cases_total"] == saved["cases_passed"] == 8
            and saved["oracle_sha256"] == EXPECTED_ORACLE_SHA, "original population receipt not accepted")
    require(saved["languages_executed"] == ["rust", "lean"]
            and saved["execution_modes"]["lean"] == "compiled_lean_evaluator_not_standalone_elf",
            "actual original source execution qualification changed")
    observed_paths = [own, oracle_path, receipt_path]
    cases, tables, contexts, weighted = [], {}, oracle.fixtures(), {}
    for case in saved["cases"]:
        name = case["fixture"]
        expected_path = evidence / (name + ".expected.json")
        observed_paths.append(expected_path)
        expected = read_json(expected_path.read_bytes())
        require(canonical(expected["context"]) == canonical(contexts[name]), "original fixture context changed")
        for language in ("lean", "rust"):
            path = evidence / (name + "." + language + ".stdout")
            observed_paths.append(path)
            old_run = case["process_runs"][language]
            require(old_run["process_started"] is True and old_run["exit_code"] == 0
                    and old_run["timed_out"] is False and sha(path) == old_run["stdout_sha256"],
                    "saved " + language + " output identity/execution changed")
            oracle.check_probe(read_json(path.read_bytes()), expected)
        context = expected["context"]
        start = oracle.validate_context(context)
        k = len(start.roots)
        actual = {}
        for row in expected["rows"]:
            state = state_of(oracle, row)
            require(state not in actual and state.encode(context) == {key: value for key, value in row.items() if key != "coefficients"},
                    "literal snapshot fields or support multiplicity changed")
            actual[state] = encoded_poly(row)
        weights = embedded_weights(oracle, start)
        verify_factorization(actual, weights, k)
        generator = verify_generator(oracle, actual, start)
        conditional = [{"final_count": j, "destinations": len(row),
                        "weights": [{"snapshot": state.encode(context), "weight": qwire(weight)}
                                    for state, weight in sorted(row.items(), key=lambda item: canonical(item[0].encode(context)))]}
                       for j, row in sorted(weights.items())]
        result = {"fixture": name, "copies": len(context["global_labels"]), "entering_roots": k,
                  "literal_rows": len(actual), "conditional": conditional, "generator": generator, "pass": True}
        (output / (name + ".factorization.json")).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        cases.append({key: result[key] for key in ("fixture", "copies", "entering_roots", "literal_rows", "pass")})
        tables[name], weighted[name] = actual, weights
    pins_before = {str(path): sha(path) for path in observed_paths}
    compressions, transfer_rows = [], 0
    for m in range(2, 9):
        count = m + 4
        atoms = [(Fraction(i + 1, count + 1), Fraction(i + 2, i + 3)) for i in range(count)]
        reduced, steps = compress(m, atoms)
        verify_compression(m, atoms, reduced)
        row_checks = 0
        for name, actual in tables.items():
            if len(contexts[name]["start"]["live"]) > m:
                continue
            for poly in actual.values():
                left = sum((alpha * reduced_generator(poly, z) for z, alpha in atoms), Fraction(0))
                right = sum((beta * reduced_generator(poly, z) for z, beta in reduced), Fraction(0))
                require(left == right, "one compressed atom list failed an original source row")
                row_checks += 1
        transfer_rows += row_checks
        compressions.append({"cap": m, "input_atoms": [[qwire(z), qwire(a)] for z, a in atoms],
                             "output_atoms": [[qwire(z), qwire(a)] for z, a in reduced],
                             "positive_atoms": len(reduced), "elimination_steps": steps,
                             "original_source_row_checks": row_checks, "total_mass": qwire(sum((a for _, a in atoms), Fraction(0))),
                             "pass": True})
    controls = []
    two_bad = copy.deepcopy(weighted["twoAncestral"])
    two_bad[1] = {state: 2 * value for state, value in two_bad[1].items()}
    controls.append(reject("ordered_pair_full_rate_instead_of_half", lambda: verify_factorization(tables["twoAncestral"], two_bad, 2)))
    four_bad = copy.deepcopy(weighted["fourAncestral"])
    a, b = list(four_bad[1])[:2]
    four_bad[1][a] += Fraction(1, 100000)
    four_bad[1][b] -= Fraction(1, 100000)
    controls.append(reject("wrong_forest_weights_despite_correct_count_mass", lambda: verify_factorization(tables["fourAncestral"], four_bad, 4)))
    controls.append(reject("generator_derivative_sign", lambda: require(
        all(sum((value * rate for rate, value in poly.items()), Fraction(0)) == generator_limit(poly)
            for poly in tables["twoAncestral"].values()), "positive derivative has the wrong generator sign")))
    controls.append(reject("row_l1_is_not_tv", lambda: require(
        sum((abs(reduced_generator(poly, Fraction(0)) - generator_limit(poly))
             for poly in tables["threeEdge0"].values()), Fraction(0)) <= count_remainder_constant(3) / 2,
        "a TV half factor was incorrectly inserted into the row-L1 bound")))
    bad = read_json((evidence / "frozenRegisterRepeat.expected.json").read_bytes())
    bad["rows"][0]["register"] = [False, False, False]
    controls.append(reject("erase_carried_original_register", lambda: oracle.check_probe(
        bad, read_json((evidence / "frozenRegisterRepeat.expected.json").read_bytes()))))
    original = [(Fraction(1, 3), Fraction(1)), (Fraction(2, 3), Fraction(1))]
    controls.append(reject("constant_coordinate_mass_omitted", lambda: verify_compression(2, original, [(Fraction(1, 3), Fraction(1))])))
    example = compressions[2]
    atoms = [(Fraction(z), Fraction(a)) for z, a in example["input_atoms"]]
    reduced = [(Fraction(z), Fraction(a)) for z, a in example["output_atoms"]]
    controls.append(reject("zero_weight_called_strictly_positive", lambda: verify_compression(4, atoms, reduced + [(atoms[0][0], Fraction(0))])))
    drift = reduced[:]
    drift[0] = (drift[0][0], drift[0][1] + Fraction(1, 100000))
    drift[1] = (drift[1][0], drift[1][1] - Fraction(1, 100000))
    controls.append(reject("same_mass_wrong_generator_coordinate", lambda: verify_compression(4, atoms, drift)))
    pins_after = {str(path): sha(path) for path in observed_paths}
    require(pins_before == pins_after, "saved original inputs changed during review")
    result = {"schema": "g6_saved_original_generator_review_v1", "pass": True,
              "claim": "FINITE_SAVED_ORIGINAL_SOURCE_GENERATOR_FACTORIZATION_AND_COMPRESSION_REVIEW",
              "reviewed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "reviewer_sha256": sha(own), "inputs_before": pins_before, "inputs_after": pins_after,
              "native_producer_executed": False, "lean_compiler_or_evaluator_executed": False,
              "source_kernel_audit_repeated": False, "general_source_refinement_proved": False,
              "source_admission_promoted": False, "positive_network_reconstructed": False,
              "count_factorization_cases": cases, "cases_total": len(cases), "cases_passed": len(cases),
              "full_literal_rows": sum(case["literal_rows"] for case in cases),
              "generator_points_per_case": 5, "compression_cases": compressions,
              "compression_source_row_checks": transfer_rows, "adversarial_controls": controls,
              "scope": "Eight previously executed original encoded source inputs, copied labels<=4; arbitrary-Code theorem, all-cap compression and positive source reconstruction remain separate proof contracts.",
              "algorithms": ["actual ordered-merger embedded weights", "scalar pure-death distinct-rate partial fractions",
                             "complete saved polynomial derivative and geometric quotient", "exact rational affine dependence elimination"]}
    (output / "RECEIPT.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in ("pass", "cases_total", "full_literal_rows", "compression_source_row_checks")}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--population-evidence", type=Path, default=DESIGN / "evidence/population-lean-rust-review-1")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        return run(args)
    except (OSError, ValueError, TypeError, KeyError) as error:
        if args.output.exists():
            (args.output / "FAILURE-RECEIPT.json").write_text(json.dumps({"pass": False, "reason": str(error)}, indent=2) + "\n")
        raise


if __name__ == "__main__":
    raise SystemExit(main())
