#!/usr/bin/env python3
"""Independent mixed-population generator review; private fixture JSON, no RC1 API.

Choose rates 7**i. With at most four copies every survival exponent is <=6,
so a univariate spectral row uniquely recovers its multivariate coefficients.
No population table product, liftTerm recursion or merger-history formula is
used. File identities and finite tests do not prove source or Rust refinement.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import time

from population_oracle import (canonical_tree, freeze_tree, require, tree_json,
                               tree_leaves)

DESIGN = Path(__file__).resolve().parent


def exact_json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def qwire(value):
    return f"{value.numerator}/{value.denominator}"


def variables(context):
    return [["E", i] for i in range(len(context["edges"]))] + [["A", context["root"]]]


def weights(context):
    return {tuple(place): 7**i for i, place in enumerate(variables(context))}


def reachable(context, start, target):
    pending, seen = [start], {start}
    while pending:
        vertex = pending.pop()
        if vertex == target:
            return True
        for older, younger in context["edges"]:
            if older == vertex and younger not in seen:
                seen.add(younger)
                pending.append(younger)
    return False


def validate_place(context, place, sample):
    require(len(place) == 2 and type(place[1]) is int, "malformed original location")
    tag, identifier = place
    if tag == "E":
        require(0 <= identifier < len(context["edges"]), "unknown original edge")
        start = context["edges"][identifier][1]
    elif tag == "V":
        require(0 <= identifier < context["vertices"], "unknown original vertex")
        start = identifier
    else:
        require(tag == "A" and identifier == context["root"], "wrong ancestral root")
        start = identifier
    require(reachable(context, start, context["leaves"][sample]), "source descendant mismatch")


@dataclass(frozen=True)
class State:
    roots: tuple[tuple[int, object, tuple[str, int]], ...]

    def encode(self, context):
        copies = len(context["local_samples"])
        require(tuple(rep for rep, _, _ in self.roots) == tuple(sorted(set(
            rep for rep, _, _ in self.roots))), "duplicate/unordered live representatives")
        ancestor, genealogy, location = [None]*copies, [None]*copies, [None]*copies
        for rep, tree, place in self.roots:
            leaves = tree_leaves(tree)
            require(type(rep) is int and rep in leaves, "owner outside its own genealogy")
            require(0 <= rep < copies, "owner outside outer Copy")
            genealogy[rep], location[rep] = tree_json(tree), list(place)
            for copy in leaves:
                require(type(copy) is int and 0 <= copy < copies and ancestor[copy] is None,
                        "genealogy fibres overlap or escape outer Copy")
                validate_place(context, place, context["local_samples"][copy])
                ancestor[copy] = rep
        require(all(rep is not None for rep in ancestor), "genealogy fibres do not cover Copy")
        return {"live": [rep for rep, _, _ in self.roots], "ancestor": ancestor,
                "genealogy": genealogy, "location": location, "register": context["register"]}

    def view(self, context):
        raw = self.encode(context)
        return {"genealogy": [raw["genealogy"][rep] for rep in raw["ancestor"]],
                "location": [raw["location"][rep] for rep in raw["ancestor"]],
                "register": raw["register"]}

    def merge(self, first, second):
        current = {rep: (tree, place) for rep, tree, place in self.roots}
        a, place = current[first]
        b, other = current[second]
        require(first != second and place == other and place[0] in ("E", "A"),
                "forbidden mixed/node merger")
        current[first] = ((a, b), place)
        del current[second]
        return State(tuple((rep, tree, location) for rep, (tree, location) in sorted(current.items())))


def decode_state(context, raw):
    state = State(tuple((rep, freeze_tree(raw["genealogy"][rep]), tuple(raw["location"][rep]))
                        for rep in raw["live"]))
    require(exact_json(state.encode(context)) == exact_json(raw), "noncanonical snapshot encoding")
    return state


def validate_context(context):
    labels, samples = context["global_labels"], context["local_samples"]
    require(len(labels) == len(samples) <= 4 and len(set(labels)) == len(labels), "invalid Copy embedding")
    require(all(type(label) is int and 0 <= label < 4 for label in labels), "invalid global labels")
    require(all(type(sample) is int and 0 <= sample < len(context["leaves"]) for sample in samples),
            "invalid original samples")
    require(len(context["register"]) == context["vertices"]
            and all(type(bit) is bool for bit in context["register"]), "invalid original register")
    return decode_state(context, context["start"])


def rate(state, bank):
    counts = Counter(place for _, _, place in state.roots if place[0] in ("E", "A"))
    return sum(count*(count-1)//2 * bank[place] for place, count in counts.items())


def generator(context):
    start, bank = validate_context(context), weights(context)
    pending, seen, rows = deque([start]), {start}, {}
    while pending:
        state = pending.popleft()
        holding = rate(state, bank)
        row = {state: Fraction(-holding)} if holding else {}
        for first, _, place in state.roots:
            for second, _, other in state.roots:
                if first == second or place != other or place[0] not in ("E", "A"):
                    continue
                destination = state.merge(first, second)
                row[destination] = row.get(destination, Fraction(0)) + Fraction(bank[place], 2)
                if destination not in seen:
                    seen.add(destination)
                    pending.append(destination)
        require(sum(row.values(), Fraction(0)) == 0, "mixed generator mass loss")
        rows[state] = row
    return start, bank, rows


def apply_generator(vector, rows):
    answer = {}
    for state, coefficient in vector.items():
        for destination, entry in rows[state].items():
            answer[destination] = answer.get(destination, Fraction(0)) + coefficient*entry
    return {state: coefficient for state, coefficient in answer.items() if coefficient}


def powers(weighted_rate, dimension):
    answer = []
    for _ in range(dimension):
        weighted_rate, digit = divmod(weighted_rate, 7)
        answer.append(digit)
    require(weighted_rate == 0, "weighted exponent escaped original variable bank")
    return tuple(answer)


def spectral_coefficients(context):
    start, bank, rows = generator(context)
    rates = sorted({rate(state, bank) for state in rows})
    answer = {state: {} for state in rows}
    for selected_rate in rates:
        vector = {start: Fraction(1)}
        for other in rates:
            if selected_rate == other:
                continue
            product = apply_generator(vector, rows)
            for state, coefficient in vector.items():
                product[state] = product.get(state, Fraction(0)) + other*coefficient
            vector = {state: coefficient/Fraction(other-selected_rate)
                      for state, coefficient in product.items() if coefficient}
        image = apply_generator(vector, rows)
        require(image == {state: -selected_rate*value for state, value in vector.items()
                          if selected_rate*value}, "mixed spectral projector is not an eigenrow")
        monomial = powers(selected_rate, len(variables(context)))
        for state, value in vector.items():
            answer[state][monomial] = value
    answer = {state: polynomial for state, polynomial in answer.items() if polynomial}
    total = {}
    for state, polynomial in answer.items():
        require(sum(polynomial.values(), Fraction(0)) == (1 if state == start else 0),
                "mixed zero-duration identity incorrect")
        for monomial, value in polynomial.items():
            total[monomial] = total.get(monomial, Fraction(0)) + value
    require({monomial: value for monomial, value in total.items() if value}
            == {(0,)*len(variables(context)): Fraction(1)}, "mixed formal mass is not one")
    return answer


def terms(polynomial):
    return [[list(monomial), qwire(value)] for monomial, value in sorted(polynomial.items()) if value]


def full_rows(context, literal):
    answer, witnesses = {}, {}
    for state, polynomial in literal.items():
        key = exact_json(state.view(context))
        witnesses.setdefault(key, state.encode(context))
        target = answer.setdefault(key, {})
        for monomial, value in polynomial.items():
            target[monomial] = target.get(monomial, Fraction(0)) + value
    return [{"view": json.loads(key), "witness": witnesses[key], "coefficients": terms(polynomial)}
            for key, polynomial in sorted(answer.items())]


def unranked_key(context, view):
    roots = {}
    for copy, raw_tree in enumerate(view["genealogy"]):
        tree = freeze_tree(raw_tree)
        canonical = canonical_tree(tree, context["global_labels"])
        key = exact_json(tree_json(canonical))
        place = view["location"][copy]
        if key in roots:
            require(roots[key]["location"] == place, "one genealogy fibre has different original locations")
        roots[key] = {"tree": tree_json(canonical), "location": place}
    forest = sorted(roots.values(), key=lambda root: min(tree_leaves(freeze_tree(root["tree"]))))
    return exact_json({"forest": forest, "register": view["register"]})


def unranked_rows(context, rows):
    answer = {}
    for row in rows:
        key = unranked_key(context, row["view"])
        polynomial = answer.setdefault(key, {})
        for monomial, value in row["coefficients"]:
            monomial = tuple(monomial)
            polynomial[monomial] = polynomial.get(monomial, Fraction(0)) + Fraction(value)
    return [{**json.loads(key), "coefficients": terms(polynomial)} for key, polynomial in sorted(answer.items())]


def fixtures():
    ordinary = {"vertices": 3, "root": 0, "edges": [[0, 1], [0, 2]], "leaves": [1, 2], "hybrids": []}
    parallel = {"vertices": 5, "root": 0, "edges": [[0, 1], [0, 2], [2, 3], [2, 3], [3, 4]],
                "leaves": [1, 4], "hybrids": [[3, 2, 3]]}
    def context(samples, locations, *, source=ordinary, labels=None, roots=None, register=None):
        n = len(samples)
        result = {**source, "local_samples": samples, "global_labels": list(range(n)) if labels is None else labels,
                  "register": [False]*source["vertices"] if register is None else register}
        state = State(tuple((i, i, tuple(place)) for i, place in enumerate(locations)) if roots is None
                      else tuple((rep, tree, tuple(place)) for rep, tree, place in roots))
        result["start"] = state.encode(result)
        return result
    return {
        "empty": context([], []),
        "oneAncestral": context([0], [["A", 0]]),
        "nodeIdentity": context([0, 0], [["V", 1], ["V", 1]]),
        "twoEdgePanels": context([0, 0, 1, 1], [["E", 0], ["E", 0], ["E", 1], ["E", 1]]),
        "edgeAncestral": context([0, 0, 0, 1], [["E", 0], ["E", 0], ["A", 0], ["A", 0]]),
        "carriedNodeExterior": context([0, 0, 0, 1], [],
            roots=((2, ((0, 1), 2), ("V", 1)), (3, 3, ("A", 0)))),
        "permutedRestricted": context([0, 1, 0], [["E", 0], ["A", 0], ["E", 0]], labels=[3, 0, 2]),
        "frozenRegister": context([0, 0, 0, 1], [["E", 0], ["E", 0], ["A", 0], ["A", 0]],
            register=[True, False, True]),
        "parallelPanels": context([1, 1, 1, 1], [["E", 2], ["E", 2], ["E", 3], ["E", 3]],
            source=parallel, labels=[2, 0, 3, 1], register=[True, False, True, False, True]),
    }


def expected_probe(name, context):
    literal = spectral_coefficients(context)
    rows = full_rows(context, literal)
    expected = {"schema": "source_epoch_probe_v1", "fixture": name, "context": context,
                "variables": variables(context), "rows": rows}
    return expected, literal, unranked_rows(context, rows)


def check_probe(actual, expected, literal, unranked):
    require(set(expected) <= set(actual) <= set(expected)|{"work", "source_admission_established"},
            "epoch probe missing/unknown fields")
    require(actual.get("source_admission_established", False) is False, "epoch probe promoted source admission")
    if "work" in actual:
        require(set(actual["work"]) == {"calls", "lifted_terms", "largest_panel_row", "branches", "term_products"}
                and all(type(value) is int and value >= 0 for value in actual["work"].values()),
                "malformed observed epoch work")
    for field in ("schema", "fixture", "context", "variables"):
        require(exact_json(actual[field]) == exact_json(expected[field]), "epoch probe changed "+field)
    require(len(actual["rows"]) == len(expected["rows"]), "epoch full row census changed")
    for row in actual["rows"]:
        require(set(row) == {"view", "witness", "coefficients"}, "unknown/missing epoch destination field")
        witness = decode_state(expected["context"], row["witness"])
        require(witness in literal, "range witness is not in the actual fixture merger support")
        require(exact_json(witness.view(expected["context"])) == exact_json(row["view"]),
                "range witness does not encode the emitted selected view")
    def stripped(rows):
        return sorted(({"view": row["view"], "coefficients": row["coefficients"]} for row in rows), key=exact_json)
    require(exact_json(stripped(actual["rows"])) == exact_json(stripped(expected["rows"])),
            "complete full selected-view coefficients differ from mixed generator")
    require(exact_json(unranked_rows(expected["context"], actual["rows"])) == exact_json(unranked),
            "complete population-preserving global unranked pushforward changed")


def parse_json(raw):
    def object_fields(pairs):
        answer = {}
        for key, value in pairs:
            require(key not in answer, "duplicate JSON key")
            answer[key] = value
        return answer
    def reject(value):
        raise ValueError("nonfinite JSON value: "+value)
    return json.loads(raw, object_pairs_hook=object_fields, parse_constant=reject)


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "epoch review output already exists")
    output.mkdir(parents=True)
    source_files = [Path(__file__).resolve(), DESIGN/"population_oracle.py"]
    source_pins = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in source_files}
    for path in source_files:
        (output/path.name).write_bytes(path.read_bytes())
    probes = {name: path.resolve() for name, path in (("rust", args.rust_probe), ("lean", args.lean_probe)) if path}
    before = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in probes.items()}
    cases = []
    for name, context in fixtures().items():
        expected, literal, unranked = expected_probe(name, context)
        census = {"empty": (1, 1), "oneAncestral": (1, 1), "nodeIdentity": (1, 1),
                  "twoEdgePanels": (9, 4), "edgeAncestral": (9, 4), "carriedNodeExterior": (1, 1),
                  "permutedRestricted": (3, 2), "frozenRegister": (9, 4), "parallelPanels": (9, 4)}
        require((len(expected["rows"]), len(unranked)) == census[name], "mixed fixture census control failed")
        (output/(name+".expected.json")).write_text(json.dumps(expected, indent=2, sort_keys=True)+"\n")
        (output/(name+".unranked.json")).write_text(json.dumps(unranked, indent=2, sort_keys=True)+"\n")
        results, errors = {}, []
        for language, binary in probes.items():
            started = time.monotonic()
            result = {"command": [str(binary), name], "process_started": False, "exit_code": None}
            stdout, stderr = b"", b""
            try:
                process = subprocess.run(result["command"], capture_output=True, timeout=30)
                stdout, stderr = process.stdout, process.stderr
                result.update(process_started=True, exit_code=process.returncode)
                require(process.returncode == 0, "epoch probe failed")
                check_probe(parse_json(stdout), expected, literal, unranked)
            except subprocess.TimeoutExpired as error:
                result.update(process_started=True, timed_out=True)
                stdout, stderr = error.stdout or b"", error.stderr or b""
                errors.append(language+": execution timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language+": "+str(error))
            (output/(name+"."+language+".stdout")).write_bytes(stdout)
            (output/(name+"."+language+".stderr")).write_bytes(stderr)
            result.update(elapsed_seconds=time.monotonic()-started,
                          stdout_sha256=hashlib.sha256(stdout).hexdigest())
            results[language] = result
        cases.append({"fixture": name, "literal_support": len(literal), "selected_views": len(expected["rows"]),
                      "unranked_views": len(unranked), "runs": results, "errors": errors, "pass": not errors})
    after = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in probes.items()}
    source_after = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in source_files}
    receipt = {"schema": "mixed_source_epoch_spectral_review_v1",
               "executed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "algorithm": "Single mixed ordered-half-rate generator with base-seven weighted sparse spectral projectors",
               "source_admission_claim": False, "general_refinement_proof_claim": False,
               "observed_work_is_not_resource_proof": True, "languages_executed": list(probes),
               "binary_pins_before": before, "binary_pins_after": after,
               "source_pins_before": source_pins, "source_pins_after": source_after,
               "cases": cases, "cases_total": len(cases), "cases_passed": sum(case["pass"] for case in cases),
               "pass": all(case["pass"] for case in cases) and before == after and source_pins == source_after,
               "claim": "ORACLE_SELF_CHECK_ONLY" if not probes else "FINITE_MIXED_EPOCH_COEFFICIENT_REVIEW"}
    (output/"RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps({key: receipt[key] for key in ("claim", "pass", "cases_total", "cases_passed")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--lean-probe", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    raise SystemExit(run(parser.parse_args()))
