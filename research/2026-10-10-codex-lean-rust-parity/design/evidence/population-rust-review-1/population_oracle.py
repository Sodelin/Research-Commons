#!/usr/bin/env python3
"""Independent exact ordered-snapshot generator oracle for population probes.

Sparse spectral projectors replace both recursive liftTerm and merger-history
path formulas. This is a finite implementation review, not a source-admission
or a general native-refinement proof. Test-only JSON has no RC1 wire status.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import time


DESIGN = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def qwire(value):
    return f"{value.numerator}/{value.denominator}"


def tree_leaves(tree):
    return (tree,) if isinstance(tree, int) else tree_leaves(tree[0])+tree_leaves(tree[1])


def freeze_tree(tree):
    if type(tree) is int:
        require(tree >= 0, "negative copied label")
        return tree
    require(isinstance(tree, (tuple, list)) and len(tree) == 2, "nonbinary ordered genealogy")
    return tuple(freeze_tree(child) for child in tree)


def canonical_tree(tree, labels):
    if isinstance(tree, int):
        return labels[tree]
    a, b = (canonical_tree(child, labels) for child in tree)
    return (a, b) if min(tree_leaves(a)) < min(tree_leaves(b)) else (b, a)


def tree_json(tree):
    return tree if isinstance(tree, int) else [tree_json(child) for child in tree]


def tree_wire(tree):
    return str(tree) if isinstance(tree, int) else "("+tree_wire(tree[0])+","+tree_wire(tree[1])+")"


@dataclass(frozen=True)
class Snapshot:
    # The complete partition recovers the original ancestor map. Dead option
    # fields are re-encoded as none, never retained as state distinctions.
    roots: tuple[tuple[int, object], ...]

    def validate(self, copies):
        reps = tuple(rep for rep, _ in self.roots)
        require(reps == tuple(sorted(set(reps))), "duplicate/unordered live representatives")
        labels = tuple(label for _, tree in self.roots for label in tree_leaves(tree))
        require(sorted(labels) == list(range(copies)), "genealogy fibres do not partition all local copies")
        for rep, tree in self.roots:
            require(rep in tree_leaves(tree), "representative not in its own fibre")

    def merge(self, first, second):
        trees = dict(self.roots)
        require(first != second and first in trees and second in trees, "illegal ordered pair")
        trees[first] = (trees[first], trees[second])
        del trees[second]
        return Snapshot(tuple(sorted(trees.items())))

    def encode(self, context):
        copies = len(context["global_labels"])
        self.validate(copies)
        ancestor, genealogy, location = [None]*copies, [None]*copies, [None]*copies
        for rep, tree in self.roots:
            genealogy[rep] = tree_json(tree)
            location[rep] = context["population"]
            for label in tree_leaves(tree):
                ancestor[label] = rep
        return {"live": [rep for rep, _ in self.roots], "ancestor": ancestor,
                "genealogy": genealogy, "location": location, "register": context["register"]}

    def forest(self, labels):
        trees = (canonical_tree(tree, labels) for _, tree in self.roots)
        return tuple(sorted(trees, key=lambda tree: min(tree_leaves(tree))))


def validate_context(context):
    # Fixed probe N is an actual ordinary two-tip RootedBinary shape. This
    # finite predicate review does not replace the Lean typed proof premise.
    require(context["vertices"] == 3 and context["root"] == 0 and context["edges"] == [[0, 1], [0, 2]]
            and context["leaves"] == [1, 2] and context["hybrids"] == [], "unexpected probe source")
    labels, samples = context["global_labels"], context["local_samples"]
    require(len(labels) == len(samples) <= 4 and len(set(labels)) == len(labels)
            and all(type(label) is int and 0 <= label < 4 for label in labels), "invalid local/global copy embedding")
    require(all(type(taxon) is int and 0 <= taxon < 2 for taxon in samples), "invalid original sample assignment")
    register = context["register"]
    require(len(register) == 3 and all(type(bit) is bool for bit in register), "invalid original V register")
    population = context["population"]
    if population[0] == "A":
        require(population == ["A", 0], "ancestral tag must retain original root")
    else:
        require(population in (["E", 0], ["E", 1]), "node/unknown location cannot coalesce")
        require(all(taxon == population[1] for taxon in samples), "local sample does not descend from original edge")
    start = context["start"]
    roots = Snapshot(tuple((rep, freeze_tree(start["genealogy"][rep])) for rep in start["live"]))
    require(roots.encode(context) == start, "snapshot options/ancestors/register do not match original encoding")
    return roots


def ordered_successors(snapshot):
    for first, _ in snapshot.roots:
        for second, _ in snapshot.roots:
            if first != second:
                yield snapshot.merge(first, second)


def generator(context):
    start = validate_context(context)
    queue, seen, rows = deque([start]), {start}, {}
    while queue:
        state = queue.popleft()
        k = len(state.roots)
        rate = k*(k-1)//2
        row = {state: Fraction(-rate)} if rate else {}
        for destination in ordered_successors(state):
            row[destination] = row.get(destination, Fraction(0))+Fraction(1, 2)
            if destination not in seen:
                seen.add(destination)
                queue.append(destination)
        require(sum(row.values(), Fraction(0)) == 0, "generator row does not conserve probability")
        rows[state] = row
    return start, rows


def apply_generator(vector, rows):
    result = {}
    for state, value in vector.items():
        for destination, entry in rows[state].items():
            result[destination] = result.get(destination, Fraction(0))+value*entry
    return {state: value for state, value in result.items() if value}


def spectral_coefficients(context):
    start, rows = generator(context)
    rates = sorted({len(state.roots)*(len(state.roots)-1)//2 for state in rows})
    answer = {state: {} for state in rows}
    for rate in rates:
        vector = {start: Fraction(1)}
        for other in rates:
            if rate == other:
                continue
            product = apply_generator(vector, rows)
            for state, value in vector.items():
                product[state] = product.get(state, Fraction(0))+other*value
            vector = {state: value/Fraction(other-rate) for state, value in product.items() if value}
        for state, value in vector.items():
            answer[state][rate] = value
    answer = {state: polynomial for state, polynomial in answer.items() if polynomial}
    # Check the projector construction against the generator differential
    # equation and the zero-duration identity. Both are exact polynomials.
    for rate in rates:
        vector = {state: polynomial[rate] for state, polynomial in answer.items() if rate in polynomial}
        image = apply_generator(vector, rows)
        require(image == {state: -rate*value for state, value in vector.items() if rate*value},
                "spectral row is not a generator eigenrow")
    for state, polynomial in answer.items():
        require(sum(polynomial.values(), Fraction(0)) == (1 if state == start else 0), "zero-duration law incorrect")
    total = {}
    for polynomial in answer.values():
        for rate, value in polynomial.items():
            total[rate] = total.get(rate, Fraction(0))+value
    require({rate: value for rate, value in total.items() if value} == {0: Fraction(1)}, "formal row mass is not one")
    return answer


def expected_probe(name, context):
    literal = spectral_coefficients(context)
    rows, quotient = [], {}
    for state, polynomial in literal.items():
        row = state.encode(context)
        row["coefficients"] = [[rate, qwire(value)] for rate, value in sorted(polynomial.items())]
        rows.append(row)
        forest = state.forest(context["global_labels"])
        target = quotient.setdefault(forest, {})
        for rate, value in polynomial.items():
            target[rate] = target.get(rate, Fraction(0))+value
    unordered = [{"forest": [tree_json(tree) for tree in forest],
                  "coefficients": [[rate, qwire(value)] for rate, value in sorted(polynomial.items()) if value]}
                 for forest, polynomial in quotient.items()]
    return {"schema": "source_population_probe_v1", "fixture": name, "context": context,
            "rows": sorted(rows, key=lambda value: json.dumps(value, sort_keys=True)),
            "unordered": sorted(unordered, key=lambda value: json.dumps(value["forest"]))}


def fixtures():
    def context(labels, samples, population, roots=None, register=(False, False, False)):
        result = {"vertices": 3, "root": 0, "edges": [[0, 1], [0, 2]], "leaves": [1, 2], "hybrids": [],
                  "global_labels": list(labels), "local_samples": list(samples), "population": list(population),
                  "register": list(register)}
        snapshot = Snapshot(tuple(roots) if roots is not None else tuple((i, i) for i in range(len(labels))))
        result["start"] = snapshot.encode(result)
        return result
    return {
        "emptyEdge0": context([], [], ("E", 0)),
        "oneAncestral": context([0], [0], ("A", 0)),
        "twoAncestral": context([0, 1], [0, 1], ("A", 0)),
        "threeEdge0": context([0, 1, 2], [0, 0, 0], ("E", 0), register=(False, True, False)),
        "fourAncestral": context([0, 1, 2, 3], [0, 1, 0, 1], ("A", 0)),
        "carriedNonminimum": context([0, 1, 2, 3], [0, 1, 0, 1], ("A", 0), roots=((2, ((0, 1), 2)), (3, 3))),
        "permutedRestrictedEdge0": context([3, 0, 2], [0, 0, 0], ("E", 0)),
        "frozenRegisterRepeat": context([0, 1, 2], [0, 0, 0], ("E", 0), register=(True, False, True)),
    }


def check_probe(actual, expected):
    require(set(actual) == set(expected), "probe missing/unknown fields")
    for field in ("schema", "fixture", "context"):
        require(actual[field] == expected[field], "probe changed " + field)
    for field in ("rows", "unordered"):
        normalized = sorted(actual[field], key=lambda value: json.dumps(value, sort_keys=True))
        wanted = sorted(expected[field], key=lambda value: json.dumps(value, sort_keys=True))
        require(normalized == wanted, "complete " + field + " differs from ordered-generator spectral coefficients")


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "population review output already exists")
    output.mkdir(parents=True)
    own = Path(__file__).resolve()
    own_sha = hashlib.sha256(own.read_bytes()).hexdigest()
    (output / "population_oracle.py").write_bytes(own.read_bytes())
    probes = {name: path.resolve() for name, path in (("rust", args.rust_probe), ("lean", args.lean_probe)) if path}
    binary_pins = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in probes.items()}
    cases = []
    for name, context in fixtures().items():
        expected = expected_probe(name, context)
        (output / (name + ".expected.json")).write_text(json.dumps(expected, indent=2, sort_keys=True)+"\n")
        results, errors = {}, []
        for language, binary in probes.items():
            start = time.monotonic()
            process = subprocess.run([str(binary), name], capture_output=True, timeout=30)
            (output / (name+"."+language+".stdout")).write_bytes(process.stdout)
            (output / (name+"."+language+".stderr")).write_bytes(process.stderr)
            results[language] = {"exit_code": process.returncode, "process_started": True,
                                 "elapsed_seconds": time.monotonic()-start,
                                 "stdout_sha256": hashlib.sha256(process.stdout).hexdigest()}
            try:
                require(process.returncode == 0, language+" probe failed")
                check_probe(json.loads(process.stdout), expected)
            except (ValueError, TypeError, KeyError) as error:
                errors.append(language+": "+str(error))
        cases.append({"fixture": name, "literal_rows": len(expected["rows"]),
                      "unordered_rows": len(expected["unordered"]), "native_runs": results,
                      "errors": errors, "pass": not errors})
    after = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in probes.items()}
    receipt = {"schema": "ordered_snapshot_spectral_review_v1", "source_admission_claim": False,
               "general_refinement_proof_claim": False, "native_languages_executed": list(probes),
               "oracle_algorithm": "Sparse spectral row projectors of literal ordered-half-rate generator",
               "executed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "binary_pins_before": binary_pins, "binary_pins_after": after,
               "oracle_sha256": own_sha, "cases": cases, "cases_total": len(cases),
               "cases_passed": sum(case["pass"] for case in cases),
               "pass": all(case["pass"] for case in cases) and binary_pins == after,
               "claim": "ORACLE_SELF_CHECK_ONLY" if not probes else "FINITE_NATIVE_LITERAL_POPULATION_COEFFICIENT_REVIEW"}
    (output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps({key: receipt[key] for key in ("claim", "pass", "cases_total", "cases_passed")}))
    return 0 if receipt["pass"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--lean-probe", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    return run(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
