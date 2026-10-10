#!/usr/bin/env python3
"""Independent whole-Copy coin marginalization for conditional original boundaries.

Private finite fixture JSON. No public wire, source-admission or generic native
refinement claim. Enumerate all Copy bits and exactly cancel unused ones rather
than using the native current-owner assignment enumerator.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

from epoch_oracle import (State, decode_state, exact_json, full_rows, parse_json,
                          terms, unranked_rows, validate_context)
from population_oracle import require

DESIGN = Path(__file__).resolve().parent


def variables(context):
    return [["ORIGINAL_GAMMA", h] for h in range(len(context["hybrids"]))]


def add(target, source):
    for monomial, value in source.items():
        target[monomial] = target.get(monomial, Fraction(0)) + value
        if not target[monomial]:
            del target[monomial]


def multiply(left, right):
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            power = tuple(i+j for i, j in zip(a, b))
            result[power] = result.get(power, Fraction(0)) + x*y
    return {power: value for power, value in result.items() if value}


def coin_weight(bits, dimension, hybrid):
    zero = (0,)*dimension
    gamma = tuple(int(i == hybrid) for i in range(dimension))
    result = {zero: Fraction(1)}
    for bit in bits:
        result = multiply(result, {gamma: Fraction(1)} if bit
                          else {zero: Fraction(1), gamma: Fraction(-1)})
    return result


def affected(context, state, action):
    kind = action[0]
    if kind == "EXIT":
        require(len(action) == 2 and type(action[1]) is int
                and 0 <= action[1] < len(context["edges"]), "bad original exit")
        place = ("E", action[1])
    elif kind == "ORDINARY":
        require(len(action) == 2 and type(action[1]) is int
                and 0 <= action[1] < len(context["edges"]), "bad ordinary edge")
        target = context["edges"][action[1]][1]
        require(sum(edge[1] == target for edge in context["edges"]) == 1,
                "ordinary target lacks indegree-one premise")
        place = ("V", target)
    elif kind == "ROOT":
        require(len(action) == 1, "root action has unknown field")
        place = ("V", context["root"])
    else:
        require(kind in ("COMMON", "INDEPENDENT") and len(action) == 2
                and type(action[1]) is int and 0 <= action[1] < len(context["hybrids"]),
                "bad original hybrid action")
        site, first, second = context["hybrids"][action[1]]
        require(first != second and 0 <= first < len(context["edges"])
                and 0 <= second < len(context["edges"])
                and context["edges"][first][1] == site
                and context["edges"][second][1] == site,
                "wrong original parent registry")
        require(sum(edge[1] == site for edge in context["edges"]) == 2
                and sum(edge[0] == site for edge in context["edges"]) == 1,
                "parent site is not actual binary hybrid")
        place = ("V", site)
    return tuple(rep for rep, _, location in state.roots if location == place)


def destination(context, state, action, bits=()):
    owners = set(affected(context, state, action))
    kind = action[0]
    roots = []
    for rep, tree, place in state.roots:
        if rep in owners:
            if kind == "EXIT":
                place = ("V", context["edges"][action[1]][0])
            elif kind == "ORDINARY":
                place = ("E", action[1])
            elif kind == "ROOT":
                place = ("A", context["root"])
            else:
                site, parent0, parent1 = context["hybrids"][action[1]]
                bit = context["register"][site] if kind == "COMMON" else bits[rep]
                place = ("E", parent1 if bit else parent0)
        roots.append((rep, tree, place))
    result = State(tuple(roots))
    raw = result.encode(context)
    original = state.encode(context)
    for field in ("live", "ancestor", "genealogy", "register"):
        require(exact_json(raw[field]) == exact_json(original[field]),
                "boundary changes inherited "+field)
    return result


def coefficients(context, action):
    start = validate_context(context)
    dimension = len(variables(context))
    literal = {}
    if action[0] == "INDEPENDENT":
        # Coins on every outer Copy include carried/dead/outside copies. Only a
        # current owner at the named site uses its own bit. Exact marginalization
        # must remove all unused gamma factors.
        for bits in itertools.product((False, True), repeat=len(context["local_samples"])):
            result = destination(context, start, action, bits)
            add(literal.setdefault(result, {}), coin_weight(bits, dimension, action[1]))
    else:
        result = destination(context, start, action)
        literal[result] = {(0,)*dimension: Fraction(1)}
    literal = {state: row for state, row in literal.items() if row}
    mass = {}
    for row in literal.values():
        add(mass, row)
    require(mass == {(0,)*dimension: Fraction(1)}, "boundary formal mass is not exactly one")
    owners = len(affected(context, start, action))
    assignments = 2**owners if action[0] == "INDEPENDENT" else 1
    contributions = assignments + owners*2**(owners-1) if action[0] == "INDEPENDENT" and owners else 1
    work = {"owners": owners, "assignments": assignments,
            "destinations": assignments, "term_contributions": contributions}
    require(len(literal) == assignments, "literal destination count differs from original parent injection")
    if action[0] == "INDEPENDENT":
        require(all(power[action[1]] <= owners for row in literal.values() for power in row),
                "unused Copy coins survive exact marginalization")
    return literal, work


def fixtures():
    ordinary = {"vertices": 3, "root": 0, "edges": [[0, 1], [0, 2]],
                "leaves": [1, 2], "hybrids": []}
    parallel = {"vertices": 5, "root": 0,
                "edges": [[0, 1], [0, 2], [2, 3], [2, 3], [3, 4]],
                "leaves": [1, 4], "hybrids": [[3, 2, 3]]}

    def context(samples, places, source=parallel, labels=None, roots=None, register=None):
        n = len(samples)
        result = {**source, "local_samples": samples,
                  "global_labels": list(range(n)) if labels is None else labels,
                  "register": [False]*source["vertices"] if register is None else register}
        state = State(tuple((i, i, tuple(place)) for i, place in enumerate(places)) if roots is None
                      else tuple((rep, tree, tuple(place)) for rep, tree, place in roots))
        result["start"] = state.encode(result)
        return result

    false = [True, False, True, False, True]
    true = [True, False, True, True, True]
    return {
        "emptyCommon": (context([], [], register=true), ["COMMON", 0]),
        "emptyIndependent": (context([], [], register=false), ["INDEPENDENT", 0]),
        "commonFalse": (context([1, 1], [["V", 3], ["V", 3]], register=false), ["COMMON", 0]),
        "commonTrue": (context([1, 1], [["V", 3], ["V", 3]], register=true), ["COMMON", 0]),
        "independentTwo": (context([1, 1], [["V", 3], ["V", 3]], register=true), ["INDEPENDENT", 0]),
        "carriedOwnerOutside": (context([1, 1, 1, 0], [], register=false,
            roots=((2, ((0, 1), 2), ("V", 3)), (3, 3, ("V", 1)))), ["INDEPENDENT", 0]),
        "noOwnerAtSite": (context([1, 0], [["E", 2], ["V", 1]], register=true), ["INDEPENDENT", 0]),
        "parallelExit": (context([1, 1, 0], [["E", 2], ["E", 3], ["V", 1]], register=false), ["EXIT", 2]),
        "ordinaryEntry": (context([0, 1], [["V", 1], ["V", 2]], source=ordinary,
                                  register=[True, False, True]), ["ORDINARY", 0]),
        "rootEntry": (context([0, 1], [["V", 0], ["V", 0]], source=ordinary,
                              register=[True, True, False]), ["ROOT"]),
        "registerRepeat": (context([1, 0], [["V", 3], ["V", 1]],
                                   register=[False, True, False, False, False]), ["COMMON", 0]),
        "permutedIndependent": (context([1, 0, 1], [["V", 3], ["V", 1], ["V", 3]],
                                        labels=[3, 0, 2], register=false), ["INDEPENDENT", 0]),
    }


def expected_probe(name, context, action):
    literal, work = coefficients(context, action)
    rows = full_rows(context, literal)
    require(len(rows) == len(literal), "boundary full selected quotient unexpectedly identifies owners")
    return {"schema": "source_boundary_probe_v1", "fixture": name, "context": context,
            "action": action, "variables": variables(context), "rows": rows, "work": work,
            "source_admission_verified": False}, literal, unranked_rows(context, rows)


def evaluate(polynomial, gamma):
    answer = Fraction(0)
    for powers, raw in polynomial:
        term = Fraction(raw)
        for power in powers:
            term *= gamma**power
        answer += term
    return answer


def asymmetric_controls(expected):
    row = expected["independentTwo"]
    gamma = Fraction(1, 3)
    by_places = {tuple(tuple(place) for place in r["view"]["location"]):
                 evaluate(r["coefficients"], gamma) for r in row["rows"]}
    expected_weights = {(("E", 2), ("E", 2)): Fraction(4, 9),
                        (("E", 2), ("E", 3)): Fraction(2, 9),
                        (("E", 3), ("E", 2)): Fraction(2, 9),
                        (("E", 3), ("E", 3)): Fraction(1, 9)}
    require(by_places == expected_weights, "original gamma orientation differs from true/parent1")
    natural_first = 1-gamma
    formal_g = Fraction(2, 3)
    require(natural_first == formal_g and natural_first != gamma,
            "asymmetric LAW complement test does not separate direct binding")
    carried = expected["carriedOwnerOutside"]["rows"]
    require(len(carried) == 2 and sorted(evaluate(r["coefficients"], gamma) for r in carried)
            == [Fraction(1, 3), Fraction(2, 3)], "carried owner was re-coined per leaf")
    for r in carried:
        require(r["view"]["location"][0] == r["view"]["location"][1]
                == r["view"]["location"][2] and r["view"]["location"][3] == ["V", 1],
                "carried/outside fibre was moved incorrectly")
    context = fixtures()["parallelExit"][0]
    start = validate_context(context)
    ordered = destination(context, destination(context, destination(context, start,
                          ["EXIT", 2]), ["EXIT", 3]), ["ORDINARY", 1])
    reversed_order = destination(context, destination(context, destination(context, start,
                                 ["ORDINARY", 1]), ["EXIT", 2]), ["EXIT", 3])
    require(ordered != reversed_order, "own-node entry commuted across original exits")
    require(ordered.view(context)["location"][:2] == [["E", 1], ["E", 1]]
            and reversed_order.view(context)["location"][:2] == [["V", 2], ["V", 2]],
            "exit-before-entry direct original locations differ")
    return {"asymmetric_gamma": "1/3", "required_LAW_G": "2/3",
            "two_owner_weights": ["4/9", "2/9", "2/9", "1/9"],
            "carried_one_coin": True, "wrong_direct_gamma_binding_rejected": True,
            "exit_before_entry_separated": True}


def check_probe(actual, expected, literal, unranked):
    require(set(actual) == set(expected), "boundary missing/unknown top-level fields")
    for field in ("schema", "fixture", "context", "action", "variables", "work",
                  "source_admission_verified"):
        require(exact_json(actual[field]) == exact_json(expected[field]), "boundary changed "+field)
    require(len(actual["rows"]) == len(expected["rows"]), "boundary full destination census changed")
    for row in actual["rows"]:
        require(set(row) == {"view", "witness", "coefficients"}, "unknown boundary destination field")
        witness = decode_state(expected["context"], row["witness"])
        require(witness in literal, "boundary witness is not in actual literal action support")
        require(exact_json(witness.view(expected["context"])) == exact_json(row["view"]),
                "boundary witness differs from full selected key")
    def stripped(rows):
        return sorted(({"view": r["view"], "coefficients": r["coefficients"]} for r in rows), key=exact_json)
    require(exact_json(stripped(actual["rows"])) == exact_json(stripped(expected["rows"])),
            "complete conditional coefficients differ from whole-Copy marginalization")
    require(exact_json(unranked_rows(expected["context"], actual["rows"])) == exact_json(unranked),
            "population/register-preserving unranked boundary pushforward changed")


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "boundary review output already exists")
    output.mkdir(parents=True)
    sources = [Path(__file__).resolve(), DESIGN/"epoch_oracle.py", DESIGN/"population_oracle.py"]
    before_sources = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    for p in sources:
        (output/p.name).write_bytes(p.read_bytes())
    probes = {name: p.resolve() for name, p in (("rust", args.rust_probe), ("lean", args.lean_probe)) if p}
    before = {name: hashlib.sha256(p.read_bytes()).hexdigest() for name, p in probes.items()}
    cases, all_expected = [], {}
    for name, (context, action) in fixtures().items():
        expected, literal, unranked = expected_probe(name, context, action)
        all_expected[name] = expected
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
                require(process.returncode == 0, "boundary probe failed")
                check_probe(parse_json(stdout), expected, literal, unranked)
            except subprocess.TimeoutExpired as error:
                result.update(process_started=True, timed_out=True)
                stdout, stderr = error.stdout or b"", error.stderr or b""
                errors.append(language+": timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language+": "+str(error))
            (output/(name+"."+language+".stdout")).write_bytes(stdout)
            (output/(name+"."+language+".stderr")).write_bytes(stderr)
            result.update(elapsed_seconds=time.monotonic()-started,
                          stdout_sha256=hashlib.sha256(stdout).hexdigest())
            results[language] = result
        cases.append({"fixture": name, "literal_destinations": len(literal), "selected_views": len(expected["rows"]),
                      "unranked_views": len(unranked), "work": expected["work"],
                      "runs": results, "errors": errors, "pass": not errors})
    controls = asymmetric_controls(all_expected)
    after = {name: hashlib.sha256(p.read_bytes()).hexdigest() for name, p in probes.items()}
    after_sources = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    receipt = {"schema": "conditional_source_boundary_whole_copy_review_v1",
               "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "algorithm": "Whole outer-Copy coin enumeration with exact unused-bit marginalization",
               "source_admission_claim": False, "general_refinement_proof_claim": False,
               "languages_executed": list(probes), "binary_pins_before": before, "binary_pins_after": after,
               "source_pins_before": before_sources, "source_pins_after": after_sources,
               "controls": controls, "cases": cases, "cases_total": len(cases),
               "cases_passed": sum(c["pass"] for c in cases),
               "pass": all(c["pass"] for c in cases) and before == after and before_sources == after_sources,
               "claim": "ORACLE_SELF_CHECK_ONLY" if not probes else "FINITE_CONDITIONAL_BOUNDARY_COEFFICIENT_REVIEW"}
    (output/"RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps({key: receipt[key] for key in ("claim", "pass", "cases_total", "cases_passed")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--lean-probe", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    raise SystemExit(run(parser.parse_args()))
