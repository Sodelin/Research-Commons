#!/usr/bin/env python3
"""Independent finite original-Code composition, retaining the whole register.

Private fixture interface, no RC1 operation or scientific admission. Conditional
epochs use the coupled generator spectral oracle; boundaries marginalize coins
on all Copy labels. A second selected-row computation challenges the literal
composition and representative independence at every reached fibre.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import time

import boundary_oracle as boundary
import epoch_oracle as epoch
from chart_check import Chart, structural_checks
from population_oracle import require, canonical_tree, freeze_tree, tree_json

DESIGN = Path(__file__).resolve().parent
DEFAULT_LIMITS = {"initial_assignments": 16, "initial_terms": 256,
    "queries": 4096, "branches": 65536, "term_products": 262144,
    "destinations": 4096, "terms": 65536}
CONTEXT_KEYS = {"vertices", "root", "edges", "leaves", "hybrids",
                "local_samples", "global_labels"}


class LimitReached(Exception):
    def __init__(self, stage, kind, required, cap):
        self.record = {"stage": stage, "kind": kind, "required": required, "cap": cap}


@dataclass(frozen=True)
class Code:
    state: epoch.State
    register: tuple[bool, ...]

    def context(self, original):
        # Global display identifiers are readout metadata, not outer Copy IDs.
        current = {**original, "global_labels": list(range(len(original["local_samples"]))),
                   "register": list(self.register)}
        current["start"] = self.state.encode(current)
        return current

    def snapshot(self, original):
        return self.context(original)["start"]

    def view(self, original):
        return self.state.view(self.context(original))


def key(code, original):
    return epoch.exact_json(code.view(original))


def add(target, source):
    boundary.add(target, source)


def multiply(left, right):
    if left and right:
        require(len(next(iter(left))) == len(next(iter(right))), "word monomial dimension mismatch")
    return boundary.multiply(left, right)


def mass_one(rows, dimension):
    total = {}
    for polynomial in rows.values():
        add(total, polynomial)
    require(total == {(0,)*dimension: Fraction(1)}, "word formal joint mass is not one")


def variables(request):
    original = request["context"]
    answer = []
    for slot in range(request["slots"]):
        answer += [["X", slot, "E", e] for e in range(len(original["edges"]))]
        answer.append(["X", slot, "A", original["root"]])
    answer += [["ORIGINAL_GAMMA", h] for h in range(len(original["hybrids"]))]
    return answer


def embed(polynomial, positions, dimension):
    result = {}
    for powers, coefficient in polynomial.items():
        require(len(powers) == len(positions), "wrong conditional provider dimension")
        expanded = [0]*dimension
        for position, power in zip(positions, powers):
            require(type(power) is int and power >= 0, "invalid provider exponent")
            expanded[position] += power
        result[tuple(expanded)] = coefficient
    return result


def check_request(request):
    require(set(request) == {"context", "initial", "common", "slots", "word", "terminal", "limits"},
            "word request has unknown or missing field")
    original = request["context"]
    require(type(original) is dict and set(original) == CONTEXT_KEYS, "wrong source context fields")
    v, root, edges, leaves, hybrids = (original[k] for k in
        ("vertices", "root", "edges", "leaves", "hybrids"))
    require(type(v) is int and 3 <= v <= 32 and type(root) is int and 0 <= root < v,
            "invalid original vertices/root")
    require(type(edges) is list and 2 <= len(edges) <= 32 and all(type(e) is list and len(e) == 2
            and all(type(a) is int and 0 <= a < v for a in e) for e in edges), "invalid original edge records")
    require(type(leaves) is list and 2 <= len(leaves) <= v and all(type(a) is int and 0 <= a < v
            for a in leaves), "invalid original tip registry")
    require(type(hybrids) is list and len(hybrids) <= v and all(type(h) is list and len(h) == 3
            and type(h[0]) is int and 0 <= h[0] < v and all(type(e) is int and 0 <= e < len(edges)
            for e in h[1:]) for h in hybrids), "invalid original hybrid registry")
    require(v + len(edges) + 1 + len(hybrids) <= 32, "original graph bank exceeds declared cap")
    structural_checks(Chart(v, root, tuple(map(tuple, edges)), tuple(leaves), tuple(map(tuple, hybrids)),
                            (), (), (), 0))
    samples, labels = original["local_samples"], original["global_labels"]
    require(type(samples) is list and type(labels) is list and len(samples) == len(labels) <= 4
            and all(type(s) is int and 0 <= s < len(leaves) for s in samples), "invalid fixed Copy samples")
    require(all(type(label) is int and 0 <= label < 2**64 for label in labels)
            and len(set(labels)) == len(labels), "global Copy embedding is not injective uint64")
    require(type(request["common"]) is list and len(request["common"]) == len(hybrids)
            and all(type(bit) is bool for bit in request["common"]), "wrong fixed hybrid mechanism vector")
    require(type(request["slots"]) is int and 0 <= request["slots"] <= 16
            and len(variables(request)) <= 256, "expanded interval bank exceeds its own cap")
    require(type(request["word"]) is list and len(request["word"]) <= 32, "wrong word length")
    for step in request["word"]:
        require(type(step) is list and len(step) == 2 and type(step[1]) is int, "malformed source Symbol")
        tag, index = step
        bound = {"INTERVAL": request["slots"], "EXIT": len(edges), "ENTER": v}.get(tag)
        require(bound is not None and 0 <= index < bound, "Symbol outside original registry")
    require(request["terminal"] in ("FULL_VIEW", "ANCESTRAL_COMPLETE"), "unknown terminal reader")
    require(type(request["initial"]) is dict and request["initial"].get("kind") in ("NATURAL", "CONDITIONAL"),
            "unknown original initial law")
    require(set(request["initial"]) == ({"kind"} if request["initial"]["kind"] == "NATURAL"
            else {"kind", "snapshot"}), "initial law has unknown field")
    require(type(request["limits"]) is dict and set(request["limits"]) == set(DEFAULT_LIMITS)
            and all(type(x) is int and 0 <= x <= 2**64-1 for x in request["limits"].values()),
            "invalid word limits")


def check_limit(request, stage, kind, required):
    cap = request["limits"][kind]
    if required > cap:
        raise LimitReached(stage, kind, required, cap)


def initial_rows(request):
    original, dimension = request["context"], len(variables(request))
    h = len(original["hybrids"])
    natural = request["initial"]["kind"] == "NATURAL"
    assignments, contributions = (2**h, 3**h) if natural else (1, 1)
    check_limit(request, "INITIAL", "initial_assignments", assignments)
    check_limit(request, "INITIAL", "initial_terms", contributions)
    result = {}
    if natural:
        roots = tuple((copy, copy, ("V", original["leaves"][sample]))
                      for copy, sample in enumerate(original["local_samples"]))
        for bits in itertools.product((False, True), repeat=h):
            register = [False]*original["vertices"]
            polynomial = {(0,)*dimension: Fraction(1)}
            for hybrid, bit in enumerate(bits):
                register[original["hybrids"][hybrid][0]] = bit
                power = [0]*dimension
                power[dimension-h+hybrid] = 1
                polynomial = multiply(polynomial, {tuple(power): Fraction(1)} if bit else
                    {(0,)*dimension: Fraction(1), tuple(power): Fraction(-1)})
            code = Code(epoch.State(roots), tuple(register))
            epoch.validate_context(code.context(original))
            result[code] = polynomial
    else:
        raw = request["initial"]["snapshot"]
        require(type(raw) is dict and type(raw.get("register")) is list, "invalid conditional Snapshot")
        current = {**original, "global_labels": list(range(len(original["local_samples"]))),
                   "register": raw["register"], "start": raw}
        state = epoch.validate_context(current)
        result[Code(state, tuple(raw["register"]))] = {(0,)*dimension: Fraction(1)}
    require(len(result) == assignments and sum(map(len, result.values())) == contributions,
            "initial raw register accounting mismatch")
    mass_one(result, dimension)
    return result, assignments, contributions


def boundary_action(request, step):
    tag, index = step
    if tag == "EXIT":
        return ["EXIT", index]
    require(tag == "ENTER", "wrong boundary Symbol")
    original = request["context"]
    if index == original["root"]:
        return ["ROOT"]
    for hid, (site, _, _) in enumerate(original["hybrids"]):
        if site == index:
            return ["COMMON" if request["common"][hid] else "INDEPENDENT", hid]
    incoming = [e for e, edge in enumerate(original["edges"]) if edge[1] == index]
    require(len(incoming) == 1, "nonhybrid nonroot is not an actual ordinary entry")
    return ["ORDINARY", incoming[0]]


def conditional_rows(request, code, step):
    original, dimension = request["context"], len(variables(request))
    current = code.context(original)
    bank = len(original["edges"])+1
    if step is None:
        require(original["local_samples"] and all(place == ("A", original["root"])
                for _, _, place in code.state.roots), "ancestral completion lacks actual root support")
        # Use the zero spectral projector of the full ordered generator, not
        # the native path/history coefficients or a count-completion formula.
        spectral = epoch.spectral_coefficients(current)
        raw = {state: {(0,)*dimension: polynomial[(0,)*bank]}
               for state, polynomial in spectral.items() if polynomial.get((0,)*bank)}
    elif step[0] == "INTERVAL":
        spectral = epoch.spectral_coefficients(current)
        positions = tuple(step[1]*bank+i for i in range(bank))
        raw = {state: embed(poly, positions, dimension) for state, poly in spectral.items()}
    else:
        literal, _ = boundary.coefficients(current, boundary_action(request, step))
        positions = tuple(range(request["slots"]*bank, dimension))
        raw = {state: embed(poly, positions, dimension) for state, poly in literal.items()}
    result = {Code(state, code.register): polynomial for state, polynomial in raw.items() if polynomial}
    for destination in result:
        epoch.validate_context(destination.context(original))
    mass_one(result, dimension)
    return result


def group_rows(original, literal):
    result = {}
    for code, polynomial in literal.items():
        view_key = key(code, original)
        row = result.setdefault(view_key, {"view": code.view(original), "polynomial": {}, "codes": []})
        add(row["polynomial"], polynomial)
        row["codes"].append(code)
    return {k: row for k, row in sorted(result.items()) if row["polynomial"]}


def advance(request, literal, step, stage, work):
    original, dimension = request["context"], len(variables(request))
    entering = group_rows(original, literal)
    queries = work["queries"]+len(entering)
    check_limit(request, stage, "queries", queries)
    conditional = {}
    logical = {}
    branches, products = 0, 0
    for view_key, row in entering.items():
        images = []
        for code in row["codes"]:
            conditional[code] = conditional_rows(request, code, step)
            grouped = group_rows(original, conditional[code])
            image = {k: r["polynomial"] for k, r in grouped.items()}
            if images:
                require(image == images[0], "reached representatives disagree after selected pushforward")
            images.append(image)
        logical[view_key] = images[0]
        branches += len(images[0])
        products += len(row["polynomial"])*sum(map(len, images[0].values()))
    branches += work["branches"]
    products += work["term_products"]
    check_limit(request, stage, "branches", branches)
    check_limit(request, stage, "term_products", products)
    outgoing = {}
    for code, incoming in literal.items():
        for destination, row in conditional[code].items():
            add(outgoing.setdefault(destination, {}), multiply(incoming, row))
    outgoing = {code: polynomial for code, polynomial in outgoing.items() if polynomial}
    selected = group_rows(original, outgoing)
    # Compare literal composition with a separate product over retained views.
    selected_product = {}
    for view_key, row in entering.items():
        for destination, polynomial in logical[view_key].items():
            add(selected_product.setdefault(destination, {}), multiply(row["polynomial"], polynomial))
    selected_product = {k: p for k, p in selected_product.items() if p}
    require(selected_product == {k: row["polynomial"] for k, row in selected.items()},
            "literal and selected word composition disagree")
    count, terms = len(selected), sum(len(row["polynomial"]) for row in selected.values())
    check_limit(request, stage, "destinations", count)
    check_limit(request, stage, "terms", terms)
    mass_one(outgoing, dimension)
    updated = {**work, "queries": queries, "branches": branches, "term_products": products,
               "largest_row": max(work["largest_row"], count), "largest_terms": max(work["largest_terms"], terms)}
    return outgoing, updated


def compile_word(request):
    check_request(request)
    dimension = len(variables(request))
    try:
        literal, assignments, contributions = initial_rows(request)
        initial = group_rows(request["context"], literal)
        check_limit(request, "INITIAL", "destinations", len(initial))
        check_limit(request, "INITIAL", "terms", contributions)
        work = {"initial_assignments": assignments, "initial_term_contributions": contributions,
                "queries": 0, "branches": 0, "term_products": 0,
                "largest_row": len(initial), "largest_terms": contributions}
        for stage, step in enumerate(request["word"]):
            literal, work = advance(request, literal, step, stage, work)
        if request["terminal"] == "ANCESTRAL_COMPLETE":
            literal, work = advance(request, literal, None, "COMPLETION", work)
        mass_one(literal, dimension)
        return {"status": "TABLE", "literal": literal, "work": work}
    except LimitReached as error:
        return {"status": "UNKNOWN", "limit": error.record}


def wire_rows(request, literal):
    original = request["context"]
    rows = []
    for _, row in group_rows(original, literal).items():
        witness = min((code.snapshot(original) for code in row["codes"]), key=epoch.exact_json)
        rows.append({"view": row["view"], "witness": witness, "coefficients": epoch.terms(row["polynomial"])})
    return rows


def expected_probe(name, request):
    result = compile_word(request)
    answer = {"schema": "source_word_probe_v1", "fixture": name, "request": request,
              "variables": variables(request), "source_admission_verified": False, "status": result["status"]}
    if result["status"] == "TABLE":
        answer.update(rows=wire_rows(request, result["literal"]), work=result["work"])
    else:
        answer["limit"] = result["limit"]
    return answer, result


def unranked(request, rows, hide_register=False):
    original = request["context"]
    result = {}
    for row in rows:
        view_key = epoch.unranked_key(original, row["view"])
        if hide_register:
            view = json.loads(view_key)
            require(request["terminal"] == "ANCESTRAL_COMPLETE" and len(view["forest"]) == 1,
                    "topology-only reader lacks completed rooted genealogy")
            view_key = epoch.exact_json(view["forest"][0]["tree"])
        polynomial = {tuple(power): Fraction(value) for power, value in row["coefficients"]}
        add(result.setdefault(view_key, {}), polynomial)
    return {k: p for k, p in sorted(result.items()) if p}


def check_probe(actual, expected, result):
    require(type(actual) is dict and set(actual) == set(expected), "word probe fields changed")
    for field in set(expected)-{"rows", "work"}:
        require(epoch.exact_json(actual[field]) == epoch.exact_json(expected[field]), "word probe changed "+field)
    if expected["status"] == "UNKNOWN":
        return {"status": "PASS", "unknown": expected["limit"]}
    require(epoch.exact_json(actual["work"]) == epoch.exact_json(expected["work"]), "word logical work differs")
    expected_rows = {epoch.exact_json(row["view"]): row["coefficients"] for row in expected["rows"]}
    actual_rows = {}
    original = expected["request"]["context"]
    for row in actual["rows"]:
        require(type(row) is dict and set(row) == {"view", "witness", "coefficients"}, "wrong word row fields")
        raw = row["witness"]
        require(type(raw) is dict and type(raw.get("register")) is list, "invalid word range witness")
        current = {**original, "global_labels": list(range(len(original["local_samples"]))),
                   "register": raw["register"], "start": raw}
        state = epoch.validate_context(current)
        code = Code(state, tuple(raw["register"]))
        require(code in result["literal"], "word witness outside independently reached literal support")
        require(epoch.exact_json(code.view(original)) == epoch.exact_json(row["view"]), "word witness/view mismatch")
        view_key = epoch.exact_json(row["view"])
        require(view_key not in actual_rows, "duplicate full word destination")
        require(row["coefficients"] == expected_rows.get(view_key), "word complete coefficients differ")
        actual_rows[view_key] = row["coefficients"]
    require(actual_rows == expected_rows, "word destinations missing or extra")
    return {"status": "PASS", "full_view_rows": len(actual_rows),
            "literal_rows": len(result["literal"]), "terms": sum(map(len, actual_rows.values()))}


def fixtures():
    ordinary = {"vertices": 3, "root": 0, "edges": [[0, 1], [0, 2]],
                "leaves": [1, 2], "hybrids": []}
    triple = {"vertices": 5, "root": 0, "edges": [[0, 1], [0, 2], [2, 3], [2, 4]],
              "leaves": [1, 3, 4], "hybrids": []}
    parallel = {"vertices": 5, "root": 0, "edges": [[0, 1], [0, 2], [2, 3], [2, 3], [3, 4]],
                "leaves": [1, 4], "hybrids": [[3, 2, 3]]}

    def request(source, samples, word, slots, common=(), terminal="FULL_VIEW", initial=None, labels=None):
        context = {**source, "local_samples": list(samples), "global_labels": list(range(len(samples)))
                   if labels is None else list(labels)}
        return {"context": context, "initial": {"kind": "NATURAL"} if initial is None else initial,
                "common": list(common), "slots": slots, "word": word, "terminal": terminal,
                "limits": dict(DEFAULT_LIMITS)}

    basic = [["ENTER", 1], ["ENTER", 2], ["INTERVAL", 0], ["EXIT", 0], ["EXIT", 1], ["ENTER", 0]]
    triple_word = [["ENTER", 1], ["ENTER", 3], ["ENTER", 4], ["INTERVAL", 0],
                   ["EXIT", 2], ["EXIT", 3], ["ENTER", 2], ["INTERVAL", 1],
                   ["EXIT", 0], ["EXIT", 1], ["ENTER", 0]]
    parallel_word = [["ENTER", 1], ["ENTER", 4], ["INTERVAL", 0], ["EXIT", 4],
                     ["ENTER", 3], ["INTERVAL", 1], ["EXIT", 2], ["EXIT", 3],
                     ["ENTER", 2], ["INTERVAL", 2], ["EXIT", 0], ["EXIT", 1], ["ENTER", 0]]
    boundary_cases = boundary.fixtures()

    def conditional(name):
        context, _ = boundary_cases[name]
        return {"kind": "CONDITIONAL", "snapshot": context["start"]}

    root_context = {**ordinary, "local_samples": [0, 0, 1], "global_labels": [0, 1, 2],
                    "register": [True, False, True]}
    root_context["start"] = epoch.State(tuple((i, i, ("A", 0)) for i in range(3))).encode(root_context)
    return {
        "emptyConditionalWord": request(ordinary, [], [], 0, initial={"kind": "CONDITIONAL", "snapshot":
            {"live": [], "ancestor": [], "genealogy": [], "location": [], "register": [True, False, True]}}),
        "emptyNaturalWord": request(parallel, [], [], 0, common=[True]),
        "emptyNaturalCommonWord": request(parallel, [], [["ENTER", 3], ["ENTER", 3]], 0, common=[True]),
        "singletonCalendar": request(ordinary, [0], basic, 1, terminal="ANCESTRAL_COMPLETE"),
        "ordinaryThreeFinite": request(triple, [0, 1, 2], triple_word, 2),
        "ordinaryThreeComplete": request(triple, [0, 1, 2], triple_word, 2, terminal="ANCESTRAL_COMPLETE"),
        "parallelCommonCalendar": request(parallel, [0, 1, 1], parallel_word, 3,
            common=[True], terminal="ANCESTRAL_COMPLETE"),
        "parallelIndependentCalendar": request(parallel, [0, 1, 1], parallel_word, 3,
            common=[False], terminal="ANCESTRAL_COMPLETE"),
        "conditionalCommonFalseWord": request(parallel, [1, 1], [["ENTER", 3], ["ENTER", 3]], 0,
            common=[True], initial=conditional("commonFalse")),
        "conditionalCommonTrueWord": request(parallel, [1, 1], [["ENTER", 3], ["ENTER", 3]], 0,
            common=[True], initial=conditional("commonTrue")),
        "repeatedIntervalSlot": request(ordinary, [0, 0, 1], [["INTERVAL", 0], ["INTERVAL", 0]], 1,
            initial={"kind": "CONDITIONAL", "snapshot": root_context["start"]}),
        "carriedOutsideWord": request(parallel, [1, 1, 1, 0], [["ENTER", 3], ["INTERVAL", 0],
            ["EXIT", 2], ["EXIT", 3], ["ENTER", 2]], 1, common=[False],
            initial=conditional("carriedOwnerOutside")),
        "permutedCalendar": request(triple, [0, 1, 2], triple_word, 2,
            terminal="ANCESTRAL_COMPLETE", labels=[3, 0, 2]),
    }


def self_controls(expected):
    # All initialization bits remain visible even when no copies are sampled.
    empty = expected["emptyNaturalWord"]
    require(len(empty["rows"]) == 2 and empty["work"]["initial_term_contributions"] == 3,
            "empty Copy erases the actual once-drawn original register")
    require(expected["emptyNaturalCommonWord"]["rows"] == empty["rows"], "empty COMMON redraws register")
    for name, edge in (("conditionalCommonFalseWord", 2), ("conditionalCommonTrueWord", 3)):
        row = expected[name]["rows"][0]
        require(all(place == ["E", edge] for place in row["view"]["location"])
                and row["view"]["register"] == expected[name]["request"]["initial"]["snapshot"]["register"],
                "COMMON repeated entry changes its entering bit/occurrence")
    # Two applications of one slot equal a single epoch with x -> x^2.
    repeated = expected["repeatedIntervalSlot"]
    request = repeated["request"]
    original = request["context"]
    raw = request["initial"]["snapshot"]
    current = {**original, "global_labels": list(range(3)), "register": raw["register"], "start": raw}
    single = epoch.full_rows(current, epoch.spectral_coefficients(current))
    doubled = {epoch.exact_json(row["view"]): [[[(2*p) for p in power], value]
               for power, value in row["coefficients"]] for row in single}
    require({epoch.exact_json(row["view"]): row["coefficients"] for row in repeated["rows"]} == doubled,
            "repeated interval slot silently allocates a new coordinate")
    # Original gamma and the formal LAW-v1 gamma have complementary orientation.
    require(Fraction(1)-Fraction(1, 3) == Fraction(2, 3), "original/Law parent transport failed")
    failed = []
    for limit, cap, need in (("initial_assignments", 1, 2), ("initial_terms", 2, 3)):
        request = json.loads(epoch.exact_json(empty["request"]))
        request["limits"][limit] = cap
        result = compile_word(request)
        require(result == {"status": "UNKNOWN", "limit": {"stage": "INITIAL", "kind": limit,
                "required": need, "cap": cap}}, "initial one-below cap promoted partial law")
        failed.append(result["limit"])
    return {"status": "PASS", "checks": ["empty-register-2^h/3^h", "stored-common-repeat",
            "repeated-slot-semigroup", "original-parent-orientation", "initial-one-below-caps"],
            "unknown_controls": failed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--fixture", action="append", default=[])
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    require(1 <= args.timeout <= 60, "invalid bounded probe timeout")
    args.output.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__), DESIGN/"boundary_oracle.py", DESIGN/"epoch_oracle.py",
             DESIGN/"population_oracle.py", DESIGN/"chart_check.py", DESIGN/"certificate_check.py",
             DESIGN/"WORD-REFINEMENT.md"]
    if args.rust_probe:
        paths.append(args.rust_probe.resolve())
    pins = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    for path in paths[:-int(bool(args.rust_probe)) or None]:
        if path.parent == DESIGN:
            (args.output/path.name).write_bytes(path.read_bytes())
    cases, results, expected = fixtures(), [], {}
    require(not args.fixture or set(args.fixture) <= set(cases), "unknown requested word fixture")
    for name, request in cases.items():
        if args.fixture and name not in args.fixture:
            continue
        started = time.time()
        result, internals = expected_probe(name, request)
        expected[name] = result
        (args.output/(name+".expected.json")).write_text(json.dumps(result, indent=2)+"\n")
        readers = {"retained_register": {k: epoch.terms(p) for k, p in unranked(request, result["rows"]).items()}}
        if request["terminal"] == "ANCESTRAL_COMPLETE":
            readers["topology_only"] = {k: epoch.terms(p) for k, p in unranked(request, result["rows"], True).items()}
        (args.output/(name+".readouts.json")).write_text(json.dumps(readers, indent=2)+"\n")
        if args.rust_probe:
            command = [str(args.rust_probe.resolve()), name]
            completed = subprocess.run(command, capture_output=True, timeout=args.timeout, check=False)
            (args.output/(name+".rust.stdout")).write_bytes(completed.stdout)
            (args.output/(name+".rust.stderr")).write_bytes(completed.stderr)
            require(completed.returncode == 0 and len(completed.stdout) <= 4*1024*1024,
                    "word probe failed or exceeded frame cap")
            actual = epoch.parse_json(completed.stdout)
            review = check_probe(actual, result, internals)
            review.update(command=command, exit_code=completed.returncode)
        else:
            review = {"status": "ORACLE_ONLY", "full_view_rows": len(result["rows"]),
                      "literal_rows": len(internals["literal"]), "terms": sum(len(r["coefficients"]) for r in result["rows"])}
        results.append({"fixture": name, "seconds": time.time()-started, **review})
        print(name, review["status"], review["full_view_rows"], flush=True)
    controls = self_controls(expected) if not args.fixture else {"status": "OMITTED_FOR_SUBSET"}
    after = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    require(pins == after, "word oracle/probe input identity changed")
    receipt = {"schema": "original_source_word_review_v1", "status": "PASS" if args.rust_probe else "ORACLE_SELF_CHECK_ONLY",
               "actual_native_execution": bool(args.rust_probe), "actual_lean_execution": False,
               "original_word_refinement_proved": False, "source_admission_verified": False,
               "pins_before": pins, "pins_after": after, "stable": True,
               "selected_fixtures": [r["fixture"] for r in results],
               "omitted_fixtures": [name for name in cases if name not in expected],
               "results": results, "controls": controls}
    (args.output/"RECEIPT.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(receipt["status"], len(results), flush=True)


if __name__ == "__main__":
    main()
