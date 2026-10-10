#!/usr/bin/env python3
"""Independent RC1 LAW framing, polynomial, reader and Python baseline checks.

The attributed inherited compiler supplies the complete coefficient baseline.
Formal normalization and the rooted-to-unrooted reader are checked separately.
This finite check is not a source-admission or a native refinement proof.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
import argparse
import hashlib
import json
from pathlib import Path
import sys
from types import ModuleType

from certificate_check import MAX_REQUEST_BYTES, MAX_CERTIFICATE_BYTES, require, nparse, qparse, read_bounded
from chart_check import Chart, structural_checks

BASELINE = Path(__file__).resolve().parents[2] / "2026-10-01-g7-continuous-design/law_compiler.py"
BASELINE_SHA = "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"


@dataclass(frozen=True)
class Law:
    chart: Chart
    mechanism: str
    samples: tuple[int, ...]
    state_cap: int
    term_cap: int
    history_cap: int

    @property
    def variables(self):
        return tuple(f"X:{i}" for i in range(len(self.chart.edges))) + tuple(f"G:{i}" for i in range(len(self.chart.hybrids)))


def parse_law(raw):
    require(len(raw) <= MAX_REQUEST_BYTES, "LAW request exceeds byte cap")
    source = raw.decode("ascii")
    require(source.endswith("\n"), "LAW missing final LF")
    lines = source[:-1].split("\n")
    require(all(line and all(line.split(" ")) and all(c == " " or 33 <= ord(c) <= 126 for c in line)
                for line in lines), "LAW noncanonical whitespace/control byte")
    header = lines[0].split(" ")
    require(len(header) == 10 and header[:2] == ["RC1", "LAW"], "wrong LAW header")
    v, e, l, h, s, state_cap, term_cap, history_cap = map(nparse, header[2:])
    require(3 <= v <= 32 and 2 <= e <= 32 and 2 <= l <= v and h <= v and v+e+1+h <= 32
            and 1 <= s <= 4 and state_cap <= 4096 and term_cap <= 65536 and history_cap <= 4096,
            "LAW counts/budgets outside contract")
    require(len(lines) == 3+e+l+h+s, "wrong LAW record count")
    iterator = iter(lines[1:])
    mode = next(iterator).split(" ")
    require(len(mode) == 2 and mode[0] == "MECHANISM" and mode[1] in ("COMMON", "INDEPENDENT"), "wrong LAW mechanism")
    root_line = next(iterator).split(" ")
    require(len(root_line) == 2 and root_line[0] == "ROOT", "wrong LAW root")
    root = nparse(root_line[1])
    require(root < v, "LAW root outside registry")
    edges, leaves, hybrids, samples = [], [], [], []
    for i in range(e):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 4 and tokens[:2] == ["EDGE", str(i)], "wrong original LAW edge ID")
        a, b = map(nparse, tokens[2:])
        require(a < v and b < v, "LAW edge outside vertex registry")
        edges.append((a, b))
    for i in range(l):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 3 and tokens[:2] == ["LEAF", str(i)], "wrong original LAW leaf ID")
        a = nparse(tokens[2])
        require(a < v, "LAW leaf outside vertex registry")
        leaves.append(a)
    for i in range(h):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 5 and tokens[:2] == ["HYBRID", str(i)], "wrong original LAW hybrid ID")
        a, incoming0, incoming1 = map(nparse, tokens[2:])
        require(a < v and incoming0 < e and incoming1 < e, "LAW hybrid occurrence outside registry")
        hybrids.append((a, incoming0, incoming1))
    for i in range(s):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 3 and tokens[:2] == ["SAMPLE", str(i)], "wrong original copied-label ID")
        taxon = nparse(tokens[2])
        require(taxon < l, "LAW sampled taxon outside registry")
        samples.append(taxon)
    chart = Chart(v, root, tuple(edges), tuple(leaves), tuple(hybrids), (), (), tuple((None, None) for _ in hybrids), 4096)
    structural_checks(chart)
    return Law(chart, mode[1], tuple(samples), state_cap, term_cap, history_cap)


def tree_leaves(tree):
    return (tree,) if isinstance(tree, int) else tree_leaves(tree[0]) + tree_leaves(tree[1])


def canonical_tree(tree):
    if isinstance(tree, str):
        return int(tree)
    if isinstance(tree, int):
        return tree
    left, right = map(canonical_tree, tree)
    return (left, right) if min(tree_leaves(left)) < min(tree_leaves(right)) else (right, left)


def tree_wire(tree):
    return str(tree) if isinstance(tree, int) else "(" + tree_wire(tree[0]) + "," + tree_wire(tree[1]) + ")"


def parse_tree(token, labels):
    require(0 < len(token) <= 4*labels+16, "LAW tree exceeds finite copied-label grammar")

    def read(i):
        if i < len(token) and token[i] == "(":
            a, i = read(i+1)
            require(i < len(token) and token[i] == ",", "LAW tree missing binary separator")
            b, i = read(i+1)
            require(i < len(token) and token[i] == ")", "LAW tree missing close")
            require(min(tree_leaves(a)) < min(tree_leaves(b)), "LAW tree children not canonical")
            return (a, b), i+1
        stop = i
        while stop < len(token) and token[stop].isdigit():
            stop += 1
        value = nparse(token[i:stop])
        require(value < labels, "LAW tree copied label outside registry")
        return value, stop

    tree, end = read(0)
    require(end == len(token) and sorted(tree_leaves(tree)) == list(range(labels)), "LAW tree omitted/repeated copied labels")
    require(tree_wire(tree) == token, "LAW tree serialization not canonical")
    return tree


def split_wire(tree):
    whole = set(tree_leaves(tree))
    cuts = set()

    def visit(node):
        if isinstance(node, int):
            return
        side = set(tree_leaves(node))
        other = whole-side
        if len(side) >= 2 and len(other) >= 2:
            cuts.add(tuple(sorted((tuple(sorted(side)), tuple(sorted(other))))))
        visit(node[0]); visit(node[1])

    visit(tree)
    vector = lambda xs: "[" + ",".join(map(str, xs)) + "]"
    return "[" + ";".join(vector(a) + "|" + vector(b) for a, b in sorted(cuts)) + "]"


def add_poly(left, right):
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Fraction(0)) + coefficient
        if result[monomial] == 0:
            del result[monomial]
    return result


def pushforward(rooted, labels):
    output = {}
    for name, polynomial in rooted.items():
        signature = split_wire(parse_tree(name, labels))
        output[signature] = add_poly(output.get(signature, {}), polynomial)
    return {name: polynomial for name, polynomial in output.items() if polynomial}


def baseline_module():
    name = "independent_pinned_inherited_law_compiler"
    if name not in sys.modules:
        raw = BASELINE.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == BASELINE_SHA, "attributed inherited LAW baseline bytes changed")
        module = ModuleType(name)
        module.__file__ = str(BASELINE)
        sys.modules[name] = module
        exec(compile(raw, str(BASELINE), "exec"), module.__dict__)
    return sys.modules[name]


@lru_cache(maxsize=128)
def reference_tables(law):
    import sympy as sp
    baseline = baseline_module()
    chart = law.chart
    network = baseline.Network(tuple((f"v{a}", f"v{b}") for a, b in chart.edges), f"v{chart.root}",
                               tuple(f"v{v}" for v in chart.leaves))
    variables = tuple(sp.Symbol(f"X{i}") for i in range(len(chart.edges))) + tuple(sp.Symbol(f"G{i}") for i in range(len(chart.hybrids)))
    samples = {}
    for copied, taxon in enumerate(law.samples):
        vertex = f"v{chart.leaves[taxon]}"
        samples[vertex] = (*samples.get(vertex, ()), str(copied))
    inherited_incoming = network.structure()[0]
    gamma = {}
    for hid, (vertex, first, _) in enumerate(chart.hybrids):
        g = variables[len(chart.edges)+hid]
        gamma[f"v{vertex}"] = g if first == inherited_incoming[f"v{vertex}"][0] else 1-g
    original = baseline.compile_law(network, law.mechanism.lower(), samples=samples,
                                    edge_values={i: x for i, x in enumerate(variables[:len(chart.edges)])},
                                    inheritance_values=gamma)
    rooted = {}
    for tree, expression in original.items():
        polynomial = {tuple(exponents): Fraction(int(coefficient.p), int(coefficient.q))
                      for exponents, coefficient in sp.Poly(sp.expand(expression), *variables).terms() if coefficient != 0}
        name = tree_wire(canonical_tree(tree))
        rooted[name] = add_poly(rooted.get(name, {}), polynomial)
    return rooted, pushforward(rooted, len(law.samples))


def verify_law_certificate(raw_request, raw_result, exit_code=None, compare_baseline=True):
    require(len(raw_result) <= MAX_CERTIFICATE_BYTES, "LAW result exceeds byte cap")
    try:
        law = parse_law(raw_request)
    except (ValueError, UnicodeError, OverflowError):
        require(raw_result == b"RC1 ERROR INVALID_REQUEST\n" and exit_code in (None, 1), "invalid LAW missing canonical refusal")
        return {"status": "REFUSED", "result_valid": True, "certificate_valid": False, "source_admission_established": False}
    prefix = b"RC1 RESULT LAW\nBEGIN_REQUEST\n" + raw_request + b"END_REQUEST\n"
    prefix += ("VARIABLES " + str(len(law.variables)) + " " + " ".join(law.variables) + "\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n").encode()
    require(raw_result.startswith(prefix), "LAW request/variable/admission frame changed")
    text = raw_result[len(prefix):].decode("ascii")
    require(text.endswith("\n"), "LAW output missing LF")
    lines = text[:-1].split("\n")
    common = {"operation": "LAW", "result_valid": True, "certificate_valid": False,
              "source_admission_established": False, "scope": "FORMAL_SUPPLIED_SOURCE_TERMINAL_GENEALOGY_TABLE_ONLY",
              "physical_survival_image_established": False, "general_native_refinement_proved": False}
    if lines[0] == "STATUS UNKNOWN":
        require(len(lines) == 3 and lines[-1] == "END" and exit_code in (None, 2), "wrong LAW UNKNOWN status/exit/frame")
        fields = lines[1].split(" ")
        require(len(fields) == 5 and fields[0] == "LIMIT", "wrong LAW limit framing")
        kind = fields[1]
        vertex, required, cap = map(nparse, fields[2:])
        limits = {"STATE": law.state_cap, "TERM": law.term_cap, "HISTORY": law.history_cap, "OUTPUT": MAX_CERTIFICATE_BYTES}
        require(kind in limits and cap == limits[kind] and required > cap and vertex < law.chart.vertices,
                "inconsistent LAW budget metadata")
        require(kind != "OUTPUT" or vertex == law.chart.root, "LAW output limit must name root")
        return common | {"status": "UNKNOWN", "limit_kind": kind, "vertex": vertex, "required": required, "cap": cap}
    require(lines[0] == "STATUS TABLE" and exit_code in (None, 0), "wrong LAW table status/exit")
    index = 1

    def table(kind, record):
        nonlocal index
        header = lines[index].split(" "); index += 1
        require(len(header) == 2 and header[0] == kind, "wrong LAW table header")
        count = nparse(header[1])
        require(0 < count <= 15, "LAW full table row count exceeds copied-label tree bound")
        output, previous = {}, None
        for _ in range(count):
            fields = lines[index].split(" "); index += 1
            require(len(fields) == 3 and fields[0] == record, "wrong LAW observable row")
            key, terms = fields[1], nparse(fields[2])
            require(previous is None or previous < key, "LAW observable order/duplicate key")
            previous = key
            if kind == "ROOTED":
                parse_tree(key, len(law.samples))
            require(0 < terms <= law.term_cap, "LAW zero polynomial or term count exceeds admitted cap")
            polynomial, prior = {}, None
            for _ in range(terms):
                fields = lines[index].split(" "); index += 1
                require(len(fields) == 2+len(law.variables) and fields[0] == "TERM", "wrong LAW polynomial term arity")
                coefficient = qparse(fields[1])
                exponents = tuple(map(nparse, fields[2:]))
                require(coefficient != 0 and (prior is None or prior < exponents), "LAW zero/duplicate/unordered term")
                require(all(e <= len(law.samples)*(len(law.samples)-1)//2 for e in exponents[:len(law.chart.edges)])
                        and all(e <= len(law.samples) for e in exponents[len(law.chart.edges):]), "LAW exponent outside original edge/hybrid degree bounds")
                polynomial[exponents] = coefficient
                prior = exponents
            output[key] = polynomial
        return output

    try:
        rooted = table("ROOTED", "TREE")
        unrooted = table("UNROOTED", "SPLIT")
    except IndexError as error:
        raise ValueError("LAW truncated polynomial table") from error
    require(lines[index:] == ["END"], "LAW trailing/missing table frame")
    constant = {(0,)*len(law.variables): Fraction(1)}
    for output in (rooted, unrooted):
        total = {}
        for polynomial in output.values():
            total = add_poly(total, polynomial)
        require(total == constant, "LAW formal table does not sum identically to one")
    require(unrooted == pushforward(rooted, len(law.samples)), "LAW unrooted table is not full rooted pushforward")
    if compare_baseline:
        expected_rooted, expected_unrooted = reference_tables(law)
        require(rooted == expected_rooted and unrooted == expected_unrooted, "LAW full polynomial coefficients differ from pinned inherited source compiler")
    return common | {"status": "TABLE", "rooted_rows": len(rooted), "unrooted_rows": len(unrooted),
                     "polynomial_normalization_checked": True, "unrooted_pushforward_checked": True,
                     "inherited_baseline_all_coefficients_checked": compare_baseline, "baseline_sha256": BASELINE_SHA,
                     "terms_checked": sum(map(len, rooted.values()))+sum(map(len, unrooted.values()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--exit-code", type=int)
    args = parser.parse_args()
    result = verify_law_certificate(read_bounded(args.request, MAX_REQUEST_BYTES),
                                    read_bounded(args.certificate, MAX_CERTIFICATE_BYTES), args.exit_code)
    print(json.dumps(result, sort_keys=True))
    return 0 if result["status"] == "TABLE" else 2 if result["status"] == "UNKNOWN" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, UnicodeError, OSError) as error:
        print(json.dumps({"result_valid": False, "certificate_valid": False, "error": str(error)}, sort_keys=True))
        sys.exit(1)
