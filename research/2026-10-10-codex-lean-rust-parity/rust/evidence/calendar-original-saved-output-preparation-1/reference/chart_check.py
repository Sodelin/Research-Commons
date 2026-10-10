#!/usr/bin/env python3
"""Independent literal CHART compiler and original-row certificate checker.

No native solver or Fourier--Motzkin elimination is called. Graph checks are
finite execution predicates; their theorem refinement and active-exposure
admission are separate. A checked matrix result retains the source-admission
gate. AFFINE's pinned certificate_check.py is preserved byte-for-byte.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import argparse
import json
from pathlib import Path
import sys

from certificate_check import (MAX_REQUEST_BYTES, MAX_CERTIFICATE_BYTES, Row,
    require, nparse, qparse, qtext, dot, check_witness, check_exclusion, list_payload, read_bounded)


@dataclass(frozen=True)
class Chart:
    vertices: int
    root: int
    edges: tuple[tuple[int, int], ...]
    leaves: tuple[int, ...]
    hybrids: tuple[tuple[int, int, int], ...]
    chronology: tuple[tuple[str, tuple, tuple], ...]
    exposures: tuple[tuple[int | None, tuple, tuple, tuple | None, tuple | None], ...]
    coins: tuple[tuple[tuple | None, tuple | None], ...]
    cap: int

    @property
    def dimension(self):
        return self.vertices + len(self.edges) + 1 + len(self.hybrids)

    @property
    def bank_keys(self):
        return (tuple(f"AGE:{i}" for i in range(self.vertices))
                + tuple(f"RATE:{i}" for i in range(len(self.edges))) + ("RATE:A",)
                + tuple(f"COIN:{i}" for i in range(len(self.hybrids))))


def reference(token, tag, count):
    require(token.startswith(tag + ":"), "wrong reference tag")
    value = nparse(token[len(tag) + 1:])
    require(value < count, "reference outside original registry")
    return value


def atom(token, vertices):
    if token.startswith("V:"):
        return "V", reference(token, "V", vertices)
    require(token.startswith("Q:"), "wrong age atom tag")
    return "Q", qparse(token[2:], bounded=True)


def endpoint(token):
    if token == "NONE":
        return None
    parts = token.split(":")
    require(len(parts) == 2 and parts[0] in ("LE", "LT"), "wrong interval endpoint grammar")
    return parts[0] == "LT", qparse(parts[1], bounded=True)


def reachability(vertices, edges, blocked=None, reflexive=False):
    reachable = [[False] * vertices for _ in range(vertices)]
    if reflexive:
        for vertex in range(vertices):
            if vertex != blocked:
                reachable[vertex][vertex] = True
    for source, target in edges:
        if source != blocked and target != blocked:
            reachable[source][target] = True
    for middle in range(vertices):
        for source in range(vertices):
            if reachable[source][middle]:
                for target in range(vertices):
                    reachable[source][target] |= reachable[middle][target]
    return reachable


def structural_checks(chart):
    v, edges, root = chart.vertices, chart.edges, chart.root
    indegree = [0] * v
    outdegree = [0] * v
    for source, target in edges:
        indegree[target] += 1
        outdegree[source] += 1
    require((indegree[root], outdegree[root]) == (0, 2), "root degrees violate RootedBinary predicate")
    require(len(set(chart.leaves)) == len(chart.leaves), "leaf registry is not injective")
    require(all((indegree[a], outdegree[a]) == (1, 0) for a in chart.leaves), "leaf degrees invalid")
    leaves = set(chart.leaves)
    for a in range(v):
        if a != root and a not in leaves:
            require((indegree[a], outdegree[a]) in ((1, 2), (2, 1)), "internal degrees invalid")
    expected_hybrids = {a for a in range(v) if (indegree[a], outdegree[a]) == (2, 1)}
    require(len(set(h[0] for h in chart.hybrids)) == len(chart.hybrids)
            and set(h[0] for h in chart.hybrids) == expected_hybrids, "hybrid registry not bijective")
    for vertex, incoming0, incoming1 in chart.hybrids:
        require(incoming0 != incoming1 and edges[incoming0][1] == vertex and edges[incoming1][1] == vertex,
                "hybrid parent occurrences invalid")
    reach = reachability(v, edges)
    require(all(not reach[a][a] for a in range(v)), "directed cycle")
    require(all(a == root or reach[root][a] for a in range(v)), "vertex not root reachable")
    for blocked in range(v):
        if blocked != root:
            avoid = reachability(v, edges, blocked, reflexive=True)
            require(any(avoid[root][leaf] for leaf in chart.leaves), "root is not least stable ancestor")


def parse_chart(raw):
    require(len(raw) <= MAX_REQUEST_BYTES, "chart input exceeds byte cap")
    text = raw.decode("ascii")
    require(text.endswith("\n"), "chart missing final newline")
    lines = text[:-1].split("\n")
    require(all(line and all(line.split(" "))
                and all(c == " " or 33 <= ord(c) <= 126 for c in line)
                for line in lines), "noncanonical chart whitespace/control character")
    header = lines[0].split(" ")
    require(len(header) == 9 and header[:2] == ["RC1", "CHART"], "wrong chart header")
    v, e, l, h, c, x, cap = map(nparse, header[2:])
    require(3 <= v <= 32 and 2 <= e <= 32 and 2 <= l <= v and h <= v and c <= 32 and x <= 32
            and cap <= 4096 and v + e + 1 + h <= 32, "chart count/dimension/cap outside contract")
    require(len(lines) == 2 + e + l + 2 * h + c + x, "wrong chart record count")
    iterator = iter(lines[1:])
    root_line = next(iterator).split(" ")
    require(len(root_line) == 2 and root_line[0] == "ROOT", "missing chart root")
    root = nparse(root_line[1])
    require(root < v, "root outside original vertex registry")
    edges = []
    for i in range(e):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 4 and tokens[:2] == ["EDGE", str(i)], "wrong original edge record/id")
        source, target = map(nparse, tokens[2:])
        require(source < v and target < v, "edge endpoint outside vertex registry")
        edges.append((source, target))
    leaves = []
    for i in range(l):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 3 and tokens[:2] == ["LEAF", str(i)], "wrong original leaf record/id")
        vertex = nparse(tokens[2])
        require(vertex < v, "leaf outside vertex registry")
        leaves.append(vertex)
    hybrids = []
    for i in range(h):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 5 and tokens[:2] == ["HYBRID", str(i)], "wrong original hybrid record/id")
        vertex, incoming0, incoming1 = map(nparse, tokens[2:])
        require(vertex < v and incoming0 < e and incoming1 < e, "hybrid reference outside original registry")
        hybrids.append((vertex, incoming0, incoming1))
    chronology = []
    for _ in range(c):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 4 and tokens[0] == "AGE" and tokens[1] in ("LT", "LE", "EQ"),
                "wrong chronology comparison")
        chronology.append((tokens[1], atom(tokens[2], v), atom(tokens[3], v)))
    exposures = []
    for i in range(x):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 7 and tokens[:2] == ["EXPOSURE", str(i)], "wrong original exposure record/id")
        population = None if tokens[2] == "A" else reference(tokens[2], "E", e)
        exposures.append((population, atom(tokens[3], v), atom(tokens[4], v),
                          endpoint(tokens[5]), endpoint(tokens[6])))
    coins = []
    for i in range(h):
        tokens = next(iterator).split(" ")
        require(len(tokens) == 4 and tokens[:2] == ["COIN", str(i)], "wrong coin interval record/id")
        coins.append((endpoint(tokens[2]), endpoint(tokens[3])))
    chart = Chart(v, root, tuple(edges), tuple(leaves), tuple(hybrids), tuple(chronology),
                  tuple(exposures), tuple(coins), cap)
    structural_checks(chart)
    require(len(compile_chart(chart)) <= 128, "actual emitted matrix exceeds row cap")
    return chart


def compile_chart(chart):
    n, v, e = chart.dimension, chart.vertices, len(chart.edges)
    zero = (Fraction(0),) * n

    def variable(i):
        return tuple(Fraction(j == i) for j in range(n)), Fraction(0)

    def constant(value):
        return zero, Fraction(value)

    def form(a):
        return variable(a[1]) if a[0] == "V" else constant(a[1])

    def subtract(left, right):
        return tuple(a - b for a, b in zip(left[0], right[0])), left[1] - right[1]

    def scale(scalar, affine):
        return tuple(scalar * a for a in affine[0]), scalar * affine[1]

    def compare(left, right, strict):
        return Row(strict, right[1] - left[1], tuple(a - b for a, b in zip(left[0], right[0])))

    def inverse(population):
        return variable(v + e if population is None else v + population)

    def coin(i):
        return variable(v + e + 1 + i)

    out = []
    for source, target in chart.edges:
        out.append(compare(variable(target), variable(source), True))
    for leaf in chart.leaves:
        out.extend((compare(variable(leaf), constant(0), False), compare(constant(0), variable(leaf), False)))
    for population in (*range(e), None):
        out.append(compare(constant(0), inverse(population), True))
    out.extend(compare(constant(0), coin(i), True) for i in range(len(chart.hybrids)))
    out.extend(compare(coin(i), constant(1), True) for i in range(len(chart.hybrids)))
    for relation, left, right in chart.chronology:
        out.append(compare(form(left), form(right), relation == "LT"))
        if relation == "EQ":
            out.append(compare(form(right), form(left), False))
    for population, younger, older, lower, upper in chart.exposures:
        duration = subtract(form(older), form(younger))
        if lower is not None:
            strict, value = lower
            out.append(compare(scale(value, inverse(population)), duration, strict))
        if upper is not None:
            strict, value = upper
            out.append(compare(duration, scale(value, inverse(population)), strict))
    for i, (lower, upper) in enumerate(chart.coins):
        if lower is not None:
            strict, value = lower
            out.append(compare(constant(value), coin(i), strict))
        if upper is not None:
            strict, value = upper
            out.append(compare(coin(i), constant(value), strict))
    return tuple(out)


def row_wire(row):
    return " ".join(("LT" if row.strict else "LE", qtext(row.bound), *map(qtext, row.coeff)))


def verify_chart_certificate(raw_request, raw_result, exit_code=None):
    require(len(raw_result) <= MAX_CERTIFICATE_BYTES, "chart result exceeds certificate byte cap")
    try:
        chart = parse_chart(raw_request)
    except (ValueError, UnicodeError, OverflowError):
        require((exit_code is None or exit_code == 1) and raw_result == b"RC1 ERROR INVALID_REQUEST\n",
                "invalid chart did not produce canonical refusal")
        return {"status": "REFUSED", "result_valid": True, "certificate_valid": False,
                "source_admission_established": False}
    rows = compile_chart(chart)
    prefix = b"RC1 RESULT CHART\nBEGIN_REQUEST\n" + raw_request + b"END_REQUEST\n"
    require(raw_result.startswith(prefix), "chart result changed/omitted complete original request")
    rest = raw_result[len(prefix):].decode("ascii")
    bank = "BANK " + str(chart.dimension) + " " + " ".join(chart.bank_keys)
    matrix = "MATRIX " + str(chart.dimension) + " " + str(len(rows)) + " " + str(chart.cap)
    compiled = bank + "\n" + matrix + "\n" + "\n".join(map(row_wire, rows)) + "\n"
    compiled += "END_MATRIX\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n"
    require(rest.startswith(compiled), "emitted original chart bank/matrix/gate differs from exact compiler")
    payload = rest[len(compiled):]
    require(payload.endswith("\n"), "chart result missing final LF")
    lines = payload[:-1].split("\n")
    require(lines[-1:] == ["END"], "chart result missing exact END")
    common = {"operation": "CHART", "result_valid": True, "certificate_valid": False,
              "source_admission_established": False, "scope": "LITERAL_SHARED_BANK_CHART_MATRIX_ONLY",
              "compiler_rows_checked": True, "graph_structure_checked": True,
              "graph_validator_refinement_proved": False, "active_exposure_admission_established": False}
    if lines[0] == "STATUS SAT":
        require(len(lines) == 4 and (exit_code is None or exit_code == 0), "wrong CHART SAT structure/status")
        witness = list_payload(lines[1], "WITNESS", chart.dimension)
        lhs = list_payload(lines[2], "EVAL", len(rows))
        check_witness(rows, witness, lhs)
        return common | {"status": "SAT", "certificate_valid": True,
                         "bank_keys": chart.bank_keys, "witness": tuple(map(qtext, witness))}
    if lines[0] == "STATUS UNSAT":
        require(len(lines) == 5 and (exit_code is None or exit_code == 0), "wrong CHART UNSAT structure/status")
        weights = list_payload(lines[1], "MULTIPLIERS", len(rows))
        fields = lines[2].split(" ")
        require(len(fields) == 2 and fields[0] == "BOUND", "wrong chart contradiction bound frame")
        require(lines[3] in ("STRICT 0", "STRICT 1"), "wrong chart contradiction strictness frame")
        aggregate = qparse(fields[1])
        strict = lines[3] == "STRICT 1"
        check_exclusion(chart.dimension, rows, weights, aggregate, strict)
        return common | {"status": "UNSAT", "certificate_valid": True,
                         "multipliers": tuple(map(qtext, weights)), "bound": qtext(aggregate), "strict": strict}
    if lines[0] == "STATUS UNKNOWN":
        require(len(lines) == 3 and (exit_code is None or exit_code == 2), "wrong CHART UNKNOWN structure/status")
        fields = lines[1].split(" ")
        require(len(fields) == 4 and fields[0] == "LIMIT", "wrong CHART limit frame")
        dimension, required, cap = map(nparse, fields[1:])
        require(0 < dimension <= chart.dimension and required > cap and cap == chart.cap,
                "inconsistent CHART projection limit metadata")
        return common | {"status": "UNKNOWN", "dimension": dimension, "required_rows": required, "cap": cap}
    raise ValueError("unexpected CHART status")


def parse_request(raw):
    """Common adapter API; the chart retains all original record identities."""
    return "CHART", parse_chart(raw)


def verify_certificate(raw_request, raw_result, exit_code=None):
    return verify_chart_certificate(raw_request, raw_result, exit_code)


def check_response(raw_request, raw_result, exit_code):
    return verify_chart_certificate(raw_request, raw_result, exit_code)["status"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--exit-code", type=int)
    args = parser.parse_args()
    checked = verify_chart_certificate(read_bounded(args.request, MAX_REQUEST_BYTES),
                                       read_bounded(args.certificate, MAX_CERTIFICATE_BYTES), args.exit_code)
    print(json.dumps(checked, sort_keys=True))
    return 0 if checked["certificate_valid"] else 1 if checked["status"] == "REFUSED" else 2


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, UnicodeError) as error:
        print(json.dumps({"result_valid": False, "certificate_valid": False, "error": str(error)}, sort_keys=True))
        sys.exit(1)
