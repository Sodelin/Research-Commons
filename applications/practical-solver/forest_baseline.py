"""Lazy exact ordinary-population forest access and coordinate probabilities.

Derivative of dot's reviewed sparse-forest baseline at 00ecd0b5. This module
evaluates one specified labelled forest, without enumerating the forest law.
Labels are exactly 1,...,m; children and roots are ordered by least leaf label.
An internal node is a two-tuple; a forest is a tuple of roots. All arithmetic
is exact. This is an ordinary-population component, not a source recognizer.

HermitianDilation exposes a *different* evolution H=[[0,Q],[Q.T,0]]/C(m,2).
Its Python access functions are classical specifications, not compiled quantum
oracles or a simulator of exp(-itH), and exp(-itH) is not exp(tQ).
"""
from __future__ import annotations

from bisect import bisect_left
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb, factorial
from typing import Iterable, Iterator, Union

Tree = Union[int, tuple["Tree", "Tree"]]
Forest = tuple[Tree, ...]


def _integer(value: int, name: str, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}.")
    return value


def _survival(x: Fraction | int, allow_boundary: bool) -> Fraction:
    if type(x) not in (int, Fraction):
        raise TypeError("Survival must be an exact Fraction or integer, not a float.")
    if type(allow_boundary) is not bool:
        raise TypeError("allow_boundary must be boolean.")
    x = Fraction(x)
    if not (0 <= x <= 1 if allow_boundary else 0 < x < 1):
        interval = "[0,1]" if allow_boundary else "(0,1)"
        raise ValueError(f"Survival must be in {interval}.")
    return x


def _least(t: Tree) -> int:
    # Canonical children put the least leaf on the left. No recursive walk.
    while isinstance(t, tuple):
        t = t[0]
    return t


def _same_forest(a: Forest, b: Forest) -> bool:
    """Structural equality without Python's recursive nested-tuple comparison."""
    if len(a) != len(b):
        return False
    stack = list(zip(a, b))
    while stack:
        left, right = stack.pop()
        if left is right:
            continue
        if type(left) is not type(right):
            return False
        if type(left) is int:
            if left != right:
                return False
        else:
            stack.extend(zip(left, right))
    return True


def canonical_forest(roots: Iterable[Tree]) -> Forest:
    """Order binary trees and forest roots; reject malformed/repeated labels.

    This convenience constructor permits positive labels other than 1,...,m.
    ForestGraph.validate additionally checks the declared complete label set.
    """
    out: list[Tree] = []
    labels: set[int] = set()
    for root in roots:
        stack = [(root, False)]
        values: list[Tree] = []
        while stack:
            t, visited = stack.pop()
            if type(t) is int:
                if t < 1 or t in labels:
                    raise ValueError("Leaf labels must be distinct positive integers.")
                labels.add(t)
                values.append(t)
            elif type(t) is tuple and len(t) == 2:
                if visited:
                    b, a = values.pop(), values.pop()
                    values.append((a, b) if _least(a) < _least(b) else (b, a))
                else:
                    stack.extend(((t, True), (t[1], False), (t[0], False)))
            else:
                raise ValueError("A tree must be an integer leaf or a binary tuple.")
        out.append(values[0])
    if not out:
        raise ValueError("The ordinary graph requires at least one entering label.")
    return tuple(sorted(out, key=_least))


@dataclass(frozen=True)
class HistoryStatistics:
    leaves: int
    roots: int
    mergers: int
    hook_product: int
    histories: int


class ForestGraph:
    """Succinct ordinary generator Q in the row-vector convention.

    forward_neighbors and reverse_neighbors yield one forest at a time.
    No full-state dictionary, forest catalogue or probability table is stored.
    """

    def __init__(self, m: int):
        self.m = _integer(m, "m", 1)
        self.token_bits = (m + 3).bit_length()  # ceil(log2(m+4))
        self.token_slots = 3 * m
        self.code_bits = self.token_slots * self.token_bits
        self.code_count = 1 << self.code_bits

    @property
    def singleton_forest(self) -> Forest:
        return tuple(range(1, self.m + 1))

    def validate(self, f: Forest) -> None:
        """Check shape, all labels exactly once and canonical ordering in O(m)."""
        if type(f) is not tuple or not 1 <= len(f) <= self.m:
            raise ValueError("A forest must be a nonempty tuple with <= m roots.")
        labels: set[int] = set()
        minima: list[int] = []
        for root in f:
            stack = [(root, False)]
            values: list[int] = []
            while stack:
                t, visited = stack.pop()
                if type(t) is int:
                    if not 1 <= t <= self.m or t in labels:
                        raise ValueError("Labels must occur exactly once in 1,...,m.")
                    labels.add(t)
                    values.append(t)
                elif type(t) is tuple and len(t) == 2:
                    if visited:
                        b, a = values.pop(), values.pop()
                        if a >= b:
                            raise ValueError("Children must be ordered by least leaf label.")
                        values.append(a)
                    else:
                        stack.extend(((t, True), (t[1], False), (t[0], False)))
                else:
                    raise ValueError("Trees must be integer leaves or binary tuples.")
            minima.append(values[0])
        if len(labels) != self.m:
            raise ValueError("The forest must contain every label in 1,...,m.")
        if any(a >= b for a, b in zip(minima, minima[1:])):
            raise ValueError("Roots must be ordered by least leaf label.")

    def encode(self, f: Forest) -> int:
        """Fixed 3m-token canonical code, compatible with the reviewed checker."""
        self.validate(f)
        tokens: list[int] = []
        for i, root in enumerate(f):
            if i:
                tokens.append(self.m + 3)
            stack: list[Tree | None] = [root]
            while stack:
                t = stack.pop()
                if t is None:
                    tokens.append(self.m + 2)
                elif type(t) is int:
                    tokens.append(t)
                else:
                    tokens.append(self.m + 1)
                    stack.extend((None, t[1], t[0]))
        code = 0
        for token in tokens:
            code = (code << self.token_bits) | token
        return code << (self.token_bits * (self.token_slots - len(tokens)))

    def decode(self, code: int) -> Forest:
        """Reject unused bit strings, padding gaps, noncanonical or duplicate labels."""
        _integer(code, "code")
        if code >= self.code_count:
            raise ValueError("Forest code exceeds its fixed register width.")
        mask = (1 << self.token_bits) - 1
        tokens = [
            (code >> (self.token_bits * i)) & mask
            for i in range(self.token_slots - 1, -1, -1)
        ]
        end = next((i for i, token in enumerate(tokens) if token == 0), len(tokens))
        if end == 0 or any(tokens[end:]):
            raise ValueError("Invalid empty code or nonzero token after padding.")
        roots: list[Tree] = []
        frames: list[list[Tree]] = [[]]
        need_root = True
        for token in tokens[:end]:
            if 1 <= token <= self.m:
                frames[-1].append(token)
                need_root = False
            elif token == self.m + 1:
                frames.append([])
                need_root = False
            elif token == self.m + 2:
                if len(frames) == 1 or len(frames[-1]) != 2:
                    raise ValueError("Unmatched delimiter or nonbinary node.")
                children = frames.pop()
                frames[-1].append((children[0], children[1]))
            elif token == self.m + 3:
                if len(frames) != 1 or len(frames[0]) != 1 or need_root:
                    raise ValueError("Invalid root separator.")
                roots.append(frames[0].pop())
                need_root = True
            else:
                raise ValueError("Invalid token.")
            if len(frames[-1]) > (1 if len(frames) == 1 else 2):
                raise ValueError("Missing separator or nonbinary node.")
        if len(frames) != 1 or len(frames[0]) != 1 or need_root:
            raise ValueError("Incomplete forest code.")
        f = tuple(roots + frames[0])
        self.validate(f)
        return f

    def _forward(self, f: Forest) -> Iterator[Forest]:
        for a, b in combinations(range(len(f)), 2):
            merged = (f[a], f[b])  # a < b preserves child order
            roots = [t for i, t in enumerate(f) if i not in (a, b)]
            roots.append(merged)
            yield tuple(sorted(roots, key=_least))

    def forward_neighbors(self, f: Forest) -> Iterator[Forest]:
        self.validate(f)
        yield from self._forward(f)

    def _reverse(self, f: Forest) -> Iterator[Forest]:
        for i, root in enumerate(f):
            if type(root) is tuple:
                yield tuple(sorted(f[:i] + f[i + 1:] + root, key=_least))

    def reverse_neighbors(self, f: Forest) -> Iterator[Forest]:
        self.validate(f)
        yield from self._reverse(f)

    def row_entries(self, f: Forest) -> Iterator[tuple[Forest, int]]:
        """Nonzero Q(f,g), including -C(k,2) on the diagonal if k >= 2."""
        self.validate(f)
        if len(f) >= 2:
            yield f, -comb(len(f), 2)
        for g in self._forward(f):
            yield g, 1

    def generator_entry(self, f: Forest, g: Forest) -> int:
        self.validate(f)
        self.validate(g)
        if _same_forest(f, g):
            return -comb(len(f), 2)
        return int(len(g) == len(f) - 1 and any(_same_forest(h, g) for h in self._forward(f)))

    def history_statistics(self, f: Forest) -> HistoryStatistics:
        self.validate(f)
        hooks = 1
        for root in f:
            stack = [(root, False)]
            sizes: list[int] = []
            while stack:
                t, visited = stack.pop()
                if type(t) is int:
                    sizes.append(1)
                elif visited:
                    size = sizes.pop() + sizes.pop()
                    hooks *= size - 1
                    sizes.append(size)
                else:
                    stack.extend(((t, True), (t[1], False), (t[0], False)))
        mergers = self.m - len(f)
        histories, remainder = divmod(factorial(mergers), hooks)
        if remainder:
            raise ArithmeticError("Forest hook product did not divide the history factorial.")
        return HistoryStatistics(self.m, len(f), mergers, hooks, histories)

    def probability(self, f: Forest, x: Fraction | int, *, allow_boundary: bool = False) -> Fraction:
        """Exact E_m(x;f) from singleton entering labels, x=exp(-t).

        Default x in (0,1) retains positive finite ordinary duration. Endpoints
        require allow_boundary=True and are mathematical diagnostics, not admitted
        positive source witnesses. The result is one coordinate, not a source fit.
        """
        stats = self.history_statistics(f)
        p = root_count_probability(self.m, stats.roots, x, allow_boundary=allow_boundary)
        choices = 1
        for j in range(stats.roots + 1, self.m + 1):
            choices *= comb(j, 2)
        return p * Fraction(stats.histories, choices)


def count_polynomial(m: int, r: int) -> tuple[tuple[int, Fraction], ...]:
    """At most m exact terms for P(m roots -> r); no forest enumeration."""
    _integer(m, "m", 1)
    _integer(r, "r", 1)
    if r > m:
        raise ValueError("r must be <= m.")
    lambdas = tuple(comb(j, 2) for j in range(r, m + 1))
    prefactor = 1
    for j in range(r + 1, m + 1):
        prefactor *= comb(j, 2)
    terms = []
    for exponent in lambdas:
        denominator = 1
        for other in lambdas:
            if other != exponent:
                denominator *= other - exponent
        terms.append((exponent, Fraction(prefactor, denominator)))
    return tuple(terms)


def root_count_probability(
    m: int, r: int, x: Fraction | int, *, allow_boundary: bool = False
) -> Fraction:
    x = _survival(x, allow_boundary)
    return sum((coefficient * x**exponent for exponent, coefficient in count_polynomial(m, r)), Fraction(0))


class HermitianDilation:
    """Exact classical access specification for H, extended by zero on invalid codes.

    Padding/location implement a full permutation on the entire layered index
    register, with a two-sided inverse. Only the current row's O(m^2) support is
    materialized. The Python implementation does not establish gate counts.
    """

    def __init__(self, graph: ForestGraph):
        if not isinstance(graph, ForestGraph):
            raise TypeError("graph must be a ForestGraph.")
        self.graph = graph
        self.index_bits = graph.code_bits + 1
        self.index_count = 1 << self.index_bits
        self.normalization = comb(graph.m, 2)
        self.sparsity = self.normalization + 1 if graph.m >= 2 else 1

    def _index(self, value: int) -> None:
        _integer(value, "layered index")
        if value >= self.index_count:
            raise ValueError("Layered index exceeds its register width.")

    def _decode_row(self, row: int) -> tuple[int, Forest] | None:
        self._index(row)
        layer, code = divmod(row, self.graph.code_count)
        try:
            return layer, self.graph.decode(code)
        except ValueError:
            return None

    def nonzero_entries(self, row: int) -> Iterator[tuple[int, Fraction]]:
        decoded = self._decode_row(row)
        if decoded is None or self.normalization == 0:
            return
        layer, f = decoded
        offset = (1 - layer) * self.graph.code_count
        if len(f) >= 2:
            yield offset + self.graph.encode(f), Fraction(-comb(len(f), 2), self.normalization)
        neighbors = self.graph._forward(f) if layer == 0 else self.graph._reverse(f)
        for g in neighbors:
            yield offset + self.graph.encode(g), Fraction(1, self.normalization)

    def entry(self, row: int, column: int) -> Fraction:
        self._index(column)
        return next((value for code, value in self.nonzero_entries(row) if code == column), Fraction(0))

    def padded_columns(self, row: int) -> tuple[int, ...]:
        columns = {column for column, _ in self.nonzero_entries(row)}
        candidate = 0
        while len(columns) < self.sparsity:
            columns.add(candidate)
            candidate += 1
        return tuple(sorted(columns))

    def location(self, row: int, slot: int) -> int:
        """pi_I(slot); includes complement unranking for slots >= sparsity."""
        self._index(slot)
        columns = self.padded_columns(row)
        if slot < self.sparsity:
            return columns[slot]
        column = slot - self.sparsity
        for value in columns:
            if value > column:
                break
            column += 1
        return column

    def inverse_location(self, row: int, column: int) -> int:
        self._index(column)
        columns = self.padded_columns(row)
        position = bisect_left(columns, column)
        if position < self.sparsity and columns[position] == column:
            return position
        return self.sparsity + column - position

    def rounded_entry(self, row: int, column: int, precision_bits: int) -> int:
        """Symmetric exact truncation toward zero, represented in units of 2^-p.

        Uniform per-entry error < 2^-p; signed output integer is an arithmetic
        specification, not a coherent XOR answer-register implementation.
        """
        _integer(precision_bits, "precision_bits")
        scaled = self.entry(row, column) * (1 << precision_bits)
        magnitude = abs(scaled.numerator) // scaled.denominator
        return magnitude if scaled >= 0 else -magnitude


def evaluate_request(request: dict) -> dict:
    """Bounded JSON consumer for one exact coordinate; no source-search outcome.

    CLI limits are m<=64 and <=256 bits in each survival integer. The reusable
    Python API has no fixed cap. Limits prevent accidental huge CLI requests,
    and do not constitute a finite bound on the original source problem.
    """
    if type(request) is not dict or set(request) != {"schema", "m", "forest", "survival"}:
        raise ValueError("Request fields must be exactly schema, m, forest, survival.")
    if request["schema"] != "ordinary_forest_request_v1":
        raise ValueError("Unsupported request schema.")
    m = _integer(request["m"], "m", 1)
    if m > 64:
        raise ValueError("This bounded CLI supports m<=64; use the Python API for larger inputs.")
    graph = ForestGraph(m)
    survival = request["survival"]
    if type(survival) is not dict or set(survival) != {"numerator", "denominator"}:
        raise ValueError("Survival must contain exact integer numerator and denominator.")
    numerator = _integer(survival["numerator"], "survival numerator", 1)
    denominator = _integer(survival["denominator"], "survival denominator", 1)
    if max(numerator.bit_length(), denominator.bit_length()) > 256:
        raise ValueError("This bounded CLI supports <=256-bit survival integers.")
    x = _survival(Fraction(numerator, denominator), False)

    def tuple_tree(value):
        if type(value) is int:
            return value
        if type(value) is list and len(value) == 2:
            return tuple(tuple_tree(child) for child in value)
        raise ValueError("JSON trees must be integer leaves or binary arrays.")

    if type(request["forest"]) is not list:
        raise ValueError("JSON forest must be an array of roots.")
    f = tuple(tuple_tree(root) for root in request["forest"])
    statistics = graph.history_statistics(f)
    probability = graph.probability(f, x)
    return {
        "schema": "ordinary_forest_result_v1",
        "status": "EXACT_CLASSICAL_COORDINATE",
        "scientific_scope": "One specified labelled forest after one ordinary population from singleton entering labels.",
        "evolution": "ordinary_stochastic_exp_tQ",
        "strict_survival": True,
        "source_witness": False,
        "general_G3_G4_resolved": False,
        "quantum_advantage_established": False,
        "m": graph.m,
        "roots": statistics.roots,
        "encoding": {"code_hex": hex(graph.encode(f)), "bits": graph.code_bits, "token_bits": graph.token_bits, "token_slots": graph.token_slots},
        "survival": {"numerator_hex": hex(x.numerator), "denominator_hex": hex(x.denominator)},
        "histories": statistics.histories,
        "hook_product": statistics.hook_product,
        "forward_neighbors": comb(statistics.roots, 2),
        "reverse_neighbors": sum(type(root) is tuple for root in f),
        "probability": {"numerator_hex": hex(probability.numerator), "denominator_hex": hex(probability.denominator),
                        "numerator_bits": probability.numerator.bit_length(), "denominator_bits": probability.denominator.bit_length()},
        "probability_display": str(probability) if max(probability.numerator.bit_length(), probability.denominator.bit_length()) <= 1024 else "Exact rational stored as hexadecimal integers in RESULT.json.",
    }


def main() -> int:
    import argparse
    import json
    from pathlib import Path
    import sys

    parser = argparse.ArgumentParser(description="Exact classical ordinary-forest coordinate; no source fit or quantum claim.")
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.output.exists():
            raise ValueError("Output directory already exists; choose a new path.")
        if args.request.is_symlink():
            raise ValueError("Request must be a regular file, not a symlink.")
        if args.request.stat().st_size > 65536:
            raise ValueError("Request exceeds the bounded CLI's 64 KiB input limit.")

        def unique_object(pairs):
            obj = {}
            for key, value in pairs:
                if key in obj:
                    raise ValueError(f"Duplicate JSON field: {key}.")
                obj[key] = value
            return obj

        request = json.loads(args.request.read_text(), object_pairs_hook=unique_object)
        result = evaluate_request(request)
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print(f"Invalid ordinary-forest request: {error}", file=sys.stderr)
        return 2
    try:
        args.output.mkdir(parents=True, exist_ok=False)
    except OSError as error:
        print(f"Cannot create ordinary-forest output: {error}", file=sys.stderr)
        return 2
    (args.output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    (args.output / "REPORT.md").write_text(
        f"# Exact classical ordinary-forest coordinate\n\n"
        f"Probability: **{result['probability_display']}**. The specified forest has {result['roots']} roots on {result['m']} entering labels. "
        f"Its {result['histories']} compatible merger histories were counted without constructing the full forest law.\n\n"
        "This evaluates one ordinary stochastic population with exact rational survival strictly between zero and one. "
        "It does not fit observations, certify a source witness, solve general G3/G4, or demonstrate a quantum advantage. "
        "The optional Python Hermitian-dilation API represents a different evolution and is not used in this result.\n"
    )
    print(result["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

