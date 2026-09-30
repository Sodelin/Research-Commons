"""Stream exact anchored quartet support into the classical signed pair graph.

Keijsper--Pendavingh (arXiv:1308.5206), Section 4.6, applied to the
intersection of the order spaces of a nonempty binary displayed-tree family.
No circular order, tree, or blob decomposition is supplied. Standard library.
Support bits 1,2,4 refer to ab|cd, ac|bd, ad|bc for sorted a<b<c<d.
The sparse second stage is imported, attributed, and preserved unchanged.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import cmp_to_key
from itertools import combinations
from pathlib import Path
from typing import Callable
import importlib.util
import sys

Oracle = Callable[[tuple[int, int, int, int]], int]


class ParityForest:
    def __init__(self, count: int):
        self.parent = list(range(count))
        self.size = [1] * count
        self.parity = [0] * count
        self.components = count

    def find(self, x: int) -> tuple[int, int]:
        if self.parent[x] != x:
            root, offset = self.find(self.parent[x])
            self.parity[x] ^= offset
            self.parent[x] = root
        return self.parent[x], self.parity[x]

    def constrain(self, x: int, y: int, offset: int) -> None:
        a, px = self.find(x)
        b, py = self.find(y)
        if a == b:
            if px ^ py != offset:
                raise ValueError("Anchored support admits no common circular order")
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.parent[b] = a
        self.parity[b] = px ^ py ^ offset
        self.size[a] += self.size[b]
        self.components -= 1


@dataclass(frozen=True)
class OrderResult:
    order: tuple[int, ...]
    anchored_calls: int
    comparison_variables: int
    independent_orientations: int
    imposed_equations: int


def valid_mask(value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or not 1 <= value <= 7:
        raise ValueError("Exact binary displayed support must be a nonempty three-bit integer")
    return value


def learn_order(n: int, oracle: Oracle, anchor: int = 0) -> OrderResult:
    if not isinstance(n, int) or isinstance(n, bool) or n < 4:
        raise ValueError("n must be an integer at least four")
    if not isinstance(anchor, int) or isinstance(anchor, bool) or not 0 <= anchor < n:
        raise ValueError("anchor must name one of the n taxa")
    labels = [x for x in range(n) if x != anchor]
    indices = {p: i for i, p in enumerate(combinations(labels, 2))}
    forest = ParityForest(len(indices))

    def directed(x: int, y: int) -> tuple[int, int]:
        return indices[tuple(sorted((x, y)))], int(x > y)

    calls = equations = 0
    for triple in combinations(labels, 3):
        q = tuple(sorted((anchor,) + triple))
        mask = valid_mask(oracle(q))
        calls += 1
        for bit, pair in enumerate(((q[0], q[1]), (q[0], q[2]), (q[0], q[3]))):
            if not mask & (1 << bit):
                continue
            paired = set(pair)
            if anchor not in paired:
                paired = set(q) - paired
            z = next(x for x in paired if x != anchor)
            x, y = sorted(set(q) - paired)
            a, pa = directed(z, x)
            b, pb = directed(z, y)
            forest.constrain(a, b, pa ^ pb)
            equations += 1

    # Root values zero choose one solution; no exponential orientation enumeration.
    values = [forest.find(i)[1] for i in range(len(indices))]

    def precedes(x: int, y: int) -> bool:
        i, offset = directed(x, y)
        return bool(values[i] ^ offset)

    order_tail = tuple(sorted(labels, key=cmp_to_key(lambda x, y: -1 if precedes(x, y) else 1)))
    # Defensive check of the representation, independent of sorting behavior.
    if any(not precedes(x, y) for i, x in enumerate(order_tail) for y in order_tail[i + 1:]):
        raise ValueError("Signed assignment is not transitive; input violated the dense support contract")
    if forest.components > n - 2:
        raise ValueError("Input violates the nonempty binary-tree-family promise")
    return OrderResult((anchor,) + order_tail, calls, len(indices), forest.components, equations)


def sparse_module():
    path = Path(__file__).resolve().parents[1] / "2026-09-30-astra-sparse-query" / "sparse_quartet.py"
    name = "attributed_astra_sparse_quartet"
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, path)
        if spec is None or spec.loader is None:
            raise ImportError(f"Cannot load attributed sparse method at {path}")
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    return sys.modules[name]


@dataclass(frozen=True)
class FullResult:
    order_result: OrderResult
    gap_pairs: frozenset[tuple[int, int]]
    sparse_calls: int
    total_calls: int

    def nontrivial_sides(self) -> frozenset[frozenset[int]]:
        order = self.order_result.order
        return frozenset(frozenset(order[i + 1:j + 1]) for i, j in self.gap_pairs)


def recover_all(n: int, oracle: Oracle, anchor: int = 0) -> FullResult:
    learned = learn_order(n, oracle, anchor)
    order = learned.order

    def relabeled(q: tuple[int, int, int, int]) -> int:
        original = tuple(sorted(order[i] for i in q))
        mask = valid_mask(oracle(original))
        answer = 0
        for bit, pair in enumerate(((original[0], original[1]), (original[0], original[2]),
                                    (original[0], original[3]))):
            if not mask & (1 << bit):
                continue
            side = frozenset(pair)
            for new_bit, partner in enumerate(q[1:]):
                new_side = frozenset((order[q[0]], order[partner]))
                if new_side == side or new_side == frozenset(original) - side:
                    answer |= 1 << new_bit
                    break
        return answer

    result = sparse_module().recover(n, relabeled)
    return FullResult(learned, result.splits, result.oracle_calls,
                      learned.anchored_calls + result.oracle_calls)
