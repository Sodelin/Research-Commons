"""Research implementation: adaptive anchored order learning by Gallai repairs.

Exact binary tree-family support, common circle promised. Query complexity
O(n^2 log n); computation is polynomial and deliberately unoptimized.
The interval hierarchy derives from classical Gallai substitution; the
signed comparison system derives from Keijsper--Pendavingh. See proof packet.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import cmp_to_key
from itertools import combinations
from math import comb
from order_recovery import ParityForest, Oracle, valid_mask, sparse_module


def equations(q: tuple[int, ...], mask: int, anchor: int, indices: dict):
    for bit, pair in enumerate(((q[0], q[1]), (q[0], q[2]), (q[0], q[3]))):
        if not mask & (1 << bit):
            continue
        paired = set(pair)
        if anchor not in paired:
            paired = set(q) - paired
        z = next(x for x in paired if x != anchor)
        x, y = sorted(set(q) - paired)
        yield (indices[tuple(sorted((z, x)))], indices[tuple(sorted((z, y)))],
               int(z > x) ^ int(z > y))


def extract_order(labels, indices, values):
    def before(x, y):
        return bool(values[indices[tuple(sorted((x, y)))]] ^ int(x > y))
    result = tuple(sorted(labels, key=cmp_to_key(lambda x, y: -1 if before(x, y) else 1)))
    if any(not before(x, y) for i, x in enumerate(result) for y in result[i + 1:]):
        raise ValueError("Current affine assignment is not transitive")
    return result


def interval_hierarchy(order: tuple[int, ...], colors: dict[tuple[int, int], int]):
    """Polynomial reference construction via minimum interval-module covers.

All pair colors in a transitive coloring satisfy c(x,z) in {c(x,y),c(y,z)}.
Gallai's module partition split into order runs gives an interval partition
with <=2 quotient colors. A minimum proper-module cover cannot have >2:
otherwise such a partition of its quotient lets us merge consecutive blocks.
"""
    def color(x, y):
        return colors[tuple(sorted((x, y)))]
    weights = {c: 0 for c in set(colors.values())}
    records = []

    def build(labels):
        size = len(labels)
        if size == 1:
            return
        allowed = [[] for _ in range(size)]
        for lo in range(size):
            for hi in range(lo + 1, size + 1):
                if lo == 0 and hi == size:
                    continue
                inside = labels[lo:hi]
                outside = labels[:lo] + labels[hi:]
                if all(all(color(z, x) == color(z, inside[0]) for x in inside[1:])
                       for z in outside):
                    allowed[lo].append(hi)
        best = [None] * (size + 1)
        best[0] = ()
        for lo in range(size):
            if best[lo] is None:
                continue
            for hi in allowed[lo]:
                candidate = best[lo] + ((lo, hi),)
                if best[hi] is None or len(candidate) < len(best[hi]):
                    best[hi] = candidate
        intervals = best[size]
        if intervals is None or len(intervals) < 2:
            raise AssertionError("Proper singleton modules must give a cover")
        children = [labels[lo:hi] for lo, hi in intervals]
        palette = {color(a[0], b[0]) for a, b in combinations(children, 2)}
        if len(palette) > 2:
            raise AssertionError("Transitive Gallai quotient has more than two colors")
        for a, b in combinations(children, 2):
            expected = color(a[0], b[0])
            if not all(color(x, y) == expected for x in a for y in b):
                raise AssertionError("Module quotient is not homogeneous")
        for c in palette:
            weights[c] += len(children)
        records.append((tuple(labels), tuple(children), tuple(sorted(palette))))
        for child in children:
            build(child)
    build(order)
    assert all(w > 0 for w in weights.values())
    assert sum(w for w in weights.values()) <= 4 * len(order) - 4
    return weights, records


class WeightedComponents:
    def __init__(self, weights):
        self.bits = {c: 0 for c in weights}
        self.owner = {c: c for c in weights}
        self.members = {c: {c} for c in weights}
        self.weights = dict(weights)
        self.original_weights = dict(weights)
        self.flipped_weight = 0
        self.merges = 0
        self.flip_events = []

    def constrain(self, a, b, parity):
        ra, rb = self.owner[a], self.owner[b]
        wrong = self.bits[a] ^ self.bits[b] != parity
        if ra == rb:
            if wrong:
                raise ValueError("Exact support violates the common-circle promise")
            return False
        if self.weights[ra] < self.weights[rb]:
            ra, rb = rb, ra
        flipped = set()
        if wrong:
            flipped = self.members[rb].copy()
            for c in flipped:
                self.bits[c] ^= 1
            self.flipped_weight += self.weights[rb]
            self.flip_events.append(tuple(sorted(flipped)))
        for c in self.members[rb]:
            self.owner[c] = ra
        self.members[ra].update(self.members.pop(rb))
        self.weights[ra] += self.weights.pop(rb)
        self.merges += 1
        return bool(flipped)


@dataclass(frozen=True)
class AdaptiveOrder:
    order: tuple[int, ...]
    oracle_calls: int
    cycle_phase_calls: int
    initial_colors: int
    hierarchy_weight: int
    repairs: int
    parity_merges: int
    distinct_adjacencies: int
    flipped_weight: int
    query_bound: int


def learn_order(n: int, oracle: Oracle, anchor: int = 0) -> AdaptiveOrder:
    if not isinstance(n, int) or isinstance(n, bool) or n < 4:
        raise ValueError("n must be an integer at least four")
    if not isinstance(anchor, int) or isinstance(anchor, bool) or not 0 <= anchor < n:
        raise ValueError("anchor must name an input taxon")
    labels = tuple(x for x in range(n) if x != anchor)
    indices = {p: i for i, p in enumerate(combinations(labels, 2))}
    forest = ParityForest(len(indices))
    cache = {}

    def ask(q):
        if q not in cache:
            cache[q] = valid_mask(oracle(q))
        return cache[q]

    # A triangle's directed cycle has pair bits 1,0,1 in naming order.
    # Reversal preserves every parity equation, so testing this cycle suffices.
    for x, y, z in combinations(labels, 3):
        targets = ((indices[(x, y)], 1), (indices[(x, z)], 0), (indices[(y, z)], 1))
        root_values = {}
        possible = True
        for variable, target in targets:
            root, parity = forest.find(variable)
            required = target ^ parity
            if root in root_values and root_values[root] != required:
                possible = False
                break
            root_values[root] = required
        if possible:
            q = tuple(sorted((anchor, x, y, z)))
            before = forest.components
            for a, b, parity in equations(q, ask(q), anchor, indices):
                forest.constrain(a, b, parity)
            if forest.components >= before:
                raise AssertionError("Cycle witness did not increase parity rank")
    cycle_calls = len(cache)
    initial_roots = {forest.find(i)[0] for i in range(len(indices))}
    if not 1 <= len(initial_roots) <= n - 2:
        raise AssertionError("All-transitive affine space has invalid dimension")
    base_values = [forest.find(i)[1] for i in range(len(indices))]
    color_values = [forest.find(i)[0] for i in range(len(indices))]
    colors = {pair: color_values[index] for pair, index in indices.items()}
    current = extract_order(labels, indices, base_values)
    for i, x in enumerate(current):
        for j in range(i + 1, len(current)):
            y = current[j]
            for z in current[j + 1:]:
                if colors[tuple(sorted((x, z)))] not in {
                    colors[tuple(sorted((x, y)))], colors[tuple(sorted((y, z)))]}:
                    raise AssertionError("Component colors are not transitive")
    weights, hierarchy = interval_hierarchy(current, colors)
    weighted = WeightedComponents(weights)
    adjacency_seen = set()
    repairs = 0
    while True:
        adjacency_seen.update(tuple(sorted(pair)) for pair in zip(current, current[1:]))
        repaired = False
        for left, right in zip(current, current[1:]):
            for third in labels:
                if third in (left, right):
                    continue
                q = tuple(sorted((anchor, left, right, third)))
                changed = False
                prior_weight = weighted.flipped_weight
                for a, b, parity in equations(q, ask(q), anchor, indices):
                    changed |= weighted.constrain(color_values[a], color_values[b],
                                                  parity ^ base_values[a] ^ base_values[b])
                if changed:
                    values = [value ^ weighted.bits[color_values[i]] for i, value in enumerate(base_values)]
                    following = extract_order(labels, indices, values)
                    before_pairs = {tuple(sorted(pair)) for pair in zip(current, current[1:])}
                    after_pairs = {tuple(sorted(pair)) for pair in zip(following, following[1:])}
                    assert len(after_pairs - before_pairs) <= 2 * (weighted.flipped_weight - prior_weight)
                    current = following
                    repairs += 1
                    repaired = True
                    break
            if repaired:
                break
        if not repaired:
            break
    total_weight = sum(weights.values())
    log_bound = (total_weight - 1).bit_length()
    assert weighted.flipped_weight <= total_weight * log_bound
    adjacency_bound = n - 2 + 2 * total_weight * log_bound
    assert len(adjacency_seen) <= adjacency_bound
    budget = comb(n - 1, 2) + (n - 3) * adjacency_bound
    assert len(cache) <= budget
    return AdaptiveOrder((anchor,) + current, len(cache), cycle_calls, len(initial_roots),
                         total_weight, repairs, weighted.merges, len(adjacency_seen),
                         weighted.flipped_weight, budget)


@dataclass(frozen=True)
class AdaptiveFull:
    learned: AdaptiveOrder
    gap_pairs: frozenset[tuple[int, int]]
    sparse_calls: int
    total_calls: int

    def nontrivial_sides(self):
        return frozenset(frozenset(self.learned.order[i + 1:j + 1]) for i, j in self.gap_pairs)


def recover_all(n: int, oracle: Oracle, anchor: int = 0) -> AdaptiveFull:
    learned = learn_order(n, oracle, anchor)
    order = learned.order
    def relabeled(q):
        original = tuple(sorted(order[i] for i in q))
        mask = valid_mask(oracle(original))
        result = 0
        for bit, pair in enumerate(((original[0], original[1]), (original[0], original[2]),
                                    (original[0], original[3]))):
            if mask & (1 << bit):
                side = frozenset(pair)
                for new_bit, partner in enumerate(q[1:]):
                    target = frozenset((order[q[0]], order[partner]))
                    if side == target or side == frozenset(original) - target:
                        result |= 1 << new_bit
                        break
        return result
    sparse = sparse_module().recover(n, relabeled)
    return AdaptiveFull(learned, sparse.splits, sparse.oracle_calls,
                        learned.oracle_calls + sparse.oracle_calls)
