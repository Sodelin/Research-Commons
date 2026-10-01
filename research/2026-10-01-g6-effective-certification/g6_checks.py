"""Exact finite checks for the G6 submitted closure proof.

This is not the full source-catalogue/QE implementation.  It independently
checks cut guards, positive clock embedding, forest kernels, source fixtures,
and the rational confidence/exclusion logic used in the proof.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, isqrt, prod
from pathlib import Path
import hashlib
import json
import platform
import networkx as nx

COUNTS: dict[str, int] = defaultdict(int)
DETAILS: dict[str, object] = {}

def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(group)
    COUNTS[group] += 1


def guard_chain(bigons: tuple[tuple[F, F], ...], bottom: F, top: F,
                cuts: tuple[F, ...]) -> tuple[set[int], list[tuple[int, int, F, F]]]:
    """Return protected bigons and unmarked runs, in backward-time order."""
    if not bottom < top or tuple(sorted(set(cuts))) != cuts:
        raise ValueError("Invalid endpoints/cut list")
    previous = bottom
    for h, u in bigons:
        if not previous < h < u < top:
            raise ValueError("Bigons and connectors must have positive durations")
        previous = u
    marked: set[int] = set()
    L = len(bigons)
    for c in cuts:
        if not bottom < c < top:
            continue
        inside = [i for i, (h, u) in enumerate(bigons) if h <= c <= u]
        if inside:
            marked.update(inside)
            continue
        # In a connector: retain BOTH incident bigons, where present.
        for j in range(L + 1):
            low = bottom if j == 0 else bigons[j - 1][1]
            high = top if j == L else bigons[j][0]
            if low < c < high:
                if j:
                    marked.add(j - 1)
                if j < L:
                    marked.add(j)
                break
    runs = []
    i = 0
    while i < L:
        if i in marked:
            i += 1
            continue
        first = i
        while i + 1 < L and i + 1 not in marked:
            i += 1
        last = i
        low = bottom if first == 0 else bigons[first - 1][1]
        high = top if last == L - 1 else bigons[last + 1][0]
        runs.append((first, last, low, high))
        i += 1
    return marked, runs


def cut_guard_checks() -> None:
    fixtures = 0
    max_ratio = F(0)
    for L in range(8):
        bottom, top = F(0), F(2 * L + 1)
        bigons = tuple((F(2 * i + 1), F(2 * i + 2)) for i in range(L))
        choices = tuple(F(j, 2) for j in range(1, 2 * int(top)))
        for J in range(min(3, len(choices)) + 1):
            for cuts in combinations(choices, J):
                marked, runs = guard_chain(bigons, bottom, top, cuts)
                check(len(marked) <= 2 * J, "cut_guard_mark_bound")
                check(len(runs) <= 2 * J + 1, "cut_guard_run_bound")
                check(all(not any(low < c < high for c in cuts)
                          for _, _, low, high in runs), "cut_guard_no_internal_cut")
                check(set(marked) | {i for a, b, _, _ in runs for i in range(a, b + 1)}
                      == set(range(L)), "cut_guard_complete_partition")
                fixtures += 1
                if J:
                    max_ratio = max(max_ratio, F(len(marked), J))
    # Protecting only a bigon whose own interval contains the cut is insufficient.
    bigons = ((F(1), F(2)), (F(3), F(4)))
    c = F(5, 2)
    naive = {i for i, (h, u) in enumerate(bigons) if h <= c <= u}
    correct, runs = guard_chain(bigons, F(0), F(5), (c,))
    check(not naive and correct == {0, 1} and not runs, "naive_cut_guard_counterexample")
    DETAILS["cut_guard"] = {"fixtures": fixtures, "largest_marks_per_cut": str(max_ratio),
                            "naive_counterexample_cut": str(c)}


# Exact finite Kingman forest kernels.  Tokens carry their entire earlier trees.
Tree = tuple
Forest = tuple[Tree, ...]
Law = dict[Forest, F]

def forest(trees) -> Forest:
    return tuple(sorted(trees, key=repr))

def leaves(k: int) -> Forest:
    return forest(("L", i) for i in range(k))

def merger(a: Tree, b: Tree, tag: int) -> Tree:
    children = sorted((a, b), key=repr)
    return ("N", tag, children[0], children[1])

def pure_death(k: int, j: int, x: F) -> F:
    if not (0 <= x <= 1 and 1 <= j <= k):
        raise ValueError("Invalid pure-death input")
    lam = lambda r: comb(r, 2)
    numerator = prod(lam(r) for r in range(j + 1, k + 1))
    value = sum((x ** lam(ell) /
                 prod(F(lam(m) - lam(ell)) for m in range(j, k + 1) if m != ell)
                 for ell in range(j, k + 1)), F(0))
    return numerator * value

@lru_cache(None)
def population(incoming: Forest, x: F, tag: int) -> tuple[tuple[Forest, F], ...]:
    k = len(incoming)
    if k <= 1:
        return ((incoming, F(1)),)
    levels: dict[int, Law] = {k: {incoming: F(1)}}
    for size in range(k, 1, -1):
        target: Law = defaultdict(F)
        for state, weight in levels[size].items():
            for i, j in combinations(range(size), 2):
                trees = [state[a] for a in range(size) if a != i and a != j]
                trees.append(merger(state[i], state[j], tag))
                target[forest(trees)] += weight / comb(size, 2)
        levels[size - 1] = dict(target)
    result: Law = defaultdict(F)
    for size, level in levels.items():
        count_probability = pure_death(k, size, x)
        for state, weight in level.items():
            if count_probability * weight:
                result[state] += count_probability * weight
    return tuple(result.items())


def bigon(incoming: Forest, x: F, y: F, g: F, tag: int, mode: str) -> Law:
    if not all(0 <= p <= 1 for p in (x, y, g)) or mode not in {"ind", "com"}:
        raise ValueError("Invalid bigon input")
    out: Law = defaultdict(F)
    if mode == "com":
        for survival, weight in ((x, g), (y, 1 - g)):
            for state, p in population(incoming, survival, tag):
                out[state] += weight * p
    else:
        k = len(incoming)
        for mask in range(1 << k):
            left = forest(incoming[i] for i in range(k) if mask >> i & 1)
            right = forest(incoming[i] for i in range(k) if not (mask >> i & 1))
            weight = g ** len(left) * (1 - g) ** len(right)
            for state1, p1 in population(left, x, tag):
                for state2, p2 in population(right, y, tag):
                    out[forest(state1 + state2)] += weight * p1 * p2
    return {state: p for state, p in out.items() if p}


def tv(a: Law, b: Law) -> F:
    return sum((abs(a.get(s, F(0)) - b.get(s, F(0))) for s in a.keys() | b.keys()), F(0)) / 2


def apply_population(law: Law, x: F, tag: int) -> Law:
    out: Law = defaultdict(F)
    for state, p in law.items():
        for result, q in population(state, x, tag):
            out[result] += p * q
    return dict(out)


def apply_bigon(law: Law, x: F, y: F, g: F, tag: int, mode: str) -> Law:
    out: Law = defaultdict(F)
    for state, p in law.items():
        for result, q in bigon(state, x, y, g, tag, mode).items():
            out[result] += p * q
    return dict(out)


def forest_checks() -> None:
    grid = (F(1, 10), F(1, 2), F(9, 10))
    largest_weak_ratio_squared = F(0)
    for k in range(2, 5):
        C = comb(k, 2)
        A = max(F(1), F(3, 2) * comb(k, 3) + 27 * comb(k, 4))
        D = 2 * C * A
        for x, y, g in product(grid, repeat=3):
            ind = bigon(leaves(k), x, y, g, 0, "ind")
            common = bigon(leaves(k), x, y, g, 0, "com")
            q = g * g * (1 - x) + (1 - g) ** 2 * (1 - y)
            ordinary = dict(population(leaves(k), 1 - q, 0))
            error = tv(ind, ordinary)
            check(error * error <= D * D * q ** 3, "independent_weak_bigon_bound")
            check(sum(ind.values()) == 1 and min(ind.values()) >= 0,
                  "independent_kernel_normalization")
            check(sum(common.values()) == 1 and min(common.values()) >= 0,
                  "common_kernel_normalization")
            largest_weak_ratio_squared = max(largest_weak_ratio_squared,
                                             error * error / (D * D * q ** 3))
        for x in (F(1, 100), F(1, 4), F(1, 2), F(9, 10)):
            check(tv(dict(population(leaves(k), x, 0)), dict(population(leaves(k), F(0), 0)))
                  <= C * x, "large_hazard_clipping_bound")
        # Same common chain law with all mergers in one bin, but not after refining it.
        params = ((F(1, 2), F(1, 2), F(1, 2)),
                  (F(1, 4), F(3, 4), F(2, 3)))
        coarse, fine = [], []
        for a, b, c in params:
            for tags, bucket in (((0, 0, 0), coarse), ((0, 1, 2), fine)):
                law = apply_population({leaves(k): F(1)}, a, tags[0])
                law = apply_bigon(law, b, b, F(1, 2), tags[1], "com")
                law = apply_population(law, c, tags[2])
                bucket.append(law)
        check(coarse[0] == coarse[1], "coarse_bin_law_equal")
        check(tv(fine[0], fine[1]) > 0, "refined_bin_law_unequal")
        DETAILS[f"clock_bin_tv_cap_{k}"] = str(tv(fine[0], fine[1]))
    DETAILS["weak_bound_largest_squared_relative_ratio"] = str(largest_weak_ratio_squared)


def clock_embedding_checks() -> None:
    for L in range(13):
        bottom, top = F(7, 5), F(11, 3)
        unit = (top - bottom) / (2 * L + 1)
        # One connector per even position, a parallel-arm interval per odd position.
        values = []
        for j in range(2 * L + 1):
            durations = (F(j + 1, 7),) if j % 2 == 0 else (F(j + 1, 7), F(j + 2, 11))
            for desired in durations:
                rate = desired / unit
                check(rate > 0 and rate * unit == desired, "same_endpoint_positive_clock_embedding")
                values.append(rate)
        check(bottom + (2 * L + 1) * unit == top, "clock_endpoint_exact")


def rare_switch_source(n: int) -> tuple[nx.DiGraph, dict[str, F], list[str]]:
    """A genuine positive binary, cut-child, outer-face rare-reticulation family."""
    if n < 4:
        raise ValueError("n must be >= 4")
    edges = [("R", "U"), ("R", "V"), ("U", "a"), ("U", "H"),
             ("V", "c"), ("V", "W"), ("W", "d"), ("W", "H"), ("H", "b")]
    graph = nx.DiGraph(edges)
    ages = {"R": F(4), "V": F(3), "U": F(2), "W": F(2), "H": F(1),
            "a": F(0), "b": F(0), "c": F(0), "d": F(0)}
    taxa = ["a", "b", "c", "d"]
    # Graft a strictly positive binary comb into the c pendant side.
    parent = "V"
    for j in range(n - 4):
        graph.remove_edge(parent, "c")
        node, new_taxon = f"T{j}", f"x{j}"
        graph.add_edges_from([(parent, node), (node, "c"), (node, new_taxon)])
        ages[node] = F(1, j + 2)
        ages[new_taxon] = F(0)
        taxa.append(new_taxon)
        parent = node
    return graph, ages, taxa


def admitted_fixture(g: nx.DiGraph, ages: dict[str, F], taxa: list[str]) -> bool:
    roots = [v for v in g if g.in_degree(v) == 0]
    if roots != ["R"] or not nx.is_directed_acyclic_graph(g):
        return False
    for v in g:
        expected = (0, 2) if v == "R" else ((1, 0) if v in taxa else None)
        if expected is not None:
            if (g.in_degree(v), g.out_degree(v)) != expected:
                return False
        elif (g.in_degree(v), g.out_degree(v)) not in {(1, 2), (2, 1)}:
            return False
    if not all(ages[u] > ages[v] for u, v in g.edges):
        return False
    undirected = g.to_undirected()
    bridges = {frozenset(e) for e in nx.bridges(undirected)}
    if any(frozenset((h, next(iter(g.successors(h))))) not in bridges
           for h in g if g.in_degree(h) == 2):
        return False
    augmented = undirected.copy()
    augmented.add_edges_from(("OUTER", t) for t in taxa)
    if not nx.check_planarity(augmented)[0]:
        return False
    for v in set(g) - {"R"}:
        copy = g.copy()
        copy.remove_node(v)
        if not (nx.descendants(copy, "R") & set(taxa)):
            return False  # v would dominate every sampled leaf.
    return True


def displayed_splits(g: nx.DiGraph, taxa: list[str]) -> set[frozenset[str]]:
    """Union of nontrivial unrooted splits, represented by a canonical side."""
    hybrids = [v for v in g if g.in_degree(v) == 2]
    parent_lists = [tuple(g.predecessors(h)) for h in hybrids]
    result: set[frozenset[str]] = set()
    taxon_set = set(taxa)
    for chosen in product(*parent_lists):
        tree = g.copy()
        for h, keep in zip(hybrids, chosen):
            for p in list(tree.predecessors(h)):
                if p != keep:
                    tree.remove_edge(p, h)
        for v in tree:
            side = ({v} | nx.descendants(tree, v)) & taxon_set
            other = taxon_set - side
            if min(len(side), len(other)) >= 2:
                key = min((tuple(sorted(side)), tuple(sorted(other))), key=lambda a: (len(a), a))
                result.add(frozenset(key))
    return result


def source_checks() -> None:
    for n in range(4, 13):
        graph, ages, taxa = rare_switch_source(n)
        check(admitted_fixture(graph, ages, taxa), "rare_switch_source_admission")
        default = graph.copy()
        default.remove_edge("W", "H")
        alternative = graph.copy()
        alternative.remove_edge("U", "H")
        default_splits = displayed_splits(default, taxa)
        full_splits = displayed_splits(graph, taxa)
        check(default_splits < full_splits, "rare_switch_target_strictly_changes")
        # On {a,b,c,d}, default has ab|cd; alternate has ac|bd.
        reduced = rare_switch_source(4)[0]
        check(displayed_splits(reduced, ["a", "b", "c", "d"])
              == {frozenset(("a", "b")), frozenset(("a", "c"))}, "rare_switch_quartet_witness")
    for M in range(1, 17):
        for e in (F(1, 1000), F(1, 10), F(1, 2)):
            check(1 - (1 - e) ** M <= M * e, "rare_switch_union_bound")
    DETAILS["rare_switch"] = {"n_checked": list(range(4, 13)), "all_population_rates": "1",
        "base_node_ages": {k: str(v) for k, v in rare_switch_source(4)[1].items()},
        "four_taxon_split_union": ["ab|cd", "ac|bd"],
        "unbounded_n_claim": "hand proof by positive pendant grafting; finite graph checks are not that proof"}


def ceil_log2(q: F) -> int:
    if q <= 0:
        raise ValueError("Positive argument required")
    b = q.numerator.bit_length() - q.denominator.bit_length()
    def two(k: int) -> F:
        return F(1 << k) if k >= 0 else F(1, 1 << (-k))
    while two(b) < q:
        b += 1
    while two(b - 1) >= q:
        b -= 1
    return b


def rational_sqrt_upper(q: F, bits: int = 24) -> F:
    if q < 0 or bits < 0:
        raise ValueError("Invalid square-root input")
    scale = 1 << bits
    floor_value = (q.numerator * scale * scale) // q.denominator
    z = isqrt(floor_value)
    if F(z * z, scale * scale) < q:
        z += 1
    return F(z, scale)


def coordinate_radius(count: int, dimension: int, alpha_weight: F) -> F:
    if count < 0 or dimension < 1 or not 0 < alpha_weight < 1:
        raise ValueError("Invalid confidence contract")
    if count == 0:
        return F(1)
    A = F(2 * dimension * count * (count + 1), 1) / alpha_weight
    b = ceil_log2(A)
    return min(F(1), rational_sqrt_upper(F(b, 2 * count), bits=count.bit_length() + 8))


def keep_candidate(cloud: tuple[tuple[F, ...], ...] | None, epsilon: F,
                   empirical: tuple[F, ...], radii: tuple[F, ...], *, complete: bool) -> bool:
    """An incomplete catalogue cannot exclude a target.  Cloud correctness is a proof input."""
    if epsilon < 0 or len(empirical) != len(radii) or any(r < 0 for r in radii):
        raise ValueError("Invalid approximation/confidence inputs")
    if any(not 0 <= p <= 1 for p in empirical):
        raise ValueError("Probabilities must lie in [0,1]")
    if not complete or cloud is None:
        return True
    if any(len(point) != len(empirical) for point in cloud):
        raise ValueError("Incompatible joint-profile dimensions")
    return any(all(abs(x - y) <= r + epsilon for x, y, r in zip(point, empirical, radii))
               for point in cloud)


def confidence_checks() -> None:
    for dimension in (2, 3, 37, 266):
        for count in (1, 5, 20, 100, 1000, 10000, 1000000):
            weight = F(1, 100)
            r = coordinate_radius(count, dimension, weight)
            if r < 1:
                b = ceil_log2(F(2 * dimension * count * (count + 1), 1) / weight)
                check(2 * count * r * r >= b, "rational_hoeffding_radius")
                check(F(2 * dimension, 1 << b) <= weight / (count * (count + 1)),
                      "anytime_error_spending_bound")
    for power in range(16, 81, 8):
        check(coordinate_radius(1 << power, 2, F(1, 20)) <= F(1, 1 << (power // 3)),
              "confidence_rounding_precision_increases")
    # A boundary target must survive whenever its closure law is inside the confidence box.
    p = (F(1, 2), F(1, 2))
    eps = F(1, 10)
    cloud = ((F(3, 5), F(2, 5)),)
    check(keep_candidate(cloud, eps, p, (F(0), F(0)), complete=True),
          "hausdorff_error_not_ignored")
    check(keep_candidate((), eps, p, (F(0), F(0)), complete=False),
          "incomplete_catalogue_never_excludes")
    check(not keep_candidate((), eps, p, (F(0), F(0)), complete=True),
          "proved_empty_catalogue_excludes")
    boundary_cloud = ((F(1, 100), F(99, 100)),)
    check(keep_candidate(boundary_cloud, F(1, 100), (F(0), F(1)), (F(0), F(0)), complete=True),
          "limiting_target_label_retained")
    # Joint shared parameters, not independent row fits: two diagonal profile points.
    joint_cloud = ((F(1, 4), F(3, 4), F(1, 4), F(3, 4)),
                   (F(3, 4), F(1, 4), F(3, 4), F(1, 4)))
    mixed_empirical = (F(1, 4), F(3, 4), F(3, 4), F(1, 4))
    check(not keep_candidate(joint_cloud, F(1, 100), mixed_empirical, (F(0),) * 4, complete=True),
          "same_source_joint_profile_enforced")
    D, alpha, gap = 2, F(1, 20), F(1, 2)
    N = 1_000_000
    r = coordinate_radius(N, D, alpha)
    empirical = (F(1, 4), F(3, 4))
    check(not keep_candidate(((F(3, 4), F(1, 4)),), gap / 8, empirical, (r, r), complete=True),
          "separated_target_eventually_excluded")
    check(keep_candidate((empirical,), gap / 8, empirical, (r, r), complete=True),
          "true_target_retained")
    # Marginal products are not the joint law of two observations of the same locus.
    joint = {((0, 0),): F(1, 2), ((1, 1),): F(1, 2)}
    independent = {((a, b),): F(1, 4) for a, b in product((0, 1), repeat=2)}
    check(tv(joint, independent) == F(1, 2), "within_locus_dependence_counterexample")
    # A TV envelope of beta can make two clean Bernoulli laws indistinguishable.
    p0, p1, beta = F(1, 4), F(3, 4), F(1, 4)
    q = (p0 + p1) / 2
    check(abs(q - p0) == beta and abs(q - p1) == beta, "closed_tv_noise_boundary_overlap")
    DETAILS["confidence"] = {"separated_example_n": N, "rational_coordinate_radius": str(r),
        "fixed_sample_bound": "k >= 32 Delta^(-2) log(2D/alpha), with net error <= Delta/8",
        "full_catalogue_executed": False}


def main() -> None:
    cut_guard_checks()
    forest_checks()
    clock_embedding_checks()
    source_checks()
    confidence_checks()
    here = Path(__file__).resolve()
    receipt = {"status": "PASS", "arithmetic": "exact rational; combinatorial graph checks",
        "python": platform.python_version(), "networkx": nx.__version__,
        "check_counts": dict(COUNTS), "total_checks": sum(COUNTS.values()),
        "details": DETAILS, "script_sha256": hashlib.sha256(here.read_bytes()).hexdigest(),
        "not_executed": ["complete all-source graph catalogue", "complete calendar compiler",
                         "general hazard-cell enumeration", "integrated empirical inference on biological data",
                         "independent mathematical review", "proof-assistant verification"],
        "separate_verification": "hazard_cells.wl was evaluated through Wolfram; see WOLFRAM-RECEIPT.md"}
    (here.parent / "checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))

if __name__ == "__main__":
    main()
