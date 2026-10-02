"""Exact original-source check of the binary G5 two-tip obstruction.

No floating-point law comparison: routes have exact Fraction weights, every
pair's first-meeting age measure is enumerated, and all population pair rates
are 1 forever. Meeting is permanent because all hybrids have one tip below
them and no hybrid lies above any first meeting. Thus each pair law is the
exact mixture of shifted Exp(1) laws reported by this check.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import platform
import networkx as nx

X = tuple("abcfz")
ROOT = "O"
HYBRIDS = ("Ha", "Hb", "Hc", "Hf")


def make_source(kind):
    common = [("O", "R"), ("O", "z"), ("R", "A"), ("R", "D")]
    ages = {"O": 16, "R": 14, "D": 8,
            "Ha": 2, "Hb": 2, "Hc": 2, "Hf": 2}
    if kind == "triangle":
        edges = common + [("A", "Ha"), ("A", "Hb"),
                          ("D", "B"), ("D", "C"),
                          ("B", "Ha"), ("B", "BC"),
                          ("C", "Hb"), ("C", "CC"),
                          ("BC", "Hc"), ("BC", "Hf"),
                          ("CC", "Hc"), ("CC", "Hf")]
        ages.update(A=4, B=6, C=6, BC=5, CC=5)
    elif kind == "star":
        edges = common + [("A", "Ha"), ("A", "Hb"),
                          ("D", "S"), ("D", "DC"),
                          ("S", "F"), ("S", "SC"),
                          ("F", "Ha"), ("F", "Hb"),
                          ("DC", "Hc"), ("DC", "Hf"),
                          ("SC", "Hc"), ("SC", "Hf")]
        ages.update(A=8, S=6, F=4, DC=5, SC=5)
    else:
        raise ValueError(kind)
    edges += [("H" + x, x) for x in "abcf"]
    ages.update({x: 0 for x in X})
    # Every ordered edge gets an explicit identity; no parallel occurrences
    # are present here, and no contraction is performed in the source audit.
    G = nx.MultiDiGraph()
    for eid, (u, v) in enumerate(edges):
        G.add_edge(u, v, key=eid, eid=eid, rate=1)
    return G, ages


def audit(G, ages):
    assert nx.is_directed_acyclic_graph(G)
    assert nx.descendants(G, ROOT) | {ROOT} == set(G)
    assert set(v for v in G if G.out_degree(v) == 0) == set(X)
    for v in G:
        degree = (G.in_degree(v), G.out_degree(v))
        assert degree == ((0, 2) if v == ROOT else
                          (1, 0) if v in X else
                          (2, 1) if v in HYBRIDS else (1, 2))
    assert all(ages[u] > ages[v] for u, v, _ in G.edges(keys=True))
    U = nx.MultiGraph()
    U.add_edges_from((u, v, k) for u, v, k in G.edges(keys=True))
    # An occurrence is a bridge precisely if deleting that occurrence alone
    # disconnects its endpoints. This respects original edge identities.
    for h in HYBRIDS:
        u, v, k = next(iter(G.out_edges(h, keys=True)))
        V = U.copy()
        V.remove_edge(u, v, k)
        assert not nx.has_path(V, u, v)
        assert nx.descendants(G, h) == {h[1:]}
    # Root is the lowest stable ancestor of all taxa, using all original paths.
    all_paths = [p for x in X for p in nx.all_simple_paths(G, ROOT, x)]
    assert set.intersection(*(set(p) for p in all_paths)) == {ROOT}
    return {"vertices": len(G), "edges": G.number_of_edges(),
            "taxa": list(X), "hybrids": 4, "root_LSA": True,
            "original_child_edges_bridges": True, "strict_ages": True,
            "all_population_pair_rates": 1, "all_parent_weights": "1/2"}


def switchings(G):
    hybrid_edges = [tuple(G.in_edges(h, keys=True)) for h in HYBRIDS]
    for choices in product(*hybrid_edges):
        T = G.copy()
        for hs, chosen in zip(hybrid_edges, choices):
            for edge in hs:
                if edge != chosen:
                    T.remove_edge(*edge)
        assert all(T.in_degree(v) == 1 for v in T if v != ROOT)
        yield T, Fraction(1, 16)


def ancestral_path(T, tip):
    edges = []
    while tip != ROOT:
        u, v, k = next(iter(T.in_edges(tip, keys=True)))
        edges.append((u, v, k))
        tip = u
    return tuple(edges)


def active(path, t, ages):
    if t >= ages[ROOT]:
        return "TAIL"
    occupied = [e for e in path if ages[e[1]] <= t < ages[e[0]]]
    assert len(occupied) == 1
    return occupied[0]


def first_meeting(T, a, b, ages):
    pa, pb = ancestral_path(T, a), ancestral_path(T, b)
    grid = sorted(set(ages.values()))
    same = [active(pa, t, ages) == active(pb, t, ages) for t in grid]
    j = same.index(True)
    assert not any(same[:j]) and all(same[j:])
    # Also test interval interiors independently; endpoints are older-side.
    for l, r in zip(grid, grid[1:]):
        t = Fraction(l + r, 2)
        assert (active(pa, t, ages) == active(pb, t, ages)) == (t >= grid[j])
    return grid[j]


def pair_measures(G, ages):
    measures = {"".join(p): defaultdict(Fraction) for p in combinations(X, 2)}
    count = 0
    for T, weight in switchings(G):
        for a, b in combinations(X, 2):
            measures[a + b][first_meeting(T, a, b, ages)] += weight
            count += 1
    assert all(sum(m.values()) == 1 for m in measures.values())
    return {p: dict(m) for p, m in measures.items()}, count


def clusters(G):
    result = {frozenset((x,)) for x in X} | {frozenset(X)}
    displayed = []
    for T, _ in switchings(G):
        per_tree = set()
        # Descendant taxa on every retained original edge give exactly the
        # clusters after pruning dead twigs and suppressing unary vertices.
        for u, v, k in T.edges(keys=True):
            c = frozenset((nx.descendants(T, v) | {v}) & set(X))
            if c:
                per_tree.add(c)
        per_tree.add(frozenset(X))
        result |= per_tree
        displayed.append(per_tree)
    return result, displayed


def splits(clusters):
    return {frozenset((c, frozenset(X) - c)) for c in clusters if 2 <= len(c) <= len(X)-2}


def quartets(clusters):
    result = set()
    for A in map(frozenset, combinations(X, 4)):
        for c in clusters:
            U = c & A
            if len(U) == 2:
                result.add((A, frozenset((U, A-U))))
    return result


def fmt_cluster(c):
    return "".join(sorted(c))


def fmt_split(s):
    return "|".join(sorted(map(fmt_cluster, s)))


def main():
    sources, measures, cs, ss, qs = {}, {}, {}, {}, {}
    total_checks = 0
    for kind in ("triangle", "star"):
        G, ages = make_source(kind)
        sources[kind] = audit(G, ages)
        sources[kind]["ages"] = ages
        sources[kind]["original_edges"] = [list(e) for e in G.edges(keys=True)]
        measures[kind], n = pair_measures(G, ages)
        total_checks += n
        cs[kind], displayed = clusters(G)
        ss[kind], qs[kind] = splits(cs[kind]), quartets(cs[kind])
        assert len(displayed) == 16
    assert measures["triangle"] == measures["star"]
    witness_c = frozenset("abc")
    witness_s = frozenset((witness_c, frozenset("fz")))
    assert witness_c in cs["star"] and witness_c not in cs["triangle"]
    assert frozenset("fz") not in cs["triangle"]
    assert witness_s in ss["star"] and witness_s not in ss["triangle"]
    # Do not incorrectly promote this S lower bound to a Q lower bound.
    assert qs["star"] == qs["triangle"]
    report = {
        "status": "PASS", "attribution": "dot, dedicated G5 panel-minimality lane",
        "sources": sources, "exact_pair_laws_equal": True,
        "mechanisms": ["common-site", "independent-live-ancestor"],
        "mechanism_justification": "Each hybrid has exactly one original descendant tip; every pair first meeting lies above every hybrid, and there are no older hybrid sites.",
        "formula": "P(T_ab>t)=sum_m w_ab(m)*exp(-max(t-m,0)); all rates are exactly 1",
        "pair_first_meeting_measures": {p: {str(t): str(w) for t, w in m.items()} for p, m in measures["star"].items()},
        "exact_route_pair_checks": total_checks,
        "rooted_clusters": {k: sorted(map(fmt_cluster, v)) for k, v in cs.items()},
        "splits": {k: sorted(map(fmt_split, v)) for k, v in ss.items()},
        "star_only_rooted_clusters": sorted(map(fmt_cluster, cs["star"]-cs["triangle"])),
        "triangle_only_rooted_clusters": sorted(map(fmt_cluster, cs["triangle"]-cs["star"])),
        "star_only_splits": sorted(map(fmt_split, ss["star"]-ss["triangle"])),
        "triangle_only_splits": sorted(map(fmt_split, ss["triangle"]-ss["star"])),
        "quartet_unions_equal": qs["star"] == qs["triangle"],
        "versions": {"python": platform.python_version(), "networkx": nx.__version__},
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": "Exact finite source/routing controls and analytic complete pair-law equality; not an all-k obstruction, Q lower bound, numerical fit, or full Lean proof."
    }
    out = Path(__file__).with_name("binary-matched-pair-laws-results.json")
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
