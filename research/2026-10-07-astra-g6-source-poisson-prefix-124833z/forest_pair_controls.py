"""Exact finite boundary-forest controls for G6 Appendix A.1.

Contributor: GPT-6 Astra Pro, 2026-10-07. This is a rational reference
calculation, not Lean, not the all-source graph compressor, and not an
exact-calendar law. The output is an unordered rooted forest with one fixed
new-merger bin. Old subtrees remain intact. Private arm routes are marginalized.
Run with --output FILE to retain a new execution receipt without overwriting old ones.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from math import comb, prod
from pathlib import Path
import platform
import time

from finite_source_prefix import Leaf, Tree, contains, graft, leaves, tree_key, tv

Forest = tuple[Tree, ...]
Law = dict[Forest, Q]


def canonical(trees) -> Forest:
    return tuple(sorted(trees, key=tree_key))


def valid_roots(roots: Forest) -> None:
    seen: set[str] = set()
    for root in roots:
        labels = leaves(root)
        if not labels or seen.intersection(labels):
            raise ValueError("Entering roots must have disjoint nonempty labelled descendants.")
        seen.update(labels)


@lru_cache(maxsize=None)
def count_law(k: int, x: Q) -> tuple[Q, ...]:
    """Kingman pure-death counts at pair survival x, exact rational coefficients.

    The entry at j is P(j roots remain from k). The formula uses distinct
    eigenvalues lambda_j=choose(j,2) for j=1,...,k. It is independently
    crosschecked below against explicit two/three/four-root probabilities.
    """
    if not isinstance(x, Q) or not 0 < x <= 1 or k < 0:
        raise ValueError("Require a nonnegative root count and 0 < rational survival <= 1.")
    if k == 0:
        return (Q(1),)
    rates = {j: comb(j, 2) for j in range(1, k + 1)}
    ans = [Q(0)] * (k + 1)
    for j in range(1, k + 1):
        prefactor = prod(rates[r] for r in range(j + 1, k + 1))
        ans[j] = prefactor * sum((
            Q(x ** rates[ell], prod(rates[r] - rates[ell]
                                   for r in range(j, k + 1) if r != ell))
            for ell in range(j, k + 1)), Q(0))
    if min(ans) < 0 or sum(ans, Q(0)) != 1:
        raise AssertionError("The finite death-count formula is not stochastic.")
    return tuple(ans)


def jump(law: Law, new_bin: int) -> Law:
    """One actual uniform unordered live-root pair merger."""
    out = defaultdict(Q)
    for forest, weight in law.items():
        if len(forest) < 2:
            raise ValueError("A merger requires at least two current roots.")
        for i, j in combinations(range(len(forest)), 2):
            dest = canonical([r for h, r in enumerate(forest) if h not in (i, j)] +
                             [graft(forest[i], forest[j], new_bin)])
            out[dest] += weight / comb(len(forest), 2)
    return dict(out)


@lru_cache(maxsize=None)
def edge_law(roots: Forest, x: Q, new_bin: int = 99) -> Law:
    """Full boundary forest, not merely its lineage-count distribution."""
    valid_roots(roots)
    probabilities = count_law(len(roots), x)
    law, out = {canonical(roots): Q(1)}, defaultdict(Q)
    for j in range(len(roots), -1, -1):
        for forest, weight in law.items():
            out[forest] += probabilities[j] * weight
        if j > 1:
            law = jump(law, new_bin)
        else:
            break
    return {forest: weight for forest, weight in out.items() if weight}


def independent_bigon(roots: Forest, g: Q, x: Q, y: Q, new_bin: int = 99) -> Law:
    """CURRENT-root private independent routing, followed by actual arm coalescents."""
    valid_roots(roots)
    if not all(isinstance(v, Q) and 0 < v < 1 for v in (g, x, y)):
        raise ValueError("Natural routing and finite positive arm survivals must be interior.")
    out = defaultdict(Q)
    for bits in product((False, True), repeat=len(roots)):
        left = canonical(root for root, bit in zip(roots, bits) if not bit)
        right = canonical(root for root, bit in zip(roots, bits) if bit)
        routing = g ** len(left) * (1 - g) ** len(right)
        for f, p in edge_law(left, x, new_bin).items():
            for h, q in edge_law(right, y, new_bin).items():
                out[canonical(f + h)] += routing * p * q
    return dict(out)


def joined(forest: Forest, pair: tuple[str, str]) -> bool:
    return any(set(pair).issubset(leaves(tree)) for tree in forest)


def pair_mass(law: Law, pair: tuple[str, str]) -> Q:
    return sum((weight for f, weight in law.items() if joined(f, pair)), Q(0))


def certificate(p: Law, q: Law, representatives: tuple[str, ...]) -> dict[str, Q]:
    """Verify the exact low-rank identities and weighted full-forest TV bound."""
    m = len(representatives)
    pairs = tuple(combinations(representatives, 2))
    all_forests = p.keys() | q.keys()
    if any(pair_mass(p, e) != pair_mass(q, e) for e in pairs):
        raise ValueError("Pair marginals differ; the finite-forest lemma does not apply.")
    delta = {f: p.get(f, Q(0)) - q.get(f, Q(0)) for f in all_forests}
    multi = {f for f in all_forests if m - len(f) >= 2}
    zero = [f for f in all_forests if len(f) == m]
    if len(zero) != 1:
        raise ValueError("The no-new-merger boundary outcome is not unique.")
    pair_count = {f: sum(joined(f, e) for e in pairs) for f in multi}
    for e in pairs:
        single = [f for f in all_forests if len(f) == m - 1 and joined(f, e)]
        if len(single) != 1:
            raise ValueError("A single-pair merger has multiple boundary outcomes.")
        if delta[single[0]] != -sum((delta[f] for f in multi if joined(f, e)), Q(0)):
            raise AssertionError("The single-pair reconstruction identity failed.")
    if delta[zero[0]] != sum(((pair_count[f] - 1) * delta[f] for f in multi), Q(0)):
        raise AssertionError("The no-merger reconstruction identity failed.")
    weighted = sum((pair_count[f] * abs(delta[f]) for f in multi), Q(0))
    multi_p = sum((p.get(f, Q(0)) for f in multi), Q(0))
    multi_q = sum((q.get(f, Q(0)) for f in multi), Q(0))
    return {"tv": tv(p, q), "weighted": weighted, "multi_p": multi_p,
            "multi_q": multi_q, "coarse": comb(m, 2) * (multi_p + multi_q)}


def run_controls() -> dict:
    started, t0 = datetime.now(timezone.utc).isoformat(), time.monotonic()
    families: dict[str, int] = {}
    rows = []
    def check(condition: bool, family: str) -> None:
        if not condition:
            raise AssertionError(f"Failed control: {family}")
        families[family] = families.get(family, 0) + 1
    for x in (Q(1, 7), Q(1, 2), Q(9, 10), Q(1)):
        check(count_law(2, x)[1] == 1 - x, "two-root-count")
        check(count_law(3, x)[1] == 1 - Q(3, 2) * x + Q(1, 2) * x**3,
              "three-root-two-mergers")
        check(sum(count_law(4, x)[1:3], Q(0)) == (1 - x**3)**2,
              "four-root-two-mergers")
    grid = (Q(1, 5), Q(1, 2), Q(4, 5))
    for m in (2, 3, 4, 5):
        roots = canonical(Leaf(f"token:{i}") for i in range(m))
        cases = product(grid, repeat=3) if m <= 4 else (
            (Q(1, 10), Q(99, 100), Q(1, 2)),
            (Q(1, 3), Q(1, 4), Q(3, 4)),
            (Q(1, 2), Q(99, 100), Q(99, 100)))
        for g, x, y in cases:
            loss = g*g*(1-x) + (1-g)**2*(1-y)
            p = independent_bigon(roots, g, x, y)
            q = edge_law(roots, 1-loss)
            check(sum(p.values(), Q(0)) == sum(q.values(), Q(0)) == 1, "normalization")
            for e in combinations(tuple(f"token:{i}" for i in range(m)), 2):
                check(pair_mass(p, e) == pair_mass(q, e) == loss,
                      "actual-source-pair-marginal")
            cert = certificate(p, q, tuple(f"token:{i}" for i in range(m)))
            check(cert["tv"] <= cert["weighted"] <= cert["coarse"], "full-forest-algebra")
            a = max(Q(1), Q(3, 2)*comb(m, 3) + 27*comb(m, 4))
            d = 2*comb(m, 2)*a
            # All comparisons below are rational; no floating square roots.
            check(cert["multi_p"]**2 <= a*a*loss**3, "bigon-multiple-merger-bound")
            check(cert["multi_q"] <= a*loss**2, "edge-multiple-merger-bound")
            check(cert["tv"]**2 <= d*d*loss**3, "independent-bigon-TV-bound")
            if m == 2:
                check(p == q, "two-token-exact-boundary-law")
            rows.append({"roots": m, "g": str(g), "x": str(x), "y": str(y),
                         "loss": str(loss), "states": len(p.keys() | q.keys()),
                         **{k: str(v) for k, v in cert.items()}})
    old = graft(Leaf("old:a"), Leaf("old:b"), 7)
    roots = canonical((old, Leaf("token:1"), Leaf("token:2")))
    p = independent_bigon(roots, Q(1, 3), Q(2, 3), Q(3, 4))
    qloss = Q(1, 3)**2*Q(1, 3) + Q(2, 3)**2*Q(1, 4)
    q = edge_law(roots, 1-qloss)
    check(certificate(p, q, ("old:a", "token:1", "token:2"))["tv"] <=
          certificate(p, q, ("old:a", "token:1", "token:2"))["coarse"],
          "old-subtree-boundary-adapter")
    for forest in p.keys() | q.keys():
        check(any(contains(tree, old) for tree in forest), "old-subtree-preservation")
    # Equal two-token pair marginals do NOT control a readout with two distinct
    # possible bins on its single merger. This is an intentional countercontrol.
    start = canonical((Leaf("a"), Leaf("b")))
    early = canonical((graft(*start, 1),))
    late = canonical((graft(*start, 2),))
    p_bad, q_bad = {early: Q(1)}, {late: Q(1)}
    check(pair_mass(p_bad, ("a", "b")) == pair_mass(q_bad, ("a", "b")) == 1,
          "timed-overclaim-countercontrol")
    check(tv(p_bad, q_bad) == 1 and all(len(f) == 1 for f in p_bad.keys() | q_bad.keys()),
          "timed-overclaim-countercontrol")
    # Add common no-merger mass so the validator reaches the single-output gate.
    p_bad = {start: Q(1, 2), early: Q(1, 2)}
    q_bad = {start: Q(1, 2), late: Q(1, 2)}
    try:
        certificate(p_bad, q_bad, ("a", "b"))
    except ValueError as e:
        check("multiple boundary outcomes" in str(e), "reject-wrong-carrier")
    else:
        raise AssertionError("The wrong timed carrier was not rejected.")
    here = Path(__file__).parent
    return {"status": "PASS_EXACT_FOREST_REFERENCE_NOT_LEAN", "started_utc": started,
            "finished_utc": datetime.now(timezone.utc).isoformat(),
            "seconds": round(time.monotonic()-t0, 6), "python": platform.python_version(),
            "checks": sum(families.values()), "families": families, "cases": rows,
            "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "dependency_sha256": hashlib.sha256((here / "finite_source_prefix.py").read_bytes()).hexdigest(),
            "scope": "Finite exact rational boundary forests at 2-5 entering roots; "
                     "no full calendar or private-register law, no graph compression implementation, "
                     "no Lean execution, and no all-size proof by extrapolation."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError("Refusing to overwrite an existing execution receipt.")
    result = run_controls()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "checks", "families", "seconds", "python")}, indent=2))
