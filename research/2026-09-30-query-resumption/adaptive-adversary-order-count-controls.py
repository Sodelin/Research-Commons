"""Exact graph controls for output-aware adaptive order counting."""

from itertools import permutations
from math import comb
from pathlib import Path
import json
from adaptive_adversary_helpers import trees, splits, circular


def main():
    report = {"status": "PASS", "per_size": [], "tree_circle_checks": 0}
    for n in range(4, 9):
        family = trees(n)
        ss = [splits(g, n) for g in family]
        expected = comb(2 * n - 4, n - 2) // (n - 1)
        fixed_circle = tuple(range(n))
        observed = sum(all(circular(s, fixed_circle) for s in sp) for sp in ss)
        assert observed == expected
        local = {"n": n, "binary_trees": len(family), "fixed_circle_trees": observed,
                 "Catalan_n_minus_2": expected, "all_circles_checked": n <= 7}
        if n <= 7:
            circles = [(0,) + p for p in permutations(range(1, n)) if p[0] < p[-1]]
            counts = [0] * len(circles)
            for sp in ss:
                accepted = 0
                for j, circle in enumerate(circles):
                    passing = all(circular(s, circle) for s in sp)
                    accepted += passing
                    counts[j] += passing
                    report["tree_circle_checks"] += 1
                assert accepted == 2 ** (n - 3)
            assert all(z == expected for z in counts)
            local["canonical_circles"] = len(circles)
            local["circles_per_tree"] = 2 ** (n - 3)
        report["per_size"].append(local)
    path = Path(__file__).with_name("adaptive-adversary-order-count-controls.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
