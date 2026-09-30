"""Check a containing-tree hypothesis for partial complete anchored masks.

All binary tree families sharing a canonical circle and all anchored query
subsets are enumerated at n<=6. Truth for trees comes from graph splits;
parity assignments are exhausted independently of the production learner.
This is not source-network realization for arbitrary tree-family witnesses.
"""
from itertools import combinations, permutations
from pathlib import Path
import importlib.util
import json

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("graph_truth", BASE.parent / "2026-09-30-root-exact-query" / "verify_candidate_order.py")
truth = importlib.util.module_from_spec(spec)
spec.loader.exec_module(truth)


def run(n):
    tail = tuple(range(1, n))
    pairs = tuple(combinations(tail, 2))
    pidx = {p: i for i, p in enumerate(pairs)}
    triples = tuple(combinations(tail, 3))
    max_bits = 1 << len(pairs)
    universe = (1 << max_bits) - 1
    all_orders = {}
    transitive = 0
    for P in permutations(tail):
        rank = {x: i for i, x in enumerate(P)}
        bits = sum(int(rank[x] < rank[y]) << i for i, (x, y) in enumerate(pairs))
        all_orders[bits] = (0,) + P
        transitive |= 1 << bits
    allowed = []
    for x, y, z in triples:
        constraints = ((pidx[(x, y)], pidx[(x, z)], 0),
                       (pidx[(x, y)], pidx[(y, z)], 1),
                       (pidx[(x, z)], pidx[(y, z)], 0))
        row = [universe]
        for mask in range(1, 8):
            vals = 0
            for bits in range(max_bits):
                if all(not(mask & (1 << k)) or
                       (((bits >> a) ^ (bits >> b)) & 1) == s
                       for k, (a, b, s) in enumerate(constraints)):
                    vals |= 1 << bits
            row.append(vals)
        allowed.append(row)
    trees = truth.trees(n)
    splits = [truth.graph_splits(G, n) for G in trees]
    tree_spaces = []
    profiles = []
    compatible = []
    for j, S in enumerate(splits):
        space = sum(1 << b for b, P in all_orders.items()
                    if all(truth.is_circular(s, P) for s in S))
        tree_spaces.append(space)
        if all(truth.is_circular(s, tuple(range(n))) for s in S):
            compatible.append(j)
            profile = 0
            for i, (x, y, z) in enumerate(triples):
                Q = (0, x, y, z)
                vals = {truth.topology_bit(Q, [a for a in Q if s & (1 << a)], 0)
                        for s in S if sum(bool(s & (1 << a)) for a in Q) == 2}
                assert len(vals) == 1
                profile |= vals.pop() << (3 * i)
            profiles.append(profile)
    distinct_profiles = {}
    for fam in range(1, 1 << len(profiles)):
        prof = 0
        members = []
        for j, P in enumerate(profiles):
            if fam & (1 << j):
                prof |= P
                members.append(compatible[j])
        distinct_profiles.setdefault(prof, members)
    checked = cyclic = 0
    for prof, members in distinct_profiles.items():
        spaces = [universe] * (1 << len(triples))
        for subset in range(1, len(spaces)):
            low = subset & -subset
            i = low.bit_length() - 1
            mask = (prof >> (3 * i)) & 7
            spaces[subset] = spaces[subset ^ low] & allowed[i][mask]
            U = spaces[subset]
            checked += 1
            assert U != 0  # the canonical circular order remains a witness
            if U & ~transitive:
                continue
            cyclic += 1
            if not any(U & ~T == 0 for T in tree_spaces):
                return {"status": "COUNTEREXAMPLE", "taxa": n,
                        "canonical_compatible_trees": len(compatible),
                        "distinct_full_anchored_profiles": len(distinct_profiles),
                        "partial_profiles_checked": checked,
                        "all_cyclic_checked": cyclic,
                        "family_tree_indices": members,
                        "family_graphs": [sorted(trees[j]) for j in members],
                        "family_splits": [sorted(splits[j]) for j in members],
                        "queried_triples": [triples[i] for i in range(len(triples)) if subset & (1 << i)],
                        "queried_masks": [(prof >> (3 * i)) & 7 for i in range(len(triples)) if subset & (1 << i)],
                        "accepted_orders": [P for b, P in all_orders.items() if U & (1 << b)],
                        "accepted_order_count": U.bit_count()}
    return {"status": "PASS", "taxa": n,
            "canonical_compatible_trees": len(compatible),
            "all_nonempty_canonical_families": (1 << len(compatible))-1,
            "distinct_full_anchored_profiles": len(distinct_profiles),
            "partial_profiles_checked": checked, "all_cyclic_checked": cyclic}


if __name__ == "__main__":
    records = []
    for n in (5, 6):
        record = run(n)
        records.append(record)
        print(json.dumps(record), flush=True)
        if record["status"] == "COUNTEREXAMPLE":
            break
    target = BASE / "partial-source-cyclic-controls.json"
    target.write_text(json.dumps({"records": records}, indent=2)+"\n")
