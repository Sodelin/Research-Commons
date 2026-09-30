"""Independent graph-cut verification of the Gallai adaptive query prototype."""
from __future__ import annotations
from datetime import datetime, timezone
from itertools import combinations, permutations
from pathlib import Path
import hashlib
import json
import random
from adaptive_recovery import recover_all, interval_hierarchy
from verify_order_recovery import graph_tools, graph_oracle, canon, random_ordered_tree, OLD

HERE = Path(__file__).resolve().parent


def verify(n, support, anchor, expected_exists):
    source = graph_oracle(n, support)
    actual_calls = []
    def ask(q):
        actual_calls.append(q)
        return source(q)
    try:
        result = recover_all(n, ask, anchor)
    except ValueError:
        assert not expected_exists, (n, support, anchor)
        return None
    assert expected_exists
    assert all(graph_tools.is_circular(s, result.learned.order) for s in support)
    assert {canon(side, n) for side in result.nontrivial_sides()} == support
    assert len(actual_calls) == result.total_calls
    assert result.learned.oracle_calls <= result.learned.query_bound
    return result


def small():
    rows = []
    for n in (4, 5):
        split_sets = [graph_tools.graph_splits(g, n) for g in graph_tools.trees(n)]
        circular_orders = [(0,) + p for p in permutations(range(1, n))]
        family_supports = [set() for _ in range(1 << len(split_sets))]
        accepted = rejected = max_calls = max_repairs = anchor_checks = 0
        for f in range(1, len(family_supports)):
            bit = f & -f
            support = family_supports[f] = family_supports[f ^ bit] | split_sets[bit.bit_length() - 1]
            exists = any(all(graph_tools.is_circular(s, order) for s in support) for order in circular_orders)
            result = verify(n, support, 0, exists)
            if result is None:
                rejected += 1
            else:
                accepted += 1
                max_calls = max(max_calls, result.total_calls)
                max_repairs = max(max_repairs, result.learned.repairs)
                if f < 100 or f % 257 == 0:
                    for anchor in range(1, n):
                        verify(n, support, anchor, True)
                        anchor_checks += 1
        rows.append(dict(n=n, families=len(family_supports)-1, accepted=accepted,
                         correctly_rejected=rejected, additional_anchor_checks=anchor_checks,
                         maximum_total_calls=max_calls, maximum_repairs=max_repairs))
    return rows


def source_fixtures():
    receipt = json.loads((OLD / "anchor-collision-receipt.json").read_text())
    assert receipt["status"] == "PASS"
    rows = []
    for fixture in receipt["fixtures"]:
        support = {canon((int(x[1:]) for x in side), 5) for side in fixture["displayed_splits"]
                   if 2 <= len(side) <= 3}
        for anchor in range(5):
            result = verify(5, support, anchor, True)
            rows.append(dict(name=fixture["name"], anchor=anchor,
                             source_admission_reused=True, split_count=len(support),
                             order_calls=result.learned.oracle_calls,
                             sparse_calls=result.sparse_calls, total_calls=result.total_calls))
    return rows


def forbidden_tree_shortcut():
    # This all-transitive comparison space has no containing binary tree;
    # the Gallai hierarchy must still handle its two-color prime quotient.
    group = {(1, 3), (2, 3), (2, 4)}
    colors = {p: int(p in group) for p in combinations(range(1, 5), 2)}
    weights, nodes = interval_hierarchy((1, 2, 3, 4), colors)
    assert sum(weights.values()) <= 12
    assert any(len(children) == 4 and len(palette) == 2 for labels, children, palette in nodes)
    orders = []
    for mask in range(4):
        for p in permutations(range(1, 5)):
            pos = {x: i for i, x in enumerate(p)}
            if all((pos[x] < pos[y]) == bool(1 ^ ((mask >> c) & 1)) for (x, y), c in colors.items()):
                orders.append(p)
    assert set(orders) == {(1,2,3,4),(3,1,4,2),(2,4,1,3),(4,3,2,1)}
    return dict(status="PASS", orders=orders, hierarchy_nodes=len(nodes), weights=weights,
                forbidden_generic_containing_tree_shortcut_not_used=True)


def stress():
    rng = random.Random(202609301217)
    rows = []
    for n in (6, 8, 12, 16, 24, 32, 48, 64):
        repeats = 20 if n <= 16 else 5 if n <= 32 else 2
        scenarios = []
        for case in range(repeats):
            order = list(range(n))
            rng.shuffle(order)
            tree_count = rng.choice((1, 2, 3, 5))
            support = set().union(*(random_ordered_tree(n, order, rng) for _ in range(tree_count)))
            result = verify(n, support, rng.randrange(n), True)
            r = result.learned
            scenarios.append(dict(trees=tree_count, k=len(support), cycle_calls=r.cycle_phase_calls,
                                  order_calls=r.oracle_calls, sparse_calls=result.sparse_calls,
                                  total_calls=result.total_calls, initial_colors=r.initial_colors,
                                  hierarchy_weight=r.hierarchy_weight, repairs=r.repairs,
                                  distinct_adjacencies=r.distinct_adjacencies,
                                  flipped_weight=r.flipped_weight, proved_budget=r.query_bound))
        rows.append(dict(n=n, scenarios=scenarios))
    return rows


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with -O")
    record = dict(status="PASS", created_utc=datetime.now(timezone.utc).isoformat(),
                  small=small(), source_fixtures=source_fixtures(),
                  forbidden_tree_shortcut=forbidden_tree_shortcut(), stress=stress(),
                  sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (HERE/"adaptive_recovery.py",Path(__file__))},
                  limits="Exact finite graph-cut controls, not an all-size proof, source census, biological validation, timing benchmark or optimal adaptive closure.")
    (HERE/"adaptive-recovery-verification.json").write_text(json.dumps(record,indent=2)+"\n")
    print(json.dumps({k:v for k,v in record.items() if k != "stress"},indent=2))
    print("Stress rows:", [(row["n"], len(row["scenarios"]),
                            max(s["order_calls"] for s in row["scenarios"])) for row in record["stress"]])
