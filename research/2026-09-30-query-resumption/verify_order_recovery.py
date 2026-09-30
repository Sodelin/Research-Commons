"""Independent graph-cut controls for streamed signed-graph order and recovery."""
from __future__ import annotations
from datetime import datetime, timezone
from itertools import combinations, permutations
from math import comb
from pathlib import Path
import hashlib
import importlib.util
import json
import random
import sys
from order_recovery import learn_order, recover_all

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "2026-09-30-root-exact-query"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


graph_tools = load("independent_graph_cut_controls", OLD / "verify_candidate_order.py")


def canon(side, n):
    mask = sum(1 << x for x in side)
    return min(mask, ((1 << n) - 1) ^ mask)


def graph_oracle(n, support):
    def ask(q):
        a, b, c, d = q
        value = 0
        for s in support:
            pair = frozenset(x for x in q if s & (1 << x))
            if len(pair) != 2:
                continue
            for bit, partner in enumerate((b, c, d)):
                target = frozenset((a, partner))
                if pair == target or pair == frozenset(q) - target:
                    value |= 1 << bit
        return value
    return ask


def verify(n, support, anchor, expected_exists=None):
    oracle = graph_oracle(n, support)
    if expected_exists is None:
        expected_exists = any(all(graph_tools.is_circular(s, (anchor,) + tail) for s in support)
                              for tail in permutations(x for x in range(n) if x != anchor))
    try:
        result = recover_all(n, oracle, anchor)
    except ValueError:
        assert not expected_exists, (n, support, anchor)
        return None
    assert expected_exists
    assert all(graph_tools.is_circular(s, result.order_result.order) for s in support)
    found = {canon(side, n) for side in result.nontrivial_sides()}
    assert found == support, (n, anchor, found, support)
    assert result.order_result.anchored_calls == comb(n - 1, 3)
    assert 1 <= result.order_result.independent_orientations <= n - 2
    return result


def small():
    rows = []
    for n in (4, 5):
        split_sets = [graph_tools.graph_splits(g, n) for g in graph_tools.trees(n)]
        supports = [set() for _ in range(1 << len(split_sets))]
        accepted = rejected = anchors = 0
        for f in range(1, len(supports)):
            bit = f & -f
            supports[f] = supports[f ^ bit] | split_sets[bit.bit_length() - 1]
            result = verify(n, supports[f], 0)
            if result is None:
                rejected += 1
            else:
                accepted += 1
                # All anchors on a deterministic subset, including nonminimum anchors.
                if f < 100 or f % 257 == 0:
                    for anchor in range(1, n):
                        verify(n, supports[f], anchor, True)
                        anchors += 1
        rows.append(dict(n=n, tree_families=len(supports)-1, accepted=accepted,
                         correctly_rejected=rejected, additional_anchor_checks=anchors))
    return rows


def source_fixtures():
    # Use the previously recorded actual source-admission certificate without
    # rerunning a legacy script that overwrites another contributor's receipt.
    receipt = json.loads((OLD / "anchor-collision-receipt.json").read_text())
    assert receipt["status"] == "PASS"
    rows = []
    for fixture in receipt["fixtures"]:
        support = {canon((int(x[1:]) for x in side), 5) for side in fixture["displayed_splits"]
                   if 2 <= len(side) <= 3}
        outputs = [verify(5, support, anchor, True) for anchor in range(5)]
        rows.append(dict(name=fixture["name"], source_admission_reused=True,
                         nontrivial_splits=len(support), anchors=5,
                         calls_at_anchor_zero=outputs[0].total_calls,
                         recovered_sides_at_anchor_zero=sorted(map(sorted, outputs[0].nontrivial_sides()))))
    return rows


def random_ordered_tree(n, order, rng):
    # Build a binary tree on a shared plane tip order; independent edge-cut truth.
    adj = {x: set() for x in range(n)}
    serial = n
    def subtree(labels):
        nonlocal serial
        if len(labels) == 1:
            return labels[0]
        cut = rng.randrange(1, len(labels))
        v = serial
        serial += 1
        adj[v] = set()
        for child in (subtree(labels[:cut]), subtree(labels[cut:])):
            adj[v].add(child)
            adj[child].add(v)
        return v
    root = subtree(order[1:])
    adj[root].add(order[0])
    adj[order[0]].add(root)
    graph = frozenset(tuple(sorted((u, v))) for u in adj for v in adj[u])
    return graph_tools.graph_splits(graph, n)


def stress():
    rng = random.Random(202609301153)
    rows = []
    for n, count in ((8, 15), (16, 12), (32, 5), (64, 2)):
        order = list(range(n))
        rng.shuffle(order)
        support = set().union(*(random_ordered_tree(n, order, rng) for _ in range(count)))
        anchor = rng.randrange(n)
        result = verify(n, support, anchor, True)
        # Check reconstruction of the full quartet table on all small / sampled large queries.
        regenerated = graph_oracle(n, {canon(side, n) for side in result.nontrivial_sides()})
        queries = list(combinations(range(n), 4)) if n <= 16 else [tuple(sorted(rng.sample(range(n), 4))) for _ in range(1000)]
        source = graph_oracle(n, support)
        assert all(regenerated(q) == source(q) for q in queries)
        rows.append(dict(n=n, trees=count, k=len(support), anchor=anchor,
                         independent_orientations=result.order_result.independent_orientations,
                         anchored_calls=result.order_result.anchored_calls,
                         sparse_calls=result.sparse_calls, total_calls=result.total_calls,
                         full_support_reprojection_checks=len(queries)))
    return rows


def invalid():
    count = 0
    for value in (0, 8, -1, True, "1", 7):
        try:
            learn_order(4, lambda q: value)
        except ValueError:
            count += 1
        else:
            raise AssertionError(("invalid mask accepted", value))
    return count


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not run with -O")
    report = dict(status="PASS", created_utc=datetime.now(timezone.utc).isoformat(),
                  small=small(), source_fixtures=source_fixtures(), stress=stress(),
                  invalid_controls=invalid(),
                  sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (HERE / "order_recovery.py", Path(__file__))},
                  limits="Finite graph-cut checks; all-size conclusion relies on the attributed proof. Source certificates reused and labeled. Large stress families share an order but need not be one admitted network. No biological data or optimal adaptive closure.")
    (HERE / "order-recovery-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
