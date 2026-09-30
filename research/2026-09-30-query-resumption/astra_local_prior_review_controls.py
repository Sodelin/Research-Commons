"""Independent finite controls for Astra's local insertion claims.

Graph truth is imported from the earlier root graph-cut verifier (credited),
not from Astra's insertion/update implementation. Candidate-order truth uses
all graph splits and exhaustive circles. These are finite checks, not an
all-size proof or an admission census for source networks.
"""
from itertools import combinations, permutations
from pathlib import Path
import importlib.util
import json
import platform

BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "root_graph_truth", BASE.parent / "2026-09-30-root-exact-query" / "verify_candidate_order.py")
truth = importlib.util.module_from_spec(spec)
spec.loader.exec_module(truth)


def quartet(ss, q):
    bits = {truth.topology_bit(q, [x for x in q if s & (1 << x)], 0)
            for s in ss if sum(bool(s & (1 << x)) for x in q) == 2}
    assert len(bits) == 1
    return bits.pop()


def run(m):
    z = m
    C = tuple(range(m))
    old_full = (1 << m) - 1
    old_orders = [(0,) + P for P in permutations(range(1, m)) if P[0] < P[-1]]
    full_gaps = [C[:j+1] + (z,) + C[j+1:] for j in range(m)]
    qs = tuple(combinations(range(m+1), 4))
    qi = {q: i for i, q in enumerate(qs)}
    rows = []
    for G in truth.trees(m+1):
        ss = truth.graph_splits(G, m+1)
        old = set()
        for s in ss:
            side = s & old_full
            side = min(side, old_full ^ side)
            if min(side.bit_count(), m-side.bit_count()) >= 2:
                old.add(side)
        if not all(truth.is_circular(s, C) for s in old):
            continue
        old_space = sum(1 << i for i, P in enumerate(old_orders)
                        if all(truth.is_circular(s, P) for s in old))
        gaps = sum(1 << i for i, P in enumerate(full_gaps)
                   if all(truth.is_circular(s, P) for s in ss))
        assert gaps.bit_count() == 2
        profile = sum(quartet(ss, q) << (3*i) for i, q in enumerate(qs))
        rows.append((old_space, gaps, profile))
    if m <= 4:
        cases = range(1, 1 << len(rows))
        def members(case):
            return [i for i in range(len(rows)) if case & (1 << i)]
    else:
        cases = [(i,) for i in range(len(rows))] + list(combinations(range(len(rows)), 2))
        def members(case):
            return case
    counts = {"old_taxa": m, "compatible_full_trees": len(rows),
              "family_cases": 0, "old_rigid_cases": 0,
              "rigid_nonempty_extension_cases": 0, "arrow_checks": 0,
              "slot_certificate_checks": 0, "two_candidate_endpoint_checks": 0}
    canonical_space = next(1 << i for i, P in enumerate(old_orders) if P == C)
    for case in cases:
        old_space = (1 << len(old_orders)) - 1
        gaps = (1 << m) - 1
        profile = 0
        for i in members(case):
            S, J, Q = rows[i]
            old_space &= S
            gaps &= J
            profile |= Q
        counts["family_cases"] += 1
        assert gaps.bit_count() <= 2
        def supported(first_pair, *labels):
            q = tuple(sorted(labels))
            return bool(profile & (truth.topology_bit(q, first_pair, 0) << (3*qi[q])))
        for i in range(m):
            a, b, c = (i-1) % m, i, (i+1) % m
            q = tuple(sorted((z,a,b,c)))
            mask = (profile >> (3*qi[q])) & 7
            singleton = mask == truth.topology_bit(q, (z,b), 0)
            arrow_gaps = (1 << ((i-1) % m)) | (1 << i)
            assert singleton == (gaps == arrow_gaps), (m, case, i, gaps, mask)
            counts["arrow_checks"] += 1
        for i in range(m):
            b, c = i, (i+1) % m
            certificate = all(not supported((z,a), z,a,b,c)
                              for a in range(m) if a not in (b,c))
            assert certificate == bool(gaps & (1 << i)), (m, case, i, gaps)
            counts["slot_certificate_checks"] += 1
        if old_space == canonical_space:
            counts["old_rigid_cases"] += 1
            if gaps.bit_count() == 2:
                ij = [i for i in range(m) if gaps & (1 << i)]
                assert (ij[0]-ij[1]) % m in (1,m-1), (m, case, gaps)
            if gaps:
                counts["rigid_nonempty_extension_cases"] += 1
        if not gaps:
            continue
        for g,h in combinations(range(m), 2):
            candidates = (1 << g) | (1 << h)
            if gaps & ~candidates:
                continue
            kept = 0
            for i,j in ((g,h),(h,g)):
                b,c = i,(i+1)%m
                endpoints = {j,(j+1)%m} - {b,c}
                if all(not supported((z,a), z,a,b,c) for a in endpoints):
                    kept |= 1 << i
            assert kept == gaps, (m, case, gaps, candidates, kept)
            counts["two_candidate_endpoint_checks"] += 1
    return counts


if __name__ == "__main__":
    rows = []
    for m in range(3,8):
        result = run(m)
        rows.append(result)
        print(json.dumps(result), flush=True)
    target = BASE / "astra-local-prior-review-controls.json"
    target.write_text(json.dumps({"status":"PASS", "python":platform.python_version(),
        "scope":"all canonical-compatible tree families on 4/5 full taxa; singleton/pair families on 6/7/8 full taxa",
        "truth":"independent graph cuts and exhaustive circles; no Astra implementation imported",
        "rows":rows}, indent=2)+"\n")
