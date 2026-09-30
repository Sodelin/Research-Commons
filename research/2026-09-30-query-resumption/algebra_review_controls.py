"""Independent exact controls for all dense anchored masks at n=4 and n=5.

This does not import the production learner. Algebra is checked by exhausting
all comparison assignments; circle truth is checked by split alternations in
all permutations. No source-network realization is asserted for arbitrary masks.
"""

from itertools import combinations, permutations, product
from pathlib import Path
import json
import math


def run(n):
    other = tuple(range(1, n))
    pair_list = tuple(combinations(other, 2))
    pair_index = {pair: i for i, pair in enumerate(pair_list)}
    triples = tuple(combinations(other, 3))

    def ordered_value(bits, a, b):
        return ((bits >> pair_index[tuple(sorted((a, b)))]) & 1) ^ (a > b)

    algebra_allowed = []
    circle_allowed = []
    for a, b, c in triples:
        # topology bits: ra|bc, rb|ac, rc|ab
        topologies = (((0, a), (b, c)), ((0, b), (a, c)), ((0, c), (a, b)))
        triple_algebra = []
        triple_circle = []
        for mask in range(1, 8):
            accepted_bits = 0
            for bits in range(1 << len(pair_list)):
                ok = True
                for k, z, x, y in ((0, a, b, c), (1, b, a, c), (2, c, a, b)):
                    if mask & (1 << k):
                        ok &= ordered_value(bits, z, x) == ordered_value(bits, z, y)
                if ok:
                    accepted_bits |= 1 << bits
            triple_algebra.append(accepted_bits)

            accepted_orders = 0
            for order in permutations(other):
                rank = {x: i for i, x in enumerate(order)}
                bits = sum((rank[x] < rank[y]) << i for i, (x, y) in enumerate(pair_list))
                cycle = (0,) + tuple(x for x in order if x in (a, b, c))
                ok = True
                for k, (side, _) in enumerate(topologies):
                    if mask & (1 << k):
                        crossings = sum((cycle[i] in side) != (cycle[(i+1) % 4] in side)
                                        for i in range(4))
                        ok &= crossings == 2
                if ok:
                    accepted_orders |= 1 << bits
            triple_circle.append(accepted_orders)
        algebra_allowed.append(triple_algebra)
        circle_allowed.append(triple_circle)

    tables = 0
    inconsistent = 0
    directed_orders = 0
    dimension_counts = {}
    full_bitset = (1 << (1 << len(pair_list))) - 1
    for masks in product(range(1, 8), repeat=len(triples)):
        algebra = full_bitset
        circles = full_bitset
        for j, mask in enumerate(masks):
            algebra &= algebra_allowed[j][mask-1]
            circles &= circle_allowed[j][mask-1]
        assert algebra == circles, (n, masks, algebra, circles)
        tables += 1
        count = algebra.bit_count()
        if count == 0:
            inconsistent += 1
        else:
            assert count & (count-1) == 0
            dimension = int(math.log2(count))
            assert 1 <= dimension <= n-2
            dimension_counts[str(dimension)] = dimension_counts.get(str(dimension), 0)+1
            directed_orders += count
    return {"taxa": n, "dense_anchored_tables": tables,
            "inconsistent_tables": inconsistent,
            "consistent_tables": tables-inconsistent,
            "accepted_directed_orders_summed": directed_orders,
            "affine_dimension_counts": dimension_counts,
            "status": "PASS"}


if __name__ == "__main__":
    records = [run(4), run(5)]
    report = {"status": "PASS", "scope": "All nonempty support masks on every anchored triple, n=4,5",
              "truth": "direct split-alternation enumeration in directed circles",
              "implementation_imported": False, "records": records}
    target = Path(__file__).with_name("algebra-review-controls.json")
    target.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))
