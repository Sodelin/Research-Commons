"""Partition one published centered curve without recomputing its means."""

import argparse
import csv
from collections import defaultdict
from decimal import Decimal, localcontext
from pathlib import Path

GRID = 1024
BLOCK_COUNTS = (32, 64, 128)


def read_prefix(path):
    curves = defaultdict(lambda: {"center32": {0: Decimal(0)}, "center64": {0: Decimal(0)}})
    with path.open(newline="") as stream:
        for row in csv.DictReader(stream):
            k, j = int(row["k"]), int(row["j"])
            for key in ("center32", "center64"):
                prefix = curves[k][key]
                if j in prefix:
                    raise ValueError(f"duplicate grid point at 2^{k}: {j}")
                prefix[j] = Decimal(row[key])
    return curves


def rows(curves):
    for k, data in sorted(curves.items()):
        for key, prefix in data.items():
            necessary = range(0, GRID+1, GRID//max(BLOCK_COUNTS))
            if any(j not in prefix for j in necessary):
                raise ValueError(f"incomplete window-boundary grid at 2^{k}")
            last_loss = Decimal(0)
            for count in BLOCK_COUNTS:
                stride = GRID // count
                sums = [prefix[j+stride] - prefix[j] for j in range(0, GRID, stride)]
                loss = sum((-v for v in sums if v < 0), Decimal(0))
                gain = sum((v for v in sums if v > 0), Decimal(0))
                assert gain-loss == prefix[GRID] and loss >= last_loss
                last_loss = loss
                norm = Decimal(1 << k)
                yield {
                    "k": k, "fixed_center_intervals": int(key.removeprefix("center")),
                    "windows": count, "negative_windows": sum(v < 0 for v in sums),
                    "positive_windows": sum(v > 0 for v in sums),
                    "loss_over_N": f"{loss/norm:.13g}", "gain_over_N": f"{gain/norm:.13g}",
                    "net_over_N": f"{(gain-loss)/norm:.13g}",
                    "doubled_loss_over_N": f"{2*loss/norm:.13g}",
                }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("grid", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    with localcontext() as ctx:
        ctx.prec = 85
        result = list(rows(read_prefix(args.grid)))
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(result[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(result)
