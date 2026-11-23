"""Validate the centered grid and render the six fixed-target prefix curves."""

import csv
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.lines import Line2D
from matplotlib.patches import Patch

HERE = Path(__file__).resolve().parent
BASELINE = HERE.parent / "2026-11-23-codex-signed-endpoint-balance-2336z" / "balance.csv"
GRID = 1024
TARGETS = range(39, 45)
COLORS = {"raw": "#666e7a", "center32": "#194f9e", "center64": "#087b68"}


def read_csv(path):
    with path.open(newline="") as stream:
        return list(csv.DictReader(stream))


def near(a, b):
    return math.isclose(a, b, rel_tol=5e-13, abs_tol=2e-7)


def values(rows, key):
    return np.fromiter((float(row[key]) for row in rows), dtype=float)


def describe(rows, old):
    k = int(old["k"])
    if [int(row["j"]) for row in rows] != list(range(1, GRID+1)):
        raise ValueError(f"Missing cells at 2^{k}")
    assert int(old["candidate_triples"]) == sum(int(row["triples"]) for row in rows)
    assert int(old["endpoints"]) == sum(int(row["endpoints"]) for row in rows)
    t = 1 << k
    assert all(int(row["n"]) == int(row["j"])*(t//GRID) for row in rows)
    g = values(rows, "g_cell")
    a = values(rows, "a_cell")
    base_abs = float(old["endpoint_abs"])
    assert near(base_abs, math.fsum(values(rows, "raw_abs")))
    raw_increments = values(rows, "raw_cell")
    assert near(float(old["signed"]), math.fsum(raw_increments))
    curve = {"raw": np.r_[0.0, values(rows, "raw_prefix")]}
    ends = np.concatenate(([0.0], values(rows, "raw_prefix")))
    assert np.allclose(ends[1:] - ends[:-1], raw_increments, atol=2e-7, rtol=5e-12)
    envelopes = {}
    metrics = {
        "k": k, "E": base_abs, "raw_final": float(old["signed"]),
        "raw_exact_peak": float(old["max_abs_prefix"]),
    }
    for bins in (32, 64):
        run = GRID // bins
        mean_columns = values(rows, f"g_mean{bins}")
        for i in range(0, GRID, run):
            true_mean = math.fsum(g[i:i+run]) / (t//bins)
            assert np.allclose(mean_columns[i:i+run], true_mean, atol=1e-16, rtol=5e-13)
        corrected = np.r_[0.0, values(rows, f"center{bins}")]
        assert np.allclose(corrected[1:] - corrected[:-1],
                           raw_increments - mean_columns*a, atol=2e-7, rtol=5e-12)
        variation = values(rows, f"variation{bins}")
        assert np.allclose(variation, values(rows, "raw_abs") +
                           abs(mean_columns)*values(rows, "a_ordered_abs"),
                           atol=2e-7, rtol=5e-12)
        assert np.all(abs(corrected[1:]-corrected[:-1]) <= variation+2e-7)
        center = (corrected[1:]+corrected[:-1])/2
        lo, hi = center-variation/2, center+variation/2
        curve[f"center{bins}"] = corrected
        envelopes[bins] = lo, hi
        extremum = int(np.argmax(abs(corrected)))
        metrics.update({
            f"end{bins}": corrected[-1], f"observed{bins}": abs(corrected[extremum]),
            f"peak_n_over_N{bins}": extremum/GRID,
            f"envelope{bins}": max(abs(lo).max(), abs(hi).max()),
            f"low{bins}": corrected.min(), f"high{bins}": corrected.max(),
        })
    return base_abs, curve, envelopes, metrics


def write_data(groups):
    with (HERE/"prefix-curves.csv").open("w", newline="") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(["k", "grid", "raw_pct_E", "center32_pct_E", "center64_pct_E",
                         "cell_low32_pct_E", "cell_high32_pct_E"])
        for k, (base_abs, curves, envelopes, _) in groups.items():
            scale = 100/base_abs if base_abs else 0
            lo, hi = envelopes[32]
            active = np.flatnonzero(np.r_[False, (lo != hi)])
            indices = (
                sorted({0, GRID, *range(int(active[0])-1, int(active[-1])+1)})
                if len(active) else (0, GRID)
            )
            for j in indices:
                heights = [scale*curves[key][j] for key in ("raw", "center32", "center64")]
                cell_envelope = [scale*lo[j-1], scale*hi[j-1]] if j else [0, 0]
                writer.writerow([k, j, *[f"{x:.12g}" for x in (*heights, *cell_envelope)]])
    with (HERE/"prefix-summary.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(groups[39][3]), lineterminator="\n")
        writer.writeheader()
        for _, _, _, metrics in groups.values():
            writer.writerow({key: f"{value:.14g}" for key, value in metrics.items()})


def draw(groups):
    matplotlib.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                                "svg.fonttype": "none", "svg.hashsalt": "goldbach-centered-prefix",
                                "axes.labelcolor": "#263447", "text.color": "#172537"})
    fig, axs = plt.subplots(3, 2, sharex=True, figsize=(11.8, 8.4),
                           gridspec_kw={"height_ratios": [0.52, 1, 1]})
    xs = np.linspace(0, 1, GRID+1)
    for ax, (k, (mass, curves, envelopes, _)) in zip(axs.flat, groups.items()):
        ax.set_title(rf"$N=2^{{{k}}}$", loc="left", weight="bold", fontsize=13, pad=6)
        ax.axhline(0, color="#8a99ad", linewidth=0.65, zorder=1)
        ax.set_xlim(0.40, 0.759)
        ax.set_xticks(np.arange(0.4, 0.751, 0.05))
        ax.grid(axis="x", color="#dbe2eb", linewidth=.7)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)
        for spine in ("left", "bottom"):
            ax.spines[spine].set_color("#aebccc")
        if not mass:
            ax.set_ylim(-0.6, 0.6)
            ax.set_yticks([0])
            ax.text(.415, .22, "Empty reflected support", fontsize=9, color=COLORS["raw"])
            ax.plot([.40, .759], [0, 0], color=COLORS["center32"], lw=1.6)
            continue
        scale = 100/mass
        lo, hi = envelopes[32]
        nonzero = np.flatnonzero(lo != hi)
        a, b = int(nonzero[0]), int(nonzero[-1])+1
        ax.fill_between(xs[a:b+1], np.r_[lo[a:b], lo[b-1]]*scale,
                        np.r_[hi[a:b], hi[b-1]]*scale, step="post",
                        color="#b4d0f4", alpha=.44, linewidth=0, zorder=0)
        ax.grid(axis="y", color="#e5ecf3", linewidth=.6)
        sample_indices = np.r_[0, np.arange(a, b+1), GRID]
        x = xs[sample_indices]
        ax.plot(x, curves["raw"][sample_indices]*scale, color=COLORS["raw"], ls=":", lw=1.25)
        ax.plot(x, curves["center32"][sample_indices]*scale, color=COLORS["center32"], lw=1.7)
        ax.plot(x, curves["center64"][sample_indices]*scale, color=COLORS["center64"], ls="--", lw=1.0)
        ax.scatter(.75, curves["center32"][-1]*scale, color=COLORS["center32"], s=16, zorder=4)
        ax.autoscale(axis="y", tight=False)

    fig.text(.06, .962, "Goldbach signed remainder in endpoint order", fontsize=20,
             weight="bold", va="top")
    fig.text(.06, .918, r"Raw even-$qh$ row · exact reflected cutoffs · one sample every $N/1024$",
             fontsize=11, color="#465870", va="top")
    fig.legend(handles=[
        Line2D([0], [0], color=COLORS["center32"], lw=1.8, label="Centered in 32 intervals"),
        Line2D([0], [0], color=COLORS["center64"], ls="--", lw=1.1, label="Centered in 64 intervals"),
        Line2D([0], [0], color=COLORS["raw"], ls=":", lw=1.4, label="Uncentered"),
        Patch(facecolor="#d6e5fa", edgecolor="none", label="32-interval between-sample envelope"),
    ], loc="upper left", bbox_to_anchor=(.057, .895), ncol=2, frameon=False,
       columnspacing=2.35, fontsize=9.7)
    fig.supxlabel(r"Endpoint fraction $n/N$", fontsize=11, y=.064)
    fig.supylabel(r"Running weight (% of endpoint absolute mass $E$)", fontsize=11, x=.021)
    fig.text(.08, .027, r"Panels use separate vertical scales. Prefixes are flat outside the plotted interval.",
             fontsize=9, color="#465870")
    fig.subplots_adjust(left=.092, right=.982, bottom=.119, top=.788, wspace=.19, hspace=.37)
    metadata = {"Title": "Goldbach signed remainder in endpoint order", "Date": None}
    fig.savefig(HERE/"centered-running-sum.svg", metadata=metadata)
    fig.savefig(HERE/"centered-running-sum.png", dpi=170)
    plt.close(fig)


if __name__ == "__main__":
    grid_data = read_csv(HERE/"grid-full.csv")
    old = {int(r["k"]): r for r in read_csv(BASELINE)
           if r["qh_parity"] == "1" and r["mask"] == "raw"}
    groups = {k: describe([r for r in grid_data if int(r["k"]) == k], old[k]) for k in TARGETS}
    write_data(groups)
    draw(groups)
