#!/usr/bin/env python3
"""Run the pinned Goldbach triple-complement balance diagnostic."""

import argparse
from collections import defaultdict
from decimal import Decimal, ROUND_CEILING, localcontext
from functools import cache
from itertools import combinations
import json
from math import fsum, gcd, isclose, isqrt, log, prod
from pathlib import Path
import subprocess
import tempfile


TARGETS = [2**20, 2**22, 2**24, 3 * 2**24, 2**26, 3 * 2**26, 2**28]
PARAMETERS = (
    "N", "H", "cutoff", "Y", "Y0", "Z", "below_high", "below_low",
    "mark_low", "mark_high", "kmin", "kmax", "min_high", "min_low",
    "ell_low", "ell_high", "d_small", "d_min",
)
COUNT_FIELDS = ("products", "pairs", "terms", "zero_brackets",
                "complete_products", "four_factor_products")
METRICS = COUNT_FIELDS + (
    "raw", "after_divisors",
    "after_products", "final", "n_prefix_low", "n_prefix_high",
    "after_ell_first", "ell_prefix_low", "ell_prefix_high",
    "zero_bracket_raw", "complete_raw", "four_factor_raw",
    "low_order_after_products", "mixed_order_drop",
)


def floor_root(value, power):
    """Integer value of floor(value ** (1/power))."""
    lo = 0
    hi = 1 << ((value.bit_length() + power - 1) // power)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid**power <= value:
            lo = mid
        else:
            hi = mid
    return lo


def decimal_parameters(n, precision):
    with localcontext() as ctx:
        ctx.prec = precision
        L = Decimal(n).ln()
        log_L = L.ln()
        exp_cut = lambda exponent: (L ** Decimal(exponent)).exp()
        mark = exp_cut("0.75")
        ceil = lambda x: int(x.to_integral_value(rounding=ROUND_CEILING))
        return {
            "N": n,
            "H": isqrt(n),
            "cutoff": floor_root(n**21, 40),
            "Y": int(exp_cut("0.005")),
            "Y0": int(exp_cut("0.10")),
            "Z": int(exp_cut("0.99")),
            "below_high": int(exp_cut("0.9896")),
            "below_low": int(exp_cut("0.95")),
            "mark_low": int(mark),
            "mark_high": int(2 * mark),
            "kmin": int(log_L / 4) + 1,
            "kmax": ceil(8 * log_L) - 1,
            "min_high": int(Decimal("0.0153") * log_L) + 1,
            "min_low": int(Decimal("0.0029") * log_L) + 1,
            "ell_low": floor_root(n, 4),
            "ell_high": floor_root(n, 3),
            "d_small": int(exp_cut("0.90")),
            "d_min": ceil(Decimal("0.4475") * log_L),
        }


def run(binary, n):
    params = decimal_parameters(n, 80)
    assert params == decimal_parameters(n, 120), f"unstable cutoff at N={n}"
    args = [str(params[key]) for key in PARAMETERS]
    result = subprocess.run([str(binary), *args], check=True, text=True, capture_output=True)
    rows = []
    for line in result.stdout.splitlines():
        scenario, sector, *rest = line.split("\t")
        k = len(COUNT_FIELDS)
        values = [int(value) for value in rest[:k]] + [float(value) for value in rest[k:]]
        stats = dict(zip(METRICS, values))
        checkpoints = values[len(METRICS):]
        assert len(checkpoints) == 64
        assert isclose(checkpoints[-1], stats["final"], rel_tol=1e-11, abs_tol=1e-8)
        scale = 1 + stats["raw"]
        tol = 1e-12 * scale
        assert stats["raw"] + tol >= stats["after_divisors"]
        assert stats["after_divisors"] + tol >= stats["after_products"]
        assert stats["after_products"] + tol >= abs(stats["final"])
        assert stats["raw"] + tol >= stats["after_ell_first"]
        assert stats["after_ell_first"] + tol >= abs(stats["final"])
        if scenario == "exact_triple_center":
            assert stats["complete_products"] <= stats["zero_brackets"]
            assert stats["zero_bracket_raw"] + tol >= stats["complete_raw"]
        rows.append({
            "scenario": scenario,
            "sector": sector,
            **stats,
            "prefix_at_jN_over_16": checkpoints[3::4],
        })
    assert len(rows) == 12
    for row in rows:
        if row["scenario"] != "exact_triple_center":
            continue
        high = next(s["after_products"] for s in rows
                    if s["scenario"] == "triple_divisors_only" and s["sector"] == row["sector"])
        expected_drop = row["low_order_after_products"] + high - row["after_products"]
        assert isclose(row["mixed_order_drop"], expected_drop, rel_tol=1e-11, abs_tol=1e-8)
    return {"target": n, "parameters": params, "balances": rows}


def trial_factorizer(limit):
    primes = []
    for p in range(2, limit + 1):
        if all(p % r for r in primes if r <= isqrt(p)):
            primes.append(p)

    @cache
    def factors(value):
        found = []
        for p in primes:
            if p * p > value:
                break
            if value % p == 0:
                value //= p
                if value % p == 0:
                    return None
                found.append(p)
        if value > 1:
            found.append(value)
        return tuple(found)

    return factors


def product_passes(m_primes, par, mark_limit=1):
    k = sum(par["Y0"] < p <= par["Z"] for p in m_primes)
    marks = sum(par["mark_low"] < p <= par["mark_high"] for p in m_primes)
    return (par["kmin"] <= k <= par["kmax"] and marks <= mark_limit
            and sum(p <= par["below_high"] for p in m_primes) >= par["min_high"]
            and (len(m_primes) % 2 == 0
                 or sum(p <= par["below_low"] for p in m_primes) >= par["min_low"]))


def paired_weight(q, h, ell, mu_q, mu_h, mu_d):
    w1 = -mu_h * mu_d * log(h) * log(ell)
    w2 = -mu_q * mu_d * log(q) * log(ell)
    return w1 + w2


def independent_check(run_result):
    """Verify the exact-center sums by trial division and the original weights."""
    par = run_result["parameters"]
    target, H = par["N"], par["H"]
    factors = trial_factorizer(H)
    by_n = defaultdict(list)
    raw, after_divisors = [], []
    count_pairs = count_terms = 0
    for q in range(H // 2 + 1, H + 1):
        if gcd(q, target) != 1 or factors(q) is None:
            continue
        for h in range(q + 1, H + 1):
            if gcd(h, target * q) != 1 or factors(h) is None:
                continue
            m = q * h
            m_primes = factors(q) + factors(h)
            if not product_passes(m_primes, par):
                continue
            n = target - m
            n_primes = factors(n)
            if not n_primes or len(n_primes) < 3 or n_primes[0] <= par["Y"]:
                continue
            values = []
            has_triple = False
            for k in range(1, len(n_primes) + 1):
                for subset in combinations(n_primes, k):
                    ell = prod(subset)
                    if n // ell <= par["cutoff"]:
                        continue
                    has_triple |= k >= 3
                    mu_d = (-1)**(len(n_primes) - k)
                    values.append(paired_weight(q, h, ell, (-1)**len(factors(q)),
                                                (-1)**len(factors(h)), mu_d))
            if has_triple:
                count_pairs += 1
                count_terms += len(values)
                raw.append(fsum(map(abs, values)))
                bracket = fsum(values)
                after_divisors.append(abs(bracket))
                by_n[n].append(bracket)

    ordered = [fsum(by_n[n]) for n in sorted(by_n)]
    expected = next(x for x in run_result["balances"]
                    if x["scenario"] == "exact_triple_center" and x["sector"] == "all")
    assert (len(by_n), count_pairs, count_terms) == (
        expected["products"], expected["pairs"], expected["terms"])
    for key, value in {
        "raw": fsum(raw),
        "after_divisors": fsum(after_divisors),
        "after_products": fsum(map(abs, ordered)),
        "final": fsum(ordered),
    }.items():
        assert isclose(expected[key], value, rel_tol=1e-11, abs_tol=1e-8), (key, value)
    return {"target": target, "method": "independent trial division and unswapped weights",
            "compared": ["products", "pairs", "terms", "raw", "after_divisors",
                         "after_products", "final"]}


def geometry_check(run_result):
    """Enumerate the witness projection starting from ell and a residue class for h."""
    par = run_result["parameters"]
    target, H = par["N"], par["H"]
    factors = trial_factorizer(H)
    p0 = next(p for p in range(3, H + 1, 2)
              if target % p and factors(p) == (p,))
    hlo, hhi = isqrt(9 * target) // 4 + 1, isqrt(49 * target) // 8
    by_pair = defaultdict(list)
    for ell in range(par["ell_low"] + 1, par["ell_high"] + 1):
        pe = factors(ell)
        if not pe or len(pe) < 3 or pe[0] <= par["Y"] or gcd(ell, target) != 1:
            continue
        for q in range(H // 2 + 1, isqrt(25 * target) // 8 + 1):
            pq = factors(q)
            if q % p0 or not pq or gcd(q, ell * target) != 1:
                continue
            residue = target * pow(q, -1, ell) % ell
            for h in range(hlo + (residue - hlo) % ell, hhi + 1, ell):
                ph = factors(h)
                if not ph or gcd(h, target * q) != 1 or not product_passes(pq + ph, par, 0):
                    continue
                d, rem = divmod(target - q * h, ell)
                assert rem == 0
                if d <= par["cutoff"] or gcd(d, ell) != 1:
                    continue
                pd = factors(d)
                if not pd or pd[0] <= par["Y"]:
                    continue
                if sum(p <= par["d_small"] for p in pd) < par["d_min"]:
                    continue
                by_pair[(q, h)].append(paired_weight(q, h, ell, (-1)**len(pq),
                                                      (-1)**len(ph), (-1)**len(pd)))
    by_n = defaultdict(list)
    for (q, h), values in by_pair.items():
        by_n[target - q * h].append(fsum(values))
    expected = next(x for x in run_result["balances"]
                    if x["scenario"] == "witness_geometry" and x["sector"] == "all")
    assert (len(by_n), len(by_pair), sum(map(len, by_pair.values()))) == (
        expected["products"], expected["pairs"], expected["terms"])
    for key, value in {
        "raw": fsum(abs(x) for values in by_pair.values() for x in values),
        "after_divisors": fsum(abs(fsum(values)) for values in by_pair.values()),
        "after_products": fsum(abs(fsum(values)) for values in by_n.values()),
        "final": fsum(fsum(values) for values in by_n.values()),
    }.items():
        assert isclose(expected[key], value, rel_tol=1e-11, abs_tol=1e-8), (key, value)
    return {"target": target, "method": "independent divisor-first progression",
            "compared": ["products", "pairs", "terms", "raw", "after_divisors",
                         "after_products", "final"]}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("targets", nargs="*", type=int, default=TARGETS)
    cli.add_argument("--output", type=Path)
    args = cli.parse_args()
    source = Path(__file__).with_name("goldbach-triple-balance.cpp")
    with tempfile.TemporaryDirectory(prefix="goldbach-balance-") as tmp:
        binary = Path(tmp) / "balance"
        subprocess.run(["g++", "-std=c++20", "-O3", "-Wall", "-Wextra", str(source),
                        "-o", str(binary)], check=True)
        runs = []
        for n in args.targets:
            if n % 2 or not 2**16 <= n <= 2**30:
                raise ValueError("supply even targets between 2^16 and 2^30")
            runs.append(run(binary, n))
        checks = [independent_check(r) for r in runs if r["target"] == 2**20]
        checks += [geometry_check(r) for r in runs if r["target"] == 2**28]
    data = {"cutoff_exponent": "21/40 in N", "cross_checks": checks, "runs": runs}
    report = json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n"
    if args.output:
        args.output.write_text(report)
    else:
        print(report, end="")


if __name__ == "__main__":
    main()
