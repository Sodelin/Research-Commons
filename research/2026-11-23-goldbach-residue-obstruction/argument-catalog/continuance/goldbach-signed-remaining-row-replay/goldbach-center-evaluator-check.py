#!/usr/bin/env python3
"""Independently check the k=20 rows by trial division and direct d-divisors."""

from collections import defaultdict
import importlib.util
import json
import math
from pathlib import Path


def small_primes(n):
    output = []
    for m in range(2, n + 1):
        if all(m % p for p in output if p * p <= m):
            output.append(m)
    return output


def factor(n, primes):
    answer = []
    for p in primes:
        if p * p > n:
            break
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            answer.append((p, exponent))
    if n > 1:
        answer.append((n, 1))
    return answer


def mobius(factors):
    return 0 if any(a > 1 for _, a in factors) else (-1) ** len(factors)


def approved(primes, parity, data):
    (_, _, middle_lo, middle_hi, mark_lo, mark_hi,
     cutoff_9896, cutoff_95, min_middle, max_middle, min_9896, min_95) = data
    return (
        min_middle <= sum(middle_lo < p <= middle_hi for p in primes) <= max_middle
        and sum(mark_lo < p <= mark_hi for p in primes) <= 1
        and sum(p <= cutoff_9896 for p in primes) >= min_9896
        and (parity == "even" or sum(p <= cutoff_95 for p in primes) >= min_95)
    )


def compare(row, observed):
    weights = [x[0] for x in observed]
    assert row["placements"] == len(weights)
    assert row["positive"] == sum(sign > 0 for _, sign in observed)
    assert row["negative"] == sum(sign < 0 for _, sign in observed)
    assert math.isclose(row["signed"], math.fsum(weights), abs_tol=2e-8, rel_tol=2e-12)
    assert math.isclose(row["absolute"], math.fsum(map(abs, weights)), abs_tol=2e-8, rel_tol=2e-12)


def main():
    base = Path(__file__).parent
    spec = importlib.util.spec_from_file_location("rounded_thresholds", base / "goldbach-center-evaluator-run.py")
    thresholds = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(thresholds)
    row = next(
        obj for line in (base / "goldbach-center-evaluator-results.jsonl").read_text().splitlines()
        if (obj := json.loads(line))["k"] == 20
    )
    target, cutoff = row["N"], row["P_floor"]
    data = thresholds.real_thresholds(row["k"], 85)
    primes = small_primes(math.isqrt(target))
    options = range(math.isqrt(target) // 2 + 1, math.isqrt(target) + 1, 2)
    observed = defaultdict(list)
    actual = defaultdict(list)
    for q in options:
        fq = factor(q, primes)
        mq = mobius(fq)
        if not mq:
            continue
        for h in options:
            if q >= h or math.gcd(q, h) != 1:
                continue
            fh = factor(h, primes)
            mh = mobius(fh)
            if not mh:
                continue
            parity = "odd" if mq != mh else "even"
            is_marked = approved([p for p, _ in fq + fh], parity, data)
            n = target - q * h
            fn = factor(n, primes)
            weight = mh * math.log(h) + mq * math.log(q)
            if len(fn) == 1:
                term = -weight * math.log(fn[0][0])
                actual["raw", parity].append((term, -mh))
                if is_marked:
                    actual["marked", parity].append((term, -mh))
            if len(fn) % 2 or mobius(fn) == 0 or len(fn) < 2:
                continue
            n_primes = [p for p, _ in fn]
            if n_primes[0] <= row["Y0_floor"]:
                continue
            category = "semiprime" if len(fn) == 2 else (
                "higher_045_slice" if parity == "odd" and n_primes[0] >= row["slice_min_prime"]
                else "higher_remainder"
            )

            # Direct original d-divisor terms, with exact products for zero and sign.
            divisors = [(1, 1)]
            for p in n_primes:
                divisors += [(d * p, -mu_d) for d, mu_d in divisors]
            numerator = denominator = 1
            for d, mu_d in divisors:
                if d <= cutoff:
                    continue
                if mu_d == -1:
                    numerator *= n // d
                else:
                    denominator *= n // d
            bracket = math.log(numerator) - math.log(denominator)
            sign = mh * ((numerator > denominator) - (numerator < denominator))
            for rough in ("Y0", "Z1"):
                if rough == "Z1" and n_primes[0] <= row["Z1_floor"]:
                    continue
                observed[rough, "raw", parity, category].append((weight * bracket, sign))
                if is_marked:
                    observed[rough, "marked", parity, category].append((weight * bracket, sign))

    for rough, by_mask in row["rows"].items():
        for mask, by_parity in by_mask.items():
            for parity, by_category in by_parity.items():
                for category, record in by_category.items():
                    compare(record, observed[rough, mask, parity, category])
    for mask in ("raw", "marked"):
        for parity in ("even", "odd"):
            compare(row[mask + "_actual_A11"][parity], actual[mask, parity])
    print("k=20 verified: 24 endpoint rows, 4 actual rows, and exact positive/negative counts")


if __name__ == "__main__":
    main()
