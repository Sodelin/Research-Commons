#!/usr/bin/env python3
"""Prepare independently rounded cutoffs and invoke the central C++ enumerator."""

from argparse import ArgumentParser
from decimal import Decimal, localcontext, ROUND_CEILING, ROUND_FLOOR
from pathlib import Path
import subprocess


def exact_power_floor(exponent, numerator, denominator):
    bound = 1 << (numerator * exponent)
    lo, hi = 1, 1 << exponent
    while lo + 1 < hi:
        midpoint = (lo + hi) // 2
        if midpoint**denominator <= bound:
            lo = midpoint
        else:
            hi = midpoint
    return lo


def real_thresholds(exponent, precision):
    with localcontext() as context:
        context.prec = precision
        log_n = exponent * Decimal(2).ln()
        log_l = log_n.ln()

        def below(value):
            return int(value.to_integral_value(rounding=ROUND_FLOOR))

        def exp_l_to(power):
            return (log_n ** Decimal(power)).exp()

        mark = exp_l_to(".75")
        return (
            below(exp_l_to(".005")),
            below((log_n * log_l.ln().sqrt() / log_l).exp()),
            below(exp_l_to(".10")),
            below(exp_l_to(".99")),
            below(mark),
            below(2 * mark),
            below(exp_l_to(".9896")),
            below(exp_l_to(".95")),
            below(Decimal(".25") * log_l) + 1,
            int((8 * log_l).to_integral_value(rounding=ROUND_CEILING)) - 1,
            below(Decimal(".0153") * log_l) + 1,
            below(Decimal(".0029") * log_l) + 1,
        )


def threshold_line(exponent):
    floor_p = exact_power_floor(exponent, 21, 40)
    slice_min = exact_power_floor(exponent, 19, 120)
    if slice_min**120 < 1 << (19 * exponent):
        slice_min += 1
    phases = real_thresholds(exponent, 100)
    if phases != real_thresholds(exponent, 160):
        raise ArithmeticError(f"rounded decimal cutoffs disagree at k={exponent}")
    return " ".join(map(str, (exponent, floor_p, slice_min, *phases)))


def main():
    parser = ArgumentParser()
    parser.add_argument("exponents", nargs="+", type=int)
    parser.add_argument("--thresholds-only", action="store_true")
    parser.add_argument(
        "--binary", type=Path,
        default=Path(__file__).with_name("goldbach-center-evaluator.bin"),
    )
    args = parser.parse_args()
    data = "".join(threshold_line(k) + "\n" for k in args.exponents)
    if args.thresholds_only:
        print(data, end="")
    else:
        subprocess.run([str(args.binary)], input=data, encoding="ascii", check=True)


if __name__ == "__main__":
    main()
