"""Generate floor-certified exact branch thresholds for the endpoint run."""

import math
import sys

from mpmath import iv


def whole_floor(value):
    lower, upper = int(value.a), int(value.b)
    if lower != upper:
        raise ArithmeticError(f"uncertified floor: {value}")
    return lower


def rational_power_floor(k, numerator, denominator):
    bound = 1 << (k * numerator)
    low, high = 0, 1 << (k * numerator // denominator + 1)
    while high - low > 1:
        mid = (low + high) // 2
        if mid**denominator <= bound:
            low = mid
        else:
            high = mid
    return low


def certified_row(k):
    if not 39 <= k <= 44:
        raise ValueError("this endpoint-balance replay covers exponents 39 through 44")
    n = 1 << k
    L = k * iv.ln(2)
    logL = iv.ln(L)
    z = iv.exp(L * iv.sqrt(iv.ln(logL)) / logL)
    floor = whole_floor
    expL = lambda s: iv.exp(L ** iv.mpf(s))
    rough = floor(z)
    assert floor(expL(".005")) < rough
    q_min = math.isqrt(n // 4) + 1
    q_min += q_min % 2 == 0
    max_n = n - q_min * (q_min + 2)
    upper_count = 8 * logL
    assert upper_count.a > floor(upper_count)
    return (
        k, n, math.isqrt(n // 4) + 1, math.isqrt(n), max_n, rough,
        rational_power_floor(k, 1, 40), rational_power_floor(k, 21, 40),
        rational_power_floor(k, 19, 40), rational_power_floor(k, 799, 1520),
        floor(expL(".10")), floor(expL(".99")), floor(expL(".75")),
        floor(2 * expL(".75")), floor(expL(".9896")), floor(expL(".95")),
        floor(logL / 4) + 1, floor(upper_count),
        floor(iv.mpf(".0153") * logL) + 1, floor(iv.mpf(".0029") * logL) + 1,
    )


if __name__ == "__main__":
    iv.dps = 85
    for item in sys.argv[1:]:
        print(*certified_row(int(item)))
