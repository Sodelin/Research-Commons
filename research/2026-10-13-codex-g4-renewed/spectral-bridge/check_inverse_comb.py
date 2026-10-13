#!/usr/bin/env python3
"""Exact rational diagnostic for one signed inverse; no G4 forcing claim."""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial, prod
from pathlib import Path
from hashlib import sha256
import json


def lam(n):
    return comb(n, 2)


def H(n):
    return prod(lam(j) for j in range(2, n + 1))


@lru_cache(None)
def death(n, k):
    """Kingman n-to-k probability at survival q=1/2."""
    return sum((F(prod(lam(j) for j in range(k + 1, n + 1)),
                  prod(lam(j) - lam(i) for j in range(k, n + 1) if j != i))
                * F(1, 2) ** lam(i) for i in range(k, n + 1)), F(0))


def transfer(n, k):
    """Inherited exact comb-cut transfer for q=q'=g=1/2."""
    return sum((F(2, 2 ** n) * comb(k - 1, j)
                * F(H(n) * H(j + 1), H(k) * H(n - (k - 1 - j)))
                * death(n - (k - 1 - j), j + 1)
                * F(1, 2) ** lam(k - 1 - j)
                for j in range(k)), F(0))


def main():
    w = [F(0)]
    rows = []
    for n in range(1, 11):
        a = [F(0)] + [transfer(n, k) for k in range(1, n + 1)]
        assert a[n] > 0 and all(x >= 0 for x in a)
        assert a[n] == sum((F(comb(n, j), 2 ** n)
                           * F(1, 2) ** (lam(j) + lam(n - j))
                           for j in range(n + 1)), F(0))
        w.append((1 - sum(a[k] * w[k] for k in range(1, n))) / a[n])
        assert sum(a[k] * w[k] for k in range(1, n + 1)) == 1
        if n >= 2:
            orbit = w[n] * F(2 ** (n - 2), factorial(n - 1))
            rows.append({"n": n, "normalized_comb": str(w[n]),
                         "signed_comb_orbit_mass": str(orbit)})
    assert w[4] == F(89, 81)
    excess = w[10] * F(2 ** 8, factorial(9)) - 1
    assert excess > 0
    return {
        "status": "PASS",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "cell": {"q_left": "1/2", "q_right": "1/2", "inheritance": "1/2"},
        "checks": rows,
        "cap_10_comb_orbit_mass_excess_over_one": str(excess),
        "limits": [
            "The inverse is signed and is not an admitted rival.",
            "The endpoint completion block is independent of downstream ordinary duration.",
            "This exact finite obstruction does not establish an asymptotic spectral rate.",
            "No G4 finite certificate, fixed-target rival construction, or Lean proof is claimed."
        ]
    }


if __name__ == "__main__":
    print(json.dumps(main(), sort_keys=True, indent=2))
