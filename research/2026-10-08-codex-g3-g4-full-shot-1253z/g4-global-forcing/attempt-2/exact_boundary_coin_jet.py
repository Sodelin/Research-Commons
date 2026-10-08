"""Exact truncated-ring derivative of one actual boundary-coin family.

Uses captured, hash-authenticated inherited EPPF bytes read-only.  It is not
a source search, approximate root solver, compiler, or full-return checker.
Output must be a new file; old evidence is never overwritten.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import argparse
import datetime
import hashlib
import json

ORDER = 4
PROVIDER = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py"
PROVIDER_SHA = "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"


@dataclass(frozen=True)
class Jet:
    coefficients: tuple

    @staticmethod
    def scalar(value):
        return Jet((F(value),) + (F(0),) * ORDER)

    @staticmethod
    def variable():
        return Jet((F(0), F(1)) + (F(0),) * (ORDER - 1))

    @staticmethod
    def cast(value):
        return value if isinstance(value, Jet) else Jet.scalar(value)

    def __add__(self, other):
        other = self.cast(other)
        return Jet(tuple(a + b for a, b in zip(self.coefficients, other.coefficients)))

    __radd__ = __add__

    def __neg__(self):
        return Jet(tuple(-a for a in self.coefficients))

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return Jet(tuple(sum((self.coefficients[j] * other.coefficients[k - j]
                              for j in range(k + 1)), F(0))
                         for k in range(ORDER + 1)))

    __rmul__ = __mul__

    def inverse(self):
        a = self.coefficients
        if not a[0]:
            raise ZeroDivisionError("formal inverse has zero constant term")
        b = [1 / a[0]]
        for k in range(1, ORDER + 1):
            b.append(-sum((a[j] * b[k - j] for j in range(1, k + 1)), F(0)) / a[0])
        return Jet(tuple(b))

    def __truediv__(self, other):
        return self * self.cast(other).inverse()

    def __rtruediv__(self, other):
        return self.cast(other) * self.inverse()

    def __pow__(self, exponent):
        if exponent < 0:
            return self.inverse() ** (-exponent)
        result, base = self.scalar(1), self
        while exponent:
            if exponent & 1:
                result *= base
            base *= base
            exponent //= 2
        return result

    def log(self):
        if self.coefficients[0] != 1:
            raise ValueError("this log implementation requires constant term one")
        z = self - 1
        return sum((F((-1) ** (k + 1), k) * z ** k
                    for k in range(1, ORDER + 1)), self.scalar(0))


def wire(jet):
    return [str(c) for c in Jet.cast(jet).coefficients]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("refusing to overwrite existing output")
    provider_path = args.root / PROVIDER
    captured = provider_path.read_bytes()
    actual_sha = hashlib.sha256(captured).hexdigest()
    if actual_sha != PROVIDER_SHA:
        raise SystemExit("source provider hash mismatch")
    provider = {"__name__": "captured_readonly_eppf", "__file__": str(provider_path)}
    exec(compile(captured, str(provider_path), "exec"), provider)

    t = Jet.variable()
    x, g = Jet.scalar(F(1, 2)), t
    q = 1 - g
    y = 1 - t / (2 * q)
    u, v = g * (1 - x), q * (1 - y)
    assert u == v == t / 2
    b = {n: provider["diag"](n, x, y, g) for n in (2, 3, 4, 6, 7, 9)}
    assert b[2] == 1 - t / 2
    assert b[3] - b[2] ** 3 == -(t / 2) ** 3
    f, h, e = provider["scalars"](x, y, g)
    X = b[2] ** -36 * f
    T = b[2] ** -15 * h
    U = b[2] ** -21 * (-h + 2 * e)
    transverse_T = T - F(5, 3) * X
    transverse_U = U + F(5, 3) * X
    D3 = b[3].log() - 3 * b[2].log()
    D4 = b[4].log() - 4 * b[3].log() + 6 * b[2].log()

    # Exact low-arity normalization and current-root projectivity controls.
    controls = 0
    for n in range(1, 6):
        total = Jet.scalar(0)
        for sizes in provider["integer_partitions"](n):
            p = provider["bare_partition"](sizes, x, y, g)
            total += provider["partition_multiplicity"](sizes) * p
            if n < 5:
                extension = provider["bare_partition"](sizes + (1,), x, y, g)
                for j in range(len(sizes)):
                    larger = sizes[:j] + (sizes[j] + 1,) + sizes[j + 1:]
                    extension += provider["bare_partition"](larger, x, y, g)
                assert extension == p
                controls += 1
        assert total == Jet.scalar(1)
        controls += 1

    report = {
        "schema": "actual-boundary-coin-exact-jet-v1",
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "provider": {"path": PROVIDER, "sha256": actual_sha},
        "producer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "arithmetic": "exact Fraction ring Q[t]/(t^5)",
        "source": {"x": "1/2", "g": "t", "y": "1-t/(2(1-t))",
                   "strict_domain": "0<t<2/3", "loss_balance": "u=v=d=t/2",
                   "mode": "INDEPENDENT current roots", "tuple_shared_all_arities": True},
        "coefficients_order_0_through_4": {
            **{"b" + str(n): wire(z) for n, z in b.items()},
            "d9": wire(f), "d6": wire(h), "e": wire(e),
            "pair_normalized_X": wire(X), "pair_normalized_T": wire(T),
            "pair_normalized_U": wire(U),
            "T_minus_5_over_3_X": wire(transverse_T),
            "U_plus_5_over_3_X": wire(transverse_U),
            "D3": wire(D3), "D4": wire(D4)},
        "exact_controls": controls + 2,
        "claim_limits": "One actual strict family jet. No full word, ordinary return, constrained-fibre sign or G4 resolution. Normalization uses a formal inverse only."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"output": str(args.output), "sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
                      "exact_controls": controls + 2,
                      "T_minus_5_over_3_X": wire(transverse_T),
                      "U_plus_5_over_3_X": wire(transverse_U),
                      "D3": wire(D3), "D4": wire(D4)}))


if __name__ == "__main__":
    main()
