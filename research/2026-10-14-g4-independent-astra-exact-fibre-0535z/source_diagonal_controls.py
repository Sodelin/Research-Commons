"""Exact source-formula controls for the all-arity tangent proof.

Requires SymPy. These checks do not prove all arities, solve an exact fibre,
verify a full source compiler, or invoke Lean/Rust. The all-arity proof is in
DIAGONAL-TANGENT-COUNTERCONTROL.md.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("Install SymPy to run these exact symbolic controls.") from exc


def lam(n: int) -> int:
    if n < 0:
        raise ValueError("Root count must be nonnegative")
    return n * (n - 1) // 2


def main() -> None:
    a, x, y, g, r, t = sp.symbols("a x y g r t")
    at = {a: sp.Rational(3, 4), x: sp.Rational(1, 2),
          y: sp.Rational(1, 2), g: sp.Rational(2, 3), r: sp.Rational(1, 2)}
    checks: dict[str, bool] = {}
    derivatives: dict[str, str] = {}
    for n in range(2, 14):
        b = sum(sp.binomial(n, k) * g**k * (1-g)**(n-k)
                * x**lam(k) * y**lam(n-k) for k in range(n+1))
        ward = (sp.Rational(3, 2) * sp.diff(b, x)
                + sp.Rational(1, 2) * sp.diff(b, y) - lam(n)*b).subs(at)
        value = sp.cancel(ward)
        derivatives[str(n)] = str(value)
        checks[f"source_diagonal_tangent_n{n}"] = value == 0

    b2 = (a*r) * (g**2*x + (1-g)**2*y + 2*g*(1-g))
    curve = {a: sp.Rational(3,4)*(1-t), x: sp.Rational(1,2)+sp.Rational(3,2)*t,
             y: sp.Rational(1,2)+sp.Rational(1,2)*t, g: sp.Rational(2,3), r: sp.Rational(1,2)}
    pair_curve = sp.expand(b2.subs(curve))
    checks["pair_curve_is_not_exact_collision"] = pair_curve == sp.Rational(13,48)*(1-t**2).expand()

    V = lambda z: (2-3*z+z**3)/6
    cB = 2*(g**2*(1-g)**2*(1-x)*(1-y)
            -g**3*(1-g)*V(x)-g*(1-g)**3*V(y))
    cK, hK = a**6*r*cB, a**6*(1-r)*cB
    D = lambda f: -a*sp.diff(f,a)+sp.Rational(3,2)*sp.diff(f,x)+sp.Rational(1,2)*sp.diff(f,y)
    values = {
        "cB": sp.cancel(cB.subs(at)),
        "cx": sp.cancel(sp.diff(cB,x).subs(at)),
        "cy": sp.cancel(sp.diff(cB,y).subs(at)),
        "cK": sp.cancel(cK.subs(at)),
        "hK": sp.cancel(hK.subs(at)),
        "DcK": sp.cancel(D(cK).subs(at)),
        "DhK": sp.cancel(D(hK).subs(at)),
    }
    expected = {"cB": sp.Rational(-1,972), "cx": sp.Rational(2,81),
                "cy": sp.Rational(-5,162), "cK": sp.Rational(-3,32768),
                "hK": sp.Rational(-3,32768), "DcK": sp.Rational(81,32768),
                "DhK": sp.Rational(81,32768)}
    for name, value in values.items():
        checks[f"cap_four_{name}"] = value == expected[name]
    receipt = {
        "scope": "Actual source diagonal and cap-four formula controls, not complete source equality",
        "sympy_version": sp.__version__,
        "check_count": len(checks), "all_passed": all(checks.values()), "checks": checks,
        "tested_arity_range": [2,13], "diagonal_residuals": derivatives,
        "pair_curve": str(pair_curve),
        "cap_four_values": {k: str(v) for k,v in values.items()},
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "limitations": ["Finite arithmetic checks do not prove all n", "No exact G4 rival", "No Lean or Rust execution", "No independent review"],
    }
    print(json.dumps(receipt, indent=2, sort_keys=True))
    if not receipt["all_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
