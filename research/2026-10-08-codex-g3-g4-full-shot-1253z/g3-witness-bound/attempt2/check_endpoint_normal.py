"""Exact symbolic audit of the mathematical COMMON endpoint/normal fixture.

This executes no inherited source provider, native genealogy engine, QE or Lean.
The rational log-word derivative formulas are stated in the accompanying proof.
"""
import json
import math
from functools import reduce
from pathlib import Path

import sympy as s


def rational(value):
    value = s.Rational(value)
    return {"numerator": int(value.p), "denominator": int(value.q)}


def signs_and_variations(chain, point):
    signs = [int(s.sign(poly.eval(point))) for poly in chain]
    nonzero = [v for v in signs if v]
    variations = sum(a != b for a, b in zip(nonzero, nonzero[1:]))
    return {"signs": signs, "variations": variations}


def audit():
    q = s.Symbol("q")
    lam6 = [1, 3, 6, 10, 15, 21]
    lam7 = lam6 + [28]
    pairs = [(s.Rational(1, 2), s.Rational(1, 2)),
             (s.Rational(1, 2), s.Rational(1, 3))]

    def row(lam):
        columns = [s.Integer(lam)]
        for p, ratio in pairs:
            f = 1 - p + p * ratio**lam
            columns.extend([(1 - ratio**lam) / f,
                            -p * lam * ratio**(lam - 1) / f])
        return columns

    j6 = s.Matrix([row(lam) for lam in lam6])
    j7 = s.Matrix([row(lam) for lam in lam7])
    assert j6.rank() == j7.rank() == 5
    normal = j6.T.nullspace()[0]
    denominator = s.ilcm(*[v.q for v in normal])
    normal = [int(v * denominator) for v in normal]
    divisor = reduce(math.gcd, normal)
    normal = [v // divisor for v in normal]
    if sum(normal) < 0:
        normal = [-v for v in normal]
    assert j6.T * s.Matrix(normal) == s.zeros(5, 1)
    assert j7.T * s.Matrix(normal + [0]) == s.zeros(5, 1)
    assert sum(c * lam for c, lam in zip(normal, lam6)) == 0

    f = s.Poly(sum(c * (1 - q**lam)
                   for c, lam in zip(normal, lam6)), q)
    g = f.exquo(s.Poly((1 - q)**2, q))
    assert g.eval(0) > 0 and g.eval(1) > 0
    chain = [s.Poly(v, q) for v in s.sturm(g.as_expr(), q)]
    left = signs_and_variations(chain, 0)
    right = signs_and_variations(chain, 1)
    assert left["variations"] == right["variations"]
    assert g.count_roots(0, 1) == 0
    assert sum(c * lam**2 for c, lam in zip(normal, lam6)) == -2 * g.eval(1)

    exponents = [0] + lam7
    atoms = [s.Integer(1), s.Rational(1, 2),
             s.Rational(1, 3), s.Rational(1, 6)]
    exposure_matrix = s.Matrix(
        [[atom**exp for exp in exponents] for atom in atoms] +
        [[exp * atom**(exp - 1) if exp else 0 for exp in exponents]
         for atom in atoms[1:]])
    assert exposure_matrix.rank() == 7
    coefficients = exposure_matrix.nullspace()[0]
    coefficients /= coefficients[0]
    exposing = s.Poly(sum(coefficients[i] * q**exp
                          for i, exp in enumerate(exponents)), q)
    assert exposing.eval(0) == 1
    assert all(coefficients)
    for atom in atoms:
        assert exposing.eval(atom) == 0
    for atom in atoms[1:]:
        assert exposing.diff().eval(atom) == 0
        assert exposing.diff().diff().eval(atom) != 0
    assert exposing.diff().eval(1) < 0
    assert exposing.count_roots(0, 1) == 4
    weight_matrix = s.Matrix([[atom**exp for atom in atoms]
                              for exp in exponents[:4]])
    assert weight_matrix.det() != 0
    moments = [sum(atom**lam for atom in atoms) / 4 for lam in lam7]

    return {
        "scope": "Exact symbolic source-formula audit, not native source execution or formal verification.",
        "sympy_version": s.__version__,
        "exponents": lam7,
        "physical_factor_points": [[rational(p), rational(r)] for p, r in pairs],
        "log_jacobian6": [[rational(v) for v in j6.row(i)] for i in range(6)],
        "log_jacobian_rank_cap7": 5,
        "log_jacobian_rank_cap8": 5,
        "invertible_first5_minor": rational(j6[:5, :].det()),
        "ordinary_neutral_integer_normal": normal + [0],
        "rare_polynomial": {"coefficient_by_degree": [int(v) for v in reversed(f.all_coeffs())]},
        "positive_quotient_G": {
            "coefficient_by_degree": [int(v) for v in reversed(g.all_coeffs())],
            "G_at_0": int(g.eval(0)), "G_at_1": int(g.eval(1)),
            "sturm_at_0": left, "sturm_at_1": right,
            "roots_closed_0_1": 0,
            "conclusion": "G strictly positive on [0,1]; F=(1-q)^2 G.",
        },
        "endpoint_exposure": {
            "exponents": exponents,
            "coefficients": [rational(v) for v in coefficients],
            "matrix_rank": 7,
            "constant_coefficient": 1,
            "positive_root_multiplicities": [1, 2, 2, 2],
            "derivative_at_1": rational(exposing.diff().eval(1)),
            "weight_matrix_determinant": rational(weight_matrix.det()),
            "endpoint_moments": [rational(v) for v in moments],
            "sign_proof": "Eight nonzero sparse terms permit at most seven positive roots counted with multiplicity; all seven are present. P(0)=1 fixes the nonnegative sign on [0,1].",
        },
    }


def main(output_path):
    output_path = Path(output_path)
    output_path.write_text(json.dumps(audit(), indent=2) + "\n")
