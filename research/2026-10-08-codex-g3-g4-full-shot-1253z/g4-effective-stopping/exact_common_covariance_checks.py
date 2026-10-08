#!/usr/bin/env python3
"""Exact bounded checks of an actual private COMMON source covariance law."""

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import platform

import sympy as sp


def pair_count(n):
    return n*(n-1)//2


def no_merge(diagonal, cross, allocation):
    result = sp.Integer(1)
    for a, count in zip(diagonal, allocation):
        result *= a**pair_count(count)
    for (i, j), z in cross.items():
        result *= z**(allocation[i]*allocation[j])
    return result


def marginal_exposer(support):
    x = sp.Symbol("x")
    powers = [0, 1, 3, 6, 10]
    coeff = sp.symbols("c0:4")
    polynomial = sum(c*x**p for c, p in zip(coeff, powers))+x**powers[-1]
    equations = []
    for atom in support:
        equations += [polynomial.subs(x, atom), sp.diff(polynomial, x).subs(x, atom)]
    solution = sp.solve(equations, coeff)
    polynomial = sp.expand(polynomial.subs(solution))
    assert all(polynomial.subs(x, atom) == 0 and sp.diff(polynomial, x).subs(x, atom) == 0 for atom in support)
    signs = [sp.sign(sp.Poly(polynomial, x).coeff_monomial(x**p)) for p in powers]
    assert all(sign != 0 for sign in signs)
    sign_changes = sum(signs[i] != signs[i+1] for i in range(4))
    assert sign_changes == 4
    # Descartes gives <=4 positive roots, already supplied by these two doubles.
    assert sp.Poly(polynomial, x).LC() == 1
    assert polynomial.subs(x, 0) > 0
    return {"polynomial": str(polynomial), "support": [str(v) for v in support],
            "positive_roots_counting_multiplicity": 4, "coefficient_sign_changes": sign_changes,
            "nonnegative_on_positive_axis_by_double_roots_and_descartes": True}


def main(output):
    # Actual four-taxon tree ((A,B),(C,D)), one COMMON bigon on the AB bridge.
    # AB bridge is E(2/3) B_common(1/2,3/4,1/3) E(3/4).
    # CD ordinary bridge survival 1/2; pendant survivals 2/3,3/4,4/5,5/6.
    weights = [sp.Rational(1, 3), sp.Rational(2, 3)]
    ab = [sp.Rational(1, 4), sp.Rational(3, 8)]
    pendants = [sp.Rational(2, 3), sp.Rational(3, 4), sp.Rational(4, 5), sp.Rational(5, 6)]
    atoms = []
    for bridge in ab:
        diagonal = [bridge*pendants[0], bridge*pendants[1], sp.Rational(1, 2)*pendants[2], sp.Rational(1, 2)*pendants[3]]
        cross = {(0, 1): bridge, (2, 3): sp.Rational(1, 2), (0, 2): sp.Integer(1),
                 (0, 3): sp.Integer(1), (1, 2): sp.Integer(1), (1, 3): sp.Integer(1)}
        atoms.append((diagonal, cross))

    def actual_diagonal(allocation):
        return sum(weight*no_merge(*atom, allocation) for weight, atom in zip(weights, atoms))

    source_checks = 0
    for allocation in itertools.product(range(3), repeat=4):
        source_product = sp.Integer(0)
        for weight, bridge in zip(weights, ab):
            conditional = bridge**pair_count(allocation[0]+allocation[1])
            conditional *= sp.Rational(1, 2)**pair_count(allocation[2]+allocation[3])
            conditional *= sp.prod(p**pair_count(n) for p, n in zip(pendants, allocation))
            source_product += weight*conditional
        assert source_product == actual_diagonal(allocation)
        source_checks += 1

    a_grid = [atom[0][0] for atom in atoms]
    b_grid = [atom[0][1] for atom in atoms]
    joint = list(itertools.product(a_grid, b_grid))
    interpolations = []
    for exponent in [12, 24, 36]:
        matrix = sp.Matrix([[a**pair_count(c)*b**pair_count(exponent//c) for a, b in joint] for c in range(1, 5)])
        assert matrix.det() != 0
        response = sp.Matrix([actual_diagonal([c, exponent//c, 0, 0]) for c in range(1, 5)])
        recovered = matrix.inv()*response
        expected = sp.Matrix([sum(w*z**exponent for w, z, atom in zip(weights, ab, atoms)
                                  if atom[0][0] == a and atom[0][1] == b) for a, b in joint])
        assert recovered == expected
        assert sum(v == 0 for v in recovered) == 2
        interpolations.append({"cross_power": exponent, "matrix_rank": 4,
                               "conditional_moments_recovered_exactly": 4, "zero_mass_grid_pairs": 2})

    exposers = [marginal_exposer(a_grid), marginal_exposer(b_grid)]
    v = [1, 3, 1, 1]
    matrix = sp.Matrix([[no_merge(*atom, [k*n for n in v]) for atom in atoms] for k in [1, 2]])
    assert matrix.det() != 0
    assert matrix.inv()*sp.Matrix([actual_diagonal([k*n for n in v]) for k in [1, 2]]) == sp.Matrix(weights)

    receipt = {"status": "PASS", "scope": "Actual private four-taxon COMMON source; diagonal covariance identity, finite-grid cross interpolation, sparse marginal certificates and joint atom weights",
               "python": platform.python_version(), "sympy": sp.__version__,
               "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "actual_source": {"tree": "((A,B),(C,D))", "eligible_ab_bridge": "E(2/3) B_common(1/2,3/4,1/3) E(3/4)",
                                 "cd_bridge": "E(1/2)", "pendant_survivals": list(map(str, pendants)), "all_physical_parameters_strict": True},
               "source_covariance_product_identities": source_checks, "grid_interpolation": interpolations,
               "sparse_marginal_exposers": exposers, "joint_atom_weights_recovered": list(map(str, weights)),
               "new_general_determinant_asymptotics": "Hand argument only; finite fixtures do not certify the universal lemma",
               "root_extension_public_type_admission": "Unresolved original-contract gate; not tested or assumed by this arithmetic",
               "lean_ci_qe_source_catalogue_or_parameter_search_executed": False}
    output.write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "source_identities": source_checks, "interpolation_cases": len(interpolations), "output": str(output)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    main(parser.parse_args().output)
