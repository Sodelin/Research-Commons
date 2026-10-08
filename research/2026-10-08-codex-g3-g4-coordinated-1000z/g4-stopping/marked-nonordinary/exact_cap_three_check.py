#!/usr/bin/env python3
"""Bounded exact full-cap-three check; no source catalogue or parameter search."""

import argparse
import hashlib
import json
import platform
from pathlib import Path

import sympy as sp


STATES = ["1|2|3", "(12)|3", "(13)|2", "(23)|1", "((12)3)", "((13)2)", "((23)1)"]


def full_kernel(no_merge, fixed_pair, fixed_tree, pair_survival):
    """Opaque current-root forest action on all seven labelled three-leaf states."""
    matrix = sp.zeros(7)
    matrix[0, 0] = no_merge
    for index in range(3):
        matrix[0, 1 + index] = fixed_pair
        matrix[0, 4 + index] = fixed_tree
        matrix[1 + index, 1 + index] = pair_survival
        matrix[1 + index, 4 + index] = 1 - pair_survival
        matrix[4 + index, 4 + index] = 1
    return matrix


def ordinary(survival):
    # Kingman: each specified initial pair has rate one; three then two roots.
    fixed_pair = (survival - survival**3) / 2
    fixed_tree = (1 - 3 * survival / 2 + survival**3 / 2) / 3
    return full_kernel(survival**3, fixed_pair, fixed_tree, survival)


def bare(x, y, g):
    # All-three routes and the six two-plus-one assignments are kept separately.
    no_merge = g**3 * x**3 + (1-g)**3 * y**3 + 3*g**2*(1-g)*x + 3*g*(1-g)**2*y
    fixed_pair = g**3 * (x-x**3)/2 + (1-g)**3 * (y-y**3)/2
    fixed_pair += g**2*(1-g)*(1-x) + g*(1-g)**2*(1-y)
    fixed_tree = g**3 * (1-3*x/2+x**3/2)/3 + (1-g)**3 * (1-3*y/2+y**3/2)/3
    pair_survival = g**2*x + (1-g)**2*y + 2*g*(1-g)
    return full_kernel(no_merge, fixed_pair, fixed_tree, pair_survival)


def zeros(matrix):
    return all(sp.simplify(value) == 0 for value in matrix)


def main(output):
    x, y, g = sp.symbols("x y g")
    raw = bare(x, y, g)
    assert all(sp.simplify(sum(raw.row(i))-1) == 0 for i in range(7))
    assert zeros(raw.subs({x: 1, y: 1}) - sp.eye(7))

    s, q, h, a = sp.symbols("s q h a")
    fair = bare(s-h, s+h, sp.Rational(1, 2))
    word = ordinary(a) * fair * ordinary(a)
    field = sp.QQ.frac_field(s, q)
    relations = sp.groebner([
        h**2-(1-s)**3/(6*s),
        a**2-2*q/(1+s),
    ], h, a, domain=field)
    # This checks every entry, including the action on previously merged subtrees.
    residues = [relations.reduce(sp.expand(value))[1] for value in word-ordinary(q)]
    assert all(value == 0 for value in residues)

    fixtures = []
    for target, mean in [(sp.Rational(1, 2), sp.Rational(3, 4)),
                         (sp.Rational(3, 4), sp.Rational(7, 8)),
                         (sp.Rational(1, 10), sp.Rational(1, 2))]:
        beta = (1+mean)/2
        arm_difference = sp.sqrt((1-mean)**3/(6*mean))
        pad = sp.sqrt(target/beta)
        arms = [mean-arm_difference, mean+arm_difference]
        assert all(bool(0 < value < 1) for value in arms+[pad])
        actual = ordinary(pad) * bare(*arms, sp.Rational(1, 2)) * ordinary(pad)
        assert zeros(actual - ordinary(target))
        assert all(bool(sp.simplify(value) >= 0) for value in actual)
        assert all(sp.simplify(sum(actual.row(i))-1) == 0 for i in range(7))
        fixtures.append({"q": str(target), "s": str(mean), "h": str(arm_difference),
                         "x": str(arms[0]), "y": str(arms[1]), "ordinary_pad": str(pad),
                         "physical_strict": True, "full_matrix_entries_equal": 49,
                         "rows_stochastic": 7})

    r = sp.symbols("r")
    equal_arm = bare(r, r, sp.Rational(1, 2))
    beta = (1+r)/2
    equal_arm_defect = sp.factor(equal_arm[0, 0]/beta**3 - 1)
    assert sp.simplify(equal_arm_defect + ((1-r)/(1+r))**3) == 0

    receipt = {
        "status": "PASS", "scope": "Exact actual full three-root forest matrix and marked one-cell ordinary-target witnesses; no larger cap or catalogue",
        "python": platform.python_version(), "sympy": sp.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "states": STATES, "chronology": "ordinary(a) * actual bare(s-h,s+h,1/2) * ordinary(a)",
        "generic_bare_row_mass_identities": 7,
        "generic_bare_identity_boundary_entries": 49,
        "symbolic_word_full_matrix_zero_residues": len(residues),
        "symbolic_relations": ["h^2=(1-s)^3/(6s)", "a^2=2q/(1+s)"],
        "positive_source_fixtures": fixtures,
        "equal_arm_negative_control": str(equal_arm_defect),
        "all_copy_inequivalence": "Inherited strict-word chain-count theorem, not tested by this finite matrix",
        "lean_ci_qe_parameter_search_executed": False,
    }
    output.write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "symbolic_full_matrix_entries": 49, "strict_fixtures": len(fixtures), "output": str(output)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    main(parser.parse_args().output)
