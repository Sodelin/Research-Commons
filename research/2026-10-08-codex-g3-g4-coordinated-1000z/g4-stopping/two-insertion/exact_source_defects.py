"""Bounded exact current-root EPPF checks, not a Lean/compiler/QE driver.

Each output block is routed wholly into one physical bare-cell arm. The
ordinary arm EPPF comes from its exact root-count death chain. This evaluates
fixed rational fixtures through nine roots; it does not search target fibres.
"""

from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json
import sys


def lam(n):
    return n * (n - 1) // 2


@lru_cache(None)
def root_count(n, r, x):
    if n == 0:
        return F(int(r == 0))
    coefficient = prod(lam(j) for j in range(r + 1, n + 1))
    return coefficient * sum(
        (x ** lam(j) / prod(lam(k) - lam(j) for k in range(r, n + 1) if k != j)
         for j in range(r, n + 1)), F(0)
    )


@lru_cache(None)
def ordinary_partition(sizes, x):
    if not sizes:
        return F(1)
    n, r = sum(sizes), len(sizes)
    conditional = F(factorial(r) * prod(factorial(s) for s in sizes),
                    factorial(n) * comb(n - 1, r - 1))
    return root_count(n, r, x) * conditional


@lru_cache(None)
def bare_partition(sizes, x, y, g):
    answer = F(0)
    for mask in product((0, 1), repeat=len(sizes)):
        left = tuple(s for s, arm in zip(sizes, mask) if arm)
        right = tuple(s for s, arm in zip(sizes, mask) if not arm)
        n_left, n_right = sum(left), sum(right)
        answer += (g ** n_left * (1 - g) ** n_right
                   * ordinary_partition(left, x)
                   * ordinary_partition(right, y))
    return answer


def diag(n, x, y, g):
    return sum((F(comb(n, j)) * g ** j * (1 - g) ** (n - j)
                * x ** lam(j) * y ** lam(n - j) for j in range(n + 1)), F(0))


def d(n, x, y, g):
    p22 = bare_partition((2, 2) + (1,) * (n - 4), x, y, g)
    p3 = bare_partition((3,) + (1,) * (n - 3), x, y, g)
    return (3 * p22 - 2 * p3) / (2 * n - 3)


def scalars(x, y, g):
    e = (2 * bare_partition((3, 2, 1, 1), x, y, g)
         - bare_partition((4, 1, 1, 1), x, y, g)) / 6
    return d(9, x, y, g), d(6, x, y, g), e


def integer_partitions(n, low=1):
    if n == 0:
        yield ()
    else:
        for first in range(low, n + 1):
            for tail in integer_partitions(n - first, first):
                yield (first,) + tail


def partition_multiplicity(sizes):
    denominator = prod(factorial(s) for s in sizes)
    denominator *= prod(factorial(sizes.count(s)) for s in set(sizes))
    return factorial(sum(sizes)) // denominator


def source_checks(cell):
    x, y, g = cell
    assertions = 0
    for n in range(1, 10):
        total = F(0)
        for sizes in integer_partitions(n):
            p = bare_partition(sizes, x, y, g)
            assert p >= 0
            assertions += 1
            total += partition_multiplicity(sizes) * p
            if n <= 8:
                extended = bare_partition(sizes + (1,), x, y, g)
                for j in range(len(sizes)):
                    larger = sizes[:j] + (sizes[j] + 1,) + sizes[j + 1:]
                    extended += bare_partition(larger, x, y, g)
                assert extended == p
                assertions += 1
        assert total == 1
        assertions += 1
        assert bare_partition((1,) * n, x, y, g) == diag(n, x, y, g)
        assertions += 1
    return assertions


def identity():
    return [[F(int(i == j)) for j in range(4)] for i in range(4)]


def multiply(left, right):
    return [[sum((left[i][k] * right[k][j] for k in range(4)), F(0))
             for j in range(4)] for i in range(4)]


def bare_matrix(cell):
    x, y, g = cell
    f, h, e = scalars(x, y, g)
    p9, p7, p6, p4 = [diag(n, x, y, g) for n in (9, 7, 6, 4)]
    return [[p9, f, f, F(0)], [F(0), p7, F(0), -h + 2 * e],
            [F(0), F(0), p6, h], [F(0), F(0), F(0), p4]]


def ordinary_matrix(a):
    answer = identity()
    for i, n in enumerate((9, 7, 6, 4)):
        answer[i][i] = a ** lam(n)
    return answer


def word_checks(cells, pads):
    assert len(pads) == len(cells) + 1
    matrix = ordinary_matrix(pads[0])
    charges = []
    for i, cell in enumerate(cells):
        bare = bare_matrix(cell)
        A9, A7, A6, A4 = [matrix[j][j] for j in range(4)]
        p9, p7, p6, p4 = [bare[j][j] for j in range(4)]
        f, h, e = scalars(*cell)
        beta = A9 * f / (A6 * p6)
        chi = A6 * p6 / (A7 * p7)
        tau = A6 * h / (A4 * p4)
        extra = A7 * (2 * e - (1 - p7 / p6) * h) / (A4 * p4)
        kappa = tau - F(5, 3) * chi ** 2 * beta
        charges.append((beta, chi, tau, extra, kappa))
        matrix = multiply(multiply(matrix, bare), ordinary_matrix(pads[i + 1]))
    beta_total = sum((r[0] for r in charges), F(0))
    alpha_total = sum((r[0] * r[1] for r in charges), F(0))
    assert beta_total == matrix[0][2] / matrix[2][2]
    assert alpha_total == matrix[0][1] / matrix[1][1]
    assert sum((r[2] for r in charges), F(0)) == matrix[2][3] / matrix[3][3]
    assert sum((r[3] - r[2] / r[1] for r in charges), F(0)) == matrix[1][3] / matrix[3][3]
    S, energy = F(0), F(0)
    for i in range(len(charges) - 1):
        S += charges[i][0]
        difference = charges[i + 1][1] ** 2 - charges[i][1] ** 2
        assert difference > 0
        energy += difference * S ** 2
    defect = F(0)
    ordered = F(0)
    for r in range(len(charges)):
        for t in range(r + 1, len(charges)):
            b, chi, _, _, _ = charges[r]
            _, chi_t, tau_t, extra_t, kappa_t = charges[t]
            defect += b * kappa_t * (1 - chi / chi_t) + chi * b * extra_t
            ordered += b * tau_t * (1 - chi / chi_t) + chi * b * extra_t
    boundary = charges[-1][1] ** 2 * beta_total ** 2 - alpha_total ** 2
    formula = F(5, 6) * (boundary - energy) + defect
    actual = matrix[0][3] / matrix[3][3]
    assert ordered == actual
    assert formula == actual
    return {'cell_count': len(cells), 'identity_assertions': 6 + len(cells) - 1,
            'energy_nonnegative': energy >= 0,
            'endpoint_upper_equalities_imposed': False,
            'full_lower_forest_equalities_imposed': False,
            'defect_nonzero': defect != 0,
            'source_product_formula_exact': True}


def fraction_record(x):
    return {'numerator': str(x.numerator), 'denominator': str(x.denominator),
            'sign': (x > 0) - (x < 0)}


def main(path):
    fixtures = [(F(1, 100), F(99, 100), F(1, 2)),
                (F(1, 2), F(1, 2), F(1, 2)),
                (F(2, 5), F(4, 5), F(1, 3))]
    assertion_count = sum(source_checks(cell) for cell in fixtures)
    ordinary_controls = 0
    for x in (F(1, 2), F(3, 4)):
        for n in range(4, 10):
            p22 = ordinary_partition((2, 2) + (1,) * (n - 4), x)
            p3 = ordinary_partition((3,) + (1,) * (n - 3), x)
            assert 3 * p22 - 2 * p3 == 0
            ordinary_controls += 1
        assert (2 * ordinary_partition((3, 2, 1, 1), x)
                - ordinary_partition((4, 1, 1, 1), x)) == 0
        ordinary_controls += 1
    strict = fixtures[0]
    f, h, e = scalars(*strict)
    p7, p6, p4 = [diag(n, *strict) for n in (7, 6, 4)]
    kappa = h / p4 - F(5, 3) * p6 * f / p7 ** 2
    extra = (2 * e - (1 - p7 / p6) * h) / p4
    assert kappa > 0
    assert extra < 0
    word_receipts = [word_checks(fixtures, [F(3, 4), F(2, 3), F(4, 5), F(5, 6)]),
                     word_checks([fixtures[2], fixtures[0]], [F(5, 7), F(3, 5), F(7, 8)])]
    boundary = (F(0), F(1), F(1, 2))
    bf, bh, be = scalars(*boundary)
    bp7, bp6, bp4 = [diag(n, *boundary) for n in (7, 6, 4)]
    assert bf == F(-1, 3840) and bh == F(-1, 288) and be == F(-1, 768)
    assert bh / bp4 - F(5, 3) * bp6 * bf / bp7 ** 2 == F(1, 960)
    assert (2 * be - (1 - bp7 / bp6) * bh) / bp4 == F(-1, 280)
    result = {
        'scope': 'Bounded exact rational original current-root EPPF arithmetic through nine roots; no target fibre search.',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'fixtures': [[str(v) for v in cell] for cell in fixtures],
        'source_probability_projectivity_assertions': assertion_count,
        'ordinary_zero_band_controls': ordinary_controls,
        'strict_fixture': {'x': '1/100', 'y': '99/100', 'g': '1/2',
                           'f': fraction_record(f), 'h': fraction_record(h), 'e': fraction_record(e),
                           'kappa_without_positive_leading_scale': fraction_record(kappa),
                           'extra_without_positive_leading_scale': fraction_record(extra)},
        'boundary_control': {'physical_source': False, 'f': '-1/3840', 'h': '-1/288', 'e': '-1/768',
                             'kappa': '1/960', 'extra': '-1/280'},
        'word_receipts': word_receipts,
        'full_lower_target_witness': False,
        'lean_invocations': 0, 'ci_dispatches': 0, 'QE_runs': 0,
    }
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'receipt': str(path), 'source_assertions': assertion_count,
                      'strict_kappa_sign': 1, 'strict_extra_sign': -1,
                      'word_products_exact': len(word_receipts), 'full_lower_target_witness': False}))


if __name__ == '__main__':
    main(Path(sys.argv[1]))
