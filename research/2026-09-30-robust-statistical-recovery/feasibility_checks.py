"""Independent checks of exact feasible-law provider; scipy is a test oracle only."""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from time import perf_counter

from robust_support import Contract, certify as contrast_certify, radius_squared
from law_feasibility import certify, certify_boxes, sharp_distance, upper_root


def verify_witnesses(certificate, boxes, contract):
    """Check original simplex/noise/model statements, not eliminated inequalities."""
    assert set(certificate.witnesses) == set(certificate.candidates)
    for mask, rows in certificate.witnesses.items():
        assert len(rows) == contract.rows
        covered = 0
        for e, (row, box) in enumerate(zip(rows, boxes)):
            p, r = row['p'], row['r']
            assert len(p) == len(r) == 3
            assert all(isinstance(x, F) for x in p + r)
            assert sum(p) == sum(r) == 1
            assert min(p) >= 0 and min(r) >= 0
            lo, hi = box
            assert all(lo[i] <= r[i] <= hi[i] for i in range(3))
            epsilon = contract.error[e]
            if contract.noise == 'tv':
                assert sum(abs(p[i] - r[i]) for i in range(3)) / 2 <= epsilon
            else:
                residual = tuple(r[i] - (1 - epsilon) * p[i] for i in range(3))
                assert min(residual) >= 0 and sum(residual) == epsilon
                if epsilon == 0:
                    assert p == r
                else:
                    contamination = tuple(x / epsilon for x in residual)
                    assert min(contamination) >= 0 and sum(contamination) == 1
            for t in range(3):
                if not mask & (1 << t):
                    assert all(p[t] <= p[j] for j in range(3))
            for t, j in row['witnesses']:
                assert mask & (1 << t) and 0 <= j < 3
                assert p[t] - p[j] >= contract.gap
                covered |= 1 << t
        assert covered == mask
    expected = ('MODEL_INCOMPATIBLE' if not certificate.candidates else
                'CERTIFIED' if len(certificate.candidates) == 1 else 'INCONCLUSIVE')
    assert certificate.status == expected
    assert certificate.mask == (certificate.candidates[0] if expected == 'CERTIFIED' else None)


def boxes_for_counts(counts, contract, queries, delta, anytime=True):
    result = []
    for row in counts:
        n = sum(row)
        if not n:
            result.append(((F(0),) * 3, (F(1),) * 3))
            continue
        r2 = radius_squared(n, contract.rows, queries, delta, anytime=anytime)
        rho = upper_root(r2, n)
        assert rho * rho >= r2
        assert rho == 0 or (rho - F(1, n)) ** 2 < r2
        center = tuple(F(x, n) for x in row)
        result.append((tuple(max(F(0), x - rho) for x in center),
                       tuple(min(F(1), x + rho) for x in center)))
    return tuple(result)


def original_lp_candidates(boxes, contract):
    """Solve full p/r model with globally assigned gap witnesses using HiGHS.

    This bypasses row projection and DP; numerical answers are only an
    independent oracle for the deliberately well-conditioned checks below.
    """
    import numpy as np
    from scipy.optimize import linprog

    m = contract.rows
    if any(sum(lo) > 1 or sum(hi) < 1 or any(l > u for l, u in zip(lo, hi))
           for lo, hi in boxes):
        return ()
    bounds, equalities, equal_rhs = [], [], []
    base, rhs = [], []
    for e, (lo, hi) in enumerate(boxes):
        bounds.extend([(0, 1)] * 3)
        bounds.extend([(float(l), float(u)) for l, u in zip(lo, hi)])
        for offset in (0, 3):
            row = [0.0] * (6 * m)
            for i in range(3):
                row[6 * e + offset + i] = 1.0
            equalities.append(row)
            equal_rhs.append(1.0)
        for i in range(3):
            row = [0.0] * (6 * m)
            if contract.noise == 'tv':
                row[6 * e + i], row[6 * e + 3 + i] = 1.0, -1.0
                base.append(row)
                rhs.append(float(contract.error[e]))
                base.append([-x for x in row])
                rhs.append(float(contract.error[e]))
            else:
                row[6 * e + i] = float(1 - contract.error[e])
                row[6 * e + 3 + i] = -1.0
                base.append(row)
                rhs.append(0.0)
    candidates = []
    for mask in contract.legal_masks:
        absent, absent_rhs = [], []
        for e in range(m):
            for t in range(3):
                if not mask & (1 << t):
                    for j in range(3):
                        row = [0.0] * (6 * m)
                        row[6 * e + t] += 1.0
                        row[6 * e + j] -= 1.0
                        absent.append(row)
                        absent_rhs.append(0.0)
        ts = [t for t in range(3) if mask & (1 << t)]
        options = [[(e, j) for e in range(m) for j in range(3) if j != t] for t in ts]
        for assignments in product(*options):
            gap_constraints = []
            for t, (e, j) in zip(ts, assignments):
                row = [0.0] * (6 * m)
                row[6 * e + j] += 1.0
                row[6 * e + t] -= 1.0
                gap_constraints.append(row)
            result = linprog(np.zeros(6 * m), A_ub=base + absent + gap_constraints,
                             b_ub=rhs + absent_rhs + [-float(contract.gap)] * len(ts),
                             A_eq=equalities, b_eq=equal_rhs, bounds=bounds, method='highs',
                             options={'primal_feasibility_tolerance': 1e-9})
            assert result.status in (0, 2), result.message
            if result.status == 0:
                candidates.append(mask)
                break
    return tuple(candidates)


def main():
    started = perf_counter()
    checks = []

    def check_boxes(name, boxes, contract, expected=None, lp=True):
        cert = certify_boxes(boxes, contract)
        verify_witnesses(cert, boxes, contract)
        if expected is not None:
            assert cert.candidates == expected, (name, cert.candidates, expected)
        if lp:
            oracle = original_lp_candidates(boxes, contract)
            assert oracle == cert.candidates, (name, oracle, cert.candidates)
        checks.append({'name': name, 'status': cert.status, 'candidates': cert.candidates,
                       'original_constraints_verified': True, 'scipy_full_model_agrees': lp})
        return cert

    def law_box(p):
        return (p, p)

    # Exact observed-law limits and source-overlap boundaries.
    A = (F(32, 48), F(8, 48), F(8, 48))
    B = (F(32, 48), F(5, 48), F(11, 48))
    check_boxes('noiseless_source_A', (law_box(A),), Contract(F(1, 8), (0,)), (1,))
    check_boxes('noiseless_source_B', (law_box(B),), Contract(F(1, 8), (0,)), (5,))
    tv_r = (F(64, 96), F(13, 96), F(19, 96))
    huber_r = (F(32, 51), F(8, 51), F(11, 51))
    assert sum(abs(A[i] - tv_r[i]) for i in range(3)) / 2 == F(1, 32)
    assert sum(abs(B[i] - tv_r[i]) for i in range(3)) / 2 == F(1, 32)
    assert sum(max(A[i], B[i]) for i in range(3)) == F(17, 16)
    for noise, err, r in [('tv', F(1, 32), tv_r), ('huber', F(1, 17), huber_r)]:
        contract = Contract(F(1, 8), (err,), noise)
        check_boxes(f'{noise}_overlap_at_exact_law', (law_box(r),), contract, (1, 5))
        raw_counts = (64, 13, 19) if noise == 'tv' else (32, 8, 11)
        for scale in (10**4, 10**8):
            counts = (tuple(x * scale for x in raw_counts),)
            boxes = boxes_for_counts(counts, contract, 3, F(1, 100))
            cert = certify(counts, contract, 3, F(1, 100))
            verify_witnesses(cert, boxes, contract)
            assert cert.candidates == (1, 5)
            checks.append({'name': f'{noise}_overlap_finite_counts_scale_{scale}',
                           'counts': counts, 'status': cert.status, 'candidates': cert.candidates,
                           'original_constraints_verified': True})

    # Positive sharp separation while coordinate-contrast margin is nonpositive.
    for noise, err, sharp_margin in [('tv', F(1, 5), F(1, 60)),
                                      ('huber', F(2, 7), F(1, 84))]:
        contract = Contract(F(3, 4), (err, err), noise)
        h = sharp_distance(contract.gap, contract.rows)
        separation = h - 2 * err if noise == 'tv' else (1 - err) * h - err
        assert h == F(5, 12) and separation == sharp_margin and contract.margin <= 0
        raw_counts = ((11, 4, 5), (5, 4, 11)) if noise == 'tv' else ((50, 29, 5), (50, 29, 5))
        expected = (5,) if noise == 'tv' else (1,)
        counts = tuple(tuple(x * 10**8 for x in row) for row in raw_counts)
        boxes = boxes_for_counts(counts, contract, 3, F(1, 100))
        exact = check_boxes(f'{noise}_large_gap_sharp_separation', boxes, contract, expected)
        assert certify(counts, contract, 3, F(1, 100)).candidates == exact.candidates
        conservative = contrast_certify(counts, contract, 3, F(1, 100))
        assert conservative.status == 'INCONCLUSIVE'
        checks[-1].update({'sharp_law_distance': str(h), 'sharp_margin': str(separation),
                           'contrast_margin': str(contract.margin),
                           'contrast_status': conservative.status,
                           'contrast_candidates': conservative.candidates})

    full = ((F(0),) * 3, (F(1),) * 3)
    check_boxes('zero_counts_single_row', (full,), Contract(F(1, 8), (0,)), (1, 2, 3, 4, 5, 6))
    check_boxes('zero_counts_two_rows_mask7_legal', (full, full),
                Contract(F(1, 8), (0, 0), legal_masks=(1, 2, 3, 4, 5, 6, 7)),
                (1, 2, 3, 4, 5, 6, 7))
    impossible = ((F(3, 4), F(3, 4), F(0)), (F(1), F(1), F(1)))
    check_boxes('incompatible_box_sum_lower_above_one', (impossible,), Contract(F(1, 8), (0,)), ())
    check_boxes('zero_counts_large_gap_one_row_excludes_two_bits', (full,), Contract(F(3, 4), (0,)), (1, 2, 4))
    check_boxes('permuted_source_B', (law_box((B[2], B[0], B[1])),), Contract(F(1, 8), (0,)), (3,))

    # Rational boxes spanning both interior and boundary cases; LP uses original variables.
    centers = [(F(1, 3),) * 3, (F(3, 5), F(1, 4), F(3, 20)),
               (F(1, 10), F(7, 10), F(1, 5)), (F(2, 5), F(2, 5), F(1, 5))]
    for k, center in enumerate(centers):
        width = F(k + 1, 100)
        box = (tuple(max(F(0), x - width) for x in center),
               tuple(min(F(1), x + width) for x in center))
        for noise in ('tv', 'huber'):
            errors = (F(k, 25), F(k + 1, 25))
            boxes = (box, (box[0][::-1], box[1][::-1]))
            check_boxes(f'rational_box_{k}_{noise}_two_rows', boxes,
                        Contract(F(1 + k, 10), errors, noise))

    # Radius ceilings include exact squares, irrational roots, and very large counts.
    radius_checks = 0
    for x in (F(0), F(1, 4), F(2), F(2, 3), F(97, 10000)):
        for n in (1, 3, 10**8):
            upper = upper_root(x, n)
            assert upper * upper >= x
            assert upper == 0 or (upper - F(1, n)) ** 2 < x
            radius_checks += 1
    for counts in (((0, 0, 0),), ((1, 2, 3),), ((10**12, 0, 0),)):
        contract = Contract(F(1, 8), (F(1, 32),))
        for anytime in (False, True):
            boxes = boxes_for_counts(counts, contract, 3, F(1, 100), anytime)
            cert = certify(counts, contract, 3, F(1, 100), anytime=anytime)
            verify_witnesses(cert, boxes, contract)
            assert cert.candidates == certify_boxes(boxes, contract).candidates
            radius_checks += 1

    invalid_checks = 0
    contract = Contract(F(1, 8), (0,))
    for counts in (((True, 0, 0),), ((1.0, 0, 0),), ((-1, 0, 0),), ((1, 2),), (), ((1, 0, 0), (1, 0, 0))):
        try:
            certify(counts, contract, 3, F(1, 100))
        except ValueError:
            invalid_checks += 1
        else:
            raise AssertionError(('invalid counts accepted', counts))
    for queries, delta in ((0, F(1, 100)), (1, 0), (1, 1), (1, 0.05)):
        try:
            certify(((0, 0, 0),), contract, queries, delta)
        except ValueError:
            invalid_checks += 1
        else:
            raise AssertionError(('invalid risk accepted', queries, delta))

    folder = Path(__file__).resolve().parent
    pins = {name: hashlib.sha256((folder / name).read_bytes()).hexdigest()
            for name in ('law_feasibility.py', 'robust_support.py', 'feasibility_checks.py')}
    record = {'all_checks_passed': True, 'candidate_case_count': len(checks),
              'independent_scipy_case_count': sum(bool(x.get('scipy_full_model_agrees')) for x in checks),
              'radius_and_count_checks': radius_checks, 'invalid_input_checks': invalid_checks,
              'runtime_seconds': round(perf_counter() - started, 3),
              'sha256': pins, 'cases': checks,
              'oracle_scope': 'SciPy only verifies tests in original p/r variables; provider decisions use exact Fractions.',
              'model_scope': 'Abstract complete-support class; no biological realizability claim.'}
    output = folder / 'feasibility-checks.json'
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({key: record[key] for key in ('all_checks_passed', 'candidate_case_count',
                                                'independent_scipy_case_count', 'radius_and_count_checks',
                                                'invalid_input_checks', 'runtime_seconds', 'sha256')}, indent=2))


if __name__ == '__main__':
    main()
