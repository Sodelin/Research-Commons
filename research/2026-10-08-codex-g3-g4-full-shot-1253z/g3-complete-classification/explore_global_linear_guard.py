"""Numerical candidate exploration only; no continuum or exact-zero proof."""
import json
import sys
import numpy as np
import scipy
from scipy.optimize import linprog


def explore():
    rows = []
    for d in (6, 8, 10, 12, 16):
        lam = np.arange(2, d + 2, dtype=float)
        lam = lam * (lam - 1) / 2
        ps = 1 / (1 + np.exp(-np.linspace(-7, 7, 31)))
        qs = np.exp(-np.linspace(.005, 7, 40))
        grid_p, grid_q = np.meshgrid(ps, qs)
        p = grid_p.ravel()[:, None]
        q = grid_q.ravel()[:, None]
        factors = 1 - p + p * q ** lam
        signatures = -np.log(factors)
        normalized = signatures / np.linalg.norm(signatures, axis=1)[:, None]
        for p0, q0 in ((.2, .5), (.5, .5), (.8, .5), (.5, .2), (.5, .8)):
            f0 = 1 - p0 + p0 * q0 ** lam
            h = -np.log(f0)
            hp = (1 - q0 ** lam) / f0
            hq = -p0 * lam * q0 ** (lam - 1) / f0
            equality = np.vstack((lam, h, hp, hq))
            equality /= np.linalg.norm(equality, axis=1)[:, None]
            # Signed c with ||c||_1 <= 1. The grid is never the full domain.
            objective = np.r_[-normalized.sum(axis=0), normalized.sum(axis=0)] / len(normalized)
            inequality = np.vstack((np.c_[-normalized, normalized], np.ones((1, 2 * d))))
            rhs = np.r_[np.zeros(len(normalized)), 1.]
            result = linprog(
                objective, A_ub=inequality, b_ub=rhs,
                A_eq=np.c_[equality, -equality], b_eq=np.zeros(4),
                bounds=(0, None), method='highs',
                options={'dual_feasibility_tolerance': 1e-9,
                         'primal_feasibility_tolerance': 1e-9},
            )
            row = {'d': d, 'anchor_p': p0, 'anchor_q': q0,
                   'sample_count': len(normalized), 'solver_success': bool(result.success),
                   'solver_message': result.message}
            if result.success:
                c = result.x[:d] - result.x[d:]
                row.update({'candidate_c': c.tolist(),
                            'objective': float(-result.fun),
                            'c_l2': float(np.linalg.norm(c)),
                            'normalized_sample_minimum': float((normalized @ c).min()),
                            'normalized_anchor_max_error': float(abs(equality @ c).max()),
                            'unscaled_anchor_H_value': float(h @ c)})
            rows.append(row)
    return {'schema': 'g3-global-linear-guard-floating-exploration-v1',
            'status': 'EXPLORATION ONLY: no exact anchor zero or continuum inequality certified',
            'executed_source_sha256': globals().get('CAPTURED_SOURCE_SHA256'),
            'python': sys.version, 'numpy': np.__version__, 'scipy': scipy.__version__,
            'run_count': len(rows), 'runs': rows,
            'scope': 'Actual mathematical cell signature sampled; no forward graph compiler, RCF, Lean or CI',
            'claim': 'No proven global guard, source-boundary YES, or refutation of the search architecture'}


if __name__ == '__main__':
    print(json.dumps(explore(), sort_keys=True, indent=2, allow_nan=False))
