#!/usr/bin/env python3
"""Exact scalar probability-algebra checks; not a source-law simulator or Lean proof."""
import json
import sympy as s

z = s.Symbol('z')
R = s.Rational


def zero(value):
    return s.simplify(value) == 0


def nonnegative(value):
    result = s.simplify(value).is_nonnegative
    if result is None:
        raise ValueError(f'Exact sign unresolved: {value}')
    return bool(result)


def palette(mu):
    """Complete for rational positive atoms/weights, with exact algebraic coins."""
    assert all(x.is_Rational and x > 0 for x in mu)
    assert all(w.is_Rational and w > 0 for w in mu.values())
    assert sum(mu.values()) == 1
    atoms = set(mu)
    ratios = sorted({y / x for x in atoms for y in atoms if y < x})
    accepted = []
    rejected_negative = []
    for ratio in ratios:
        paths = []
        for top in sorted((x for x in atoms if x / ratio not in atoms), reverse=True):
            path = []
            x = top
            while x in atoms:
                path.append(x)
                x *= ratio
            paths.append(path)
        assert {x for path in paths for x in path} == atoms
        polys = [s.Poly(sum(mu[x] * z**j for j, x in enumerate(path)), z)
                 for path in paths]
        common = polys[0]
        for poly in polys[1:]:
            common = s.gcd(common, poly)
        for root, multiplicity in s.real_roots(common, multiple=False):
            if not (root < 0):
                continue
            alpha = s.simplify(-root / (1 - root))
            remainder = {}
            valid = True
            for path, poly in zip(paths, polys):
                q, rem = s.div(poly.as_expr(), alpha + (1 - alpha) * z,
                               z, extension=True)
                assert zero(rem)
                coefficients = [s.simplify(s.expand(q).coeff(z, j))
                                for j in range(len(path) - 1)]
                valid &= all(nonnegative(v) for v in coefficients)
                for x, v in zip(path[:-1], coefficients):
                    if not zero(v):
                        remainder[x] = v
            if not valid:
                rejected_negative.append((ratio, alpha))
                continue
            assert zero(sum(remainder.values()) - 1)
            reconstructed = {}
            for x, mass in remainder.items():
                for point, value in [(x, alpha * mass), (ratio * x, (1 - alpha) * mass)]:
                    reconstructed[point] = reconstructed.get(point, 0) + value
            assert set(reconstructed) == atoms
            assert all(zero(reconstructed[x] - mu[x]) for x in atoms)
            assert nonnegative(alpha - mu[max(atoms)])
            assert nonnegative(1 - alpha - mu[min(atoms)])
            accepted.append((ratio, alpha, multiplicity))
    return accepted, rejected_negative


def geometric(weights):
    return {R(1, 2) ** (j + 1): R(w) for j, w in enumerate(weights)}


def main():
    cases = [
        ('two_distinct_ratios', {R(1,2):R(2,5), R(1,4):R(1,5), R(1,6):R(4,15), R(1,12):R(2,15)},
         [(R(1,2), R(2,3), 1), (R(1,3), R(3,5), 1)]),
        ('two_coins_one_ratio', geometric([R(2,9), R(5,9), R(2,9)]),
         [(R(1,2), R(1,3), 1), (R(1,2), R(2,3), 1)]),
        ('gapped_quotient', geometric([R(1,4)] * 4),
         [(R(1,2), R(1,2), 1), (R(1,4), R(1,2), 1)]),
        ('negative_quotient_rejected', geometric([R(5,16), R(3,16), R(3,16), R(5,16)]), []),
        ('disconnected_paths', {R(1,2):R(3,10), R(1,4):R(1,5), R(1,5):R(3,10), R(1,10):R(1,5)},
         [(R(1,2), R(3,5), 1), (R(2,5), R(1,2), 1)]),
        ('incompatible_path_roots', {R(1,2):R(1,5), R(1,4):R(3,10), R(1,5):R(1,4), R(1,10):R(1,4)}, []),
        ('singleton', {R(1,2):s.Integer(1)}, []),
        ('repeated_factor', geometric([R(1,4), R(1,2), R(1,4)]),
         [(R(1,2), R(1,2), 2)]),
        ('irrational_coins', geometric([R(1,8), R(3,4), R(1,8)]),
         [(R(1,2), (2-s.sqrt(2))/4, 1), (R(1,2), (2+s.sqrt(2))/4, 1)]),
    ]
    report = {'scope': 'exact scalar finite-measure algebra; no source compiler or Lean execution',
              'sympy_version': s.__version__, 'cases': []}
    for name, mu, expected in cases:
        got, rejected = palette(mu)
        assert len(got) == len(expected), (name, got, expected)
        assert all(any(a == x and zero(b-y) and c == m for x,y,m in got)
                   for a,b,c in expected), (name, got, expected)
        if name == 'negative_quotient_rejected':
            assert (R(1,2), R(1,2)) in rejected
        report['cases'].append({'name': name, 'passed': True,
                                'palette_ratio_short_coin_root_multiplicity':
                                [[str(x), str(a), int(m)] for x,a,m in got],
                                'negative_quotient_rejections': [[str(x), str(a)] for x,a in rejected]})
    report['passed'] = len(cases)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
