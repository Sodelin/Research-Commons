#!/usr/bin/env python3
"""Closed-form three-sample checks of the inherited full joint law compiler.

The expected expressions below follow directly from the probability of no
pair merger before the ancestral root and the root's three equally likely
first pairs. They do not execute the compiler's frontier algorithm.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import sympy as sp

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
PROVIDER = ROOT / 'research/2026-10-01-g7-continuous-design/law_compiler.py'


def no_bc_merger(mode, x1, x2, x3, x4, gamma):
    if mode == 'common':
        parent = gamma * x2 + (1 - gamma) * x3
    elif mode == 'independent':
        parent = gamma**2 * x2 + (1 - gamma)**2 * x3 + 2 * gamma * (1 - gamma)
    elif mode == 'forced-0':
        parent = x2
    elif mode == 'forced-1':
        parent = x3
    else:
        raise ValueError(mode)
    return x4 * x1 * parent


def three_topology_law(no_merger):
    return {'bc': sp.expand(1 - sp.Rational(2, 3) * no_merger),
            'ab': sp.expand(no_merger / 3), 'ac': sp.expand(no_merger / 3)}


def descendants(tree):
    return {tree} if isinstance(tree, str) else descendants(tree[0]) | descendants(tree[1])


def topology(tree):
    for child in tree:
        tips = descendants(child)
        if len(tips) == 2:
            return ''.join(sorted(tips))
    raise ValueError('Expected a rooted three-label genealogy')


def main():
    raw = PROVIDER.read_bytes()
    spec = importlib.util.spec_from_file_location('inherited_joint_law_baseline', PROVIDER)
    compiler = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = compiler
    spec.loader.exec_module(compiler)
    x = sp.symbols('x0:5')
    g = sp.Symbol('g_3')
    ordinary = compiler.Network((('0', '1'), ('0', '2'), ('2', '3'), ('2', '4')), '0', ('1', '3', '4'))
    parallel = compiler.Network((('0', '1'), ('0', '2'), ('2', '3'), ('2', '3'), ('3', '4')), '0', ('1', '4'))
    rows = []
    cases = [('ordinary', ordinary, 'independent', {'1': ('a',), '3': ('b',), '4': ('c',)}, None, x[1])]
    for mode in ('common', 'independent', 'forced-0', 'forced-1'):
        forced = {'3': int(mode[-1])} if mode.startswith('forced') else None
        mechanism = mode if not forced else 'independent'
        cases.append((mode, parallel, mechanism, {'1': ('a',), '4': ('b', 'c')}, forced,
                      no_bc_merger(mode, x[1], x[2], x[3], x[4], g)))
    for name, net, mechanism, samples, forced, no_merger in cases:
        emitted = compiler.compile_law(net, mechanism, forced=forced, samples=samples)
        actual = {topology(tree): poly for tree, poly in emitted.items()}
        expected = three_topology_law(no_merger)
        passed = set(actual) == set(expected) and all(sp.expand(actual[t] - expected[t]) == 0 for t in expected)
        rows.append({'case': name, 'pass': passed,
                     'expected_exact_polynomials': {t: str(p) for t, p in expected.items()},
                     'emitted_exact_polynomials': {t: str(p) for t, p in actual.items()},
                     'normalization_exactly_one': sp.expand(sum(actual.values()) - 1) == 0})
    difference = sp.factor(no_bc_merger('independent', x[1], x[2], x[3], x[4], g)
                           - no_bc_merger('common', x[1], x[2], x[3], x[4], g))
    contrast = sp.expand(difference - x[1] * x[4] * g * (1 - g) * (2 - x[2] - x[3])) == 0
    stable = PROVIDER.read_bytes() == raw
    result = {'status': 'PASS' if stable and contrast and all(r['pass'] and r['normalization_exactly_one'] for r in rows) else 'FAIL',
              'cases': rows, 'cases_total': len(rows), 'cases_passed': sum(r['pass'] for r in rows),
              'inherited_provider': str(PROVIDER.relative_to(ROOT)), 'provider_sha256': hashlib.sha256(raw).hexdigest(),
              'provider_bytes_stable': stable, 'sympy_version': sp.__version__,
              'oracle_source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'independent_minus_common_no_merger': str(difference), 'contrast_formula_checked': contrast,
              'scope': 'Inherited Python full-joint provider agrees with five independent symbolic three-sample formulas. No native parity, physical source admission, calibration or unknown-size source-coverage claim.'}
    out = PACKET / 'quality/evidence/law-analytic-baseline-1'
    out.mkdir(parents=True, exist_ok=False)
    (out / 'ORACLE.py').write_bytes(Path(__file__).read_bytes())
    (out / 'PROVIDER.py').write_bytes(raw)
    (out / 'RECEIPT.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'cases_passed', 'cases_total', 'contrast_formula_checked')}))
    return result['status'] != 'PASS'


if __name__ == '__main__':
    raise SystemExit(main())
