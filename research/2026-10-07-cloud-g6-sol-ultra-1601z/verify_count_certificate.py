"""Bounded exact controls using direct factorial reconstruction, not exp floats."""
import hashlib
import json
import math
import time
from fractions import Fraction
from pathlib import Path

from count_certificate import certify, weights


def direct(a, k):
    terms = [a ** j / math.factorial(j) for j in range(k + 1)]
    s = sum(terms)
    t = a ** (k + 1) / math.factorial(k + 1)
    return s, t, 2 * t / (s + 2 * t)


started = time.monotonic()
cases = []
for a in [Fraction(0), Fraction(1, 2), Fraction(1), Fraction(5), Fraction(10), Fraction(128)]:
    for eps in [Fraction(1, 4), Fraction(1, 100), Fraction(1, 2 ** 16), Fraction(1, 2 ** 64)]:
        result = certify(a, eps, max_steps=1024)
        assert result['status'] == 'CERTIFIED'
        k = result['K']
        s, t, delta = direct(a, k)
        assert k + 2 >= 2 * a and delta <= eps
        assert (s, t, s + 2 * t, delta) == tuple(Fraction(result[x]) for x in ['S', 'T', 'U', 'delta'])
        q = weights(a, k)
        assert sum(q) == 1 and all(x >= 0 for x in q)
        assert q == tuple((a ** j / math.factorial(j)) / s for j in range(k + 1))
        for previous in range(k):
            assert previous + 2 < 2 * a or direct(a, previous)[2] > eps
        cases.append({'a': str(a), 'epsilon': str(eps), 'K': k, 'status': 'PASS'})

equality = certify(Fraction(1), Fraction(3, 4), max_steps=1)
assert equality['status'] == 'CERTIFIED' and equality['K'] == 0
assert equality['K'] + 2 == 2 * Fraction(equality['a'])
assert weights(Fraction(0), 0) == (Fraction(1),)
for limit in [0, 1, 4]:
    result = certify(Fraction(128), Fraction(1, 2 ** 64), max_steps=limit)
    assert result['status'] == 'RESOURCE_LIMIT' and result['inspected'] == limit
rejections = 0
for a, eps in [(Fraction(-1), Fraction(1, 2)), (Fraction(0), Fraction(0)),
               (Fraction(0), Fraction(1)), (Fraction(0), Fraction(-1))]:
    try:
        certify(a, eps, max_steps=1)
    except ValueError:
        rejections += 1
    else:
        raise AssertionError('invalid input accepted')
assert rejections == 4
receipt = {
    'status': 'PASS', 'cases': cases, 'certificates': len(cases),
    'zero_and_ratio_equality_boundaries': 'PASS', 'resource_limits': 3,
    'invalid_inputs_rejected': rejections, 'wall_seconds': time.monotonic() - started,
    'source_sha256': hashlib.sha256(Path(__file__).with_name('count_certificate.py').read_bytes()).hexdigest(),
    'controls_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'scope': 'exact rational numerical certificates and normalized weights; no biological/master proof',
}
print(json.dumps(receipt, sort_keys=True, indent=2))
