"""Exact finite-jet verifier. Standard library only; no source compiler.

A VERIFIED_POLYNOMIAL_JET verdict proves only the stated polynomial-fibre
existence implication, subject to the accompanying hand theorem. It does not
verify that supplied polynomials encode a G4 physical source or legal observers.
All algebraic coefficients share ONE isolated real root. No floats or eval.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from typing import Any

QP = tuple[Q, ...]
ZERO: QP = ()
ONE: QP = (Q(1),)

class InvalidCertificate(ValueError):
    pass

class ResourceLimit(RuntimeError):
    pass

def rat(x: Any) -> Q:
    if type(x) not in (str, int):
        raise InvalidCertificate('Rational coefficients must be integer or exact rational strings, not floats/bools')
    if isinstance(x, str) and any(c not in '-+0123456789/' for c in x):
        raise InvalidCertificate('Use integer/fraction strings, not decimals or expressions')
    try:
        return Q(x)
    except (ValueError, ZeroDivisionError) as exc:
        raise InvalidCertificate('Invalid rational coefficient') from exc

def trim(v) -> QP:
    a = list(v)
    while a and not a[-1]:
        a.pop()
    return tuple(a)

def add(a: QP, b: QP) -> QP:
    return trim((a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
                for i in range(max(len(a), len(b))))

def neg(a: QP) -> QP:
    return tuple(-x for x in a)

def mul(a: QP, b: QP) -> QP:
    if not a or not b:
        return ZERO
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)

def divrem(a: QP, b: QP) -> tuple[QP, QP]:
    if not b:
        raise ZeroDivisionError('zero polynomial')
    r = list(a)
    q = [Q(0)] * max(0, len(a)-len(b)+1)
    while len(r) >= len(b):
        k, v = len(r)-len(b), r[-1]/b[-1]
        q[k] = v
        for j, x in enumerate(b):
            r[k+j] -= v*x
        while r and not r[-1]:
            r.pop()
    return trim(q), tuple(r)

def deriv(a: QP) -> QP:
    return trim(i*a[i] for i in range(1, len(a)))

def gcd(a: QP, b: QP) -> QP:
    while b:
        a, b = b, divrem(a, b)[1]
    return tuple(x/a[-1] for x in a) if a else ZERO

def ev(a: QP, x: Q) -> Q:
    v = Q(0)
    for c in reversed(a):
        v = v*x+c
    return v

def sturm(a: QP) -> tuple[QP, ...]:
    if len(a) < 2:
        return (a,)
    seq = [a, deriv(a)]
    while seq[-1]:
        rem = neg(divrem(seq[-2], seq[-1])[1])
        if not rem:
            break
        seq.append(rem)
    return tuple(seq)

def changes(seq: tuple[QP, ...], x: Q) -> int:
    signs = [1 if v > 0 else -1 for p in seq if (v := ev(p, x))]
    return sum(a != b for a, b in zip(signs, signs[1:]))

def roots(a: QP, lo: Q, hi: Q) -> int:
    if len(a) < 2:
        return 0
    if not ev(a, lo) or not ev(a, hi):
        raise InvalidCertificate('Root-count interval endpoint lies on the polynomial')
    seq = sturm(a)
    return changes(seq, lo)-changes(seq, hi)

def interval_eval(a: QP, lo: Q, hi: Q) -> tuple[Q, Q]:
    lower = upper = Q(0)
    for c in reversed(a):
        vals = (lower*lo, lower*hi, upper*lo, upper*hi)
        lower, upper = min(vals)+c, max(vals)+c
    return lower, upper

class RealEmbedding:
    """Q[alpha] evaluated at one root. Reducible squarefree P is permitted.

    This is NOT claimed to be a field quotient when P is reducible. Equality
    at the chosen root uses gcd/root counting, not only remainder == 0.
    No division by algebraic elements is needed by this verifier.
    """
    def __init__(self, spec: dict, refinements: int = 512):
        if not isinstance(spec, dict):
            raise InvalidCertificate('embedding must be an object')
        raw = spec.get('polynomial')
        if not isinstance(raw, list) or len(raw) > 65:
            raise InvalidCertificate('Supply a polynomial coefficient list of degree at most 64')
        self.p = trim(rat(x) for x in raw)
        if len(self.p) < 2 or len(gcd(self.p, deriv(self.p))) != 1:
            raise InvalidCertificate('Embedding polynomial must be nonconstant and squarefree')
        bounds = spec.get('interval')
        if not isinstance(bounds, list) or len(bounds) != 2:
            raise InvalidCertificate('Supply two exact isolating endpoints')
        self.lo, self.hi = map(rat, bounds)
        if self.lo >= self.hi or roots(self.p, self.lo, self.hi) != 1:
            raise InvalidCertificate('Interval must isolate exactly one real root')
        self.refinements = refinements
        self.cache: dict[QP, int] = {ZERO: 0, ONE: 1}

    def reduce(self, a: QP) -> QP:
        return divrem(a, self.p)[1]

    def element(self, raw: Any) -> QP:
        if not isinstance(raw, list) or len(raw) > 1024:
            raise InvalidCertificate('Algebraic coefficients must be finite rational coefficient lists')
        return self.reduce(trim(rat(x) for x in raw))

    def plus(self, a: QP, b: QP) -> QP:
        return self.reduce(add(a, b))

    def times(self, a: QP, b: QP) -> QP:
        return self.reduce(mul(a, b))

    def sign(self, a: QP) -> int:
        a = self.reduce(a)
        if a in self.cache:
            return self.cache[a]
        shared = gcd(self.p, a)
        if len(shared) > 1 and roots(shared, self.lo, self.hi) == 1:
            self.cache[a] = 0
            return 0
        lo, hi = self.lo, self.hi
        for _ in range(self.refinements):
            lower, upper = interval_eval(a, lo, hi)
            if lower > 0 or upper < 0:
                s = 1 if lower > 0 else -1
                self.cache[a] = s
                return s
            mid = (lo+hi)/2
            if ev(self.p, mid) == 0:
                value = ev(a, mid)
                s = (value > 0)-(value < 0)
                self.cache[a] = s
                return s
            if roots(self.p, lo, mid) == 1:
                hi = mid
            else:
                lo = mid
        raise ResourceLimit('Algebraic sign isolation exceeded the refinement budget')

TP = dict[int, QP]
MP = list[tuple[QP, tuple[int, ...]]]

def tpadd(a: TP, b: TP, field: RealEmbedding) -> TP:
    out = dict(a)
    for k, v in b.items():
        out[k] = field.plus(out.get(k, ZERO), v)
    return {k: v for k, v in out.items() if field.sign(v)}

def tpmul(a: TP, b: TP, field: RealEmbedding, q: int) -> TP:
    out: TP = {}
    for i, x in a.items():
        for j, y in b.items():
            if i+j < q:
                out[i+j] = field.plus(out.get(i+j, ZERO), field.times(x, y))
    return {k: v for k, v in out.items() if field.sign(v)}

def tppow(a: TP, e: int, field: RealEmbedding, q: int) -> TP:
    out: TP = {0: ONE}
    while e:
        if e & 1:
            out = tpmul(out, a, field, q)
        e //= 2
        if e:
            a = tpmul(a, a, field, q)
    return out

def parse_mp(raw: Any, n: int, field: RealEmbedding) -> MP:
    if not isinstance(raw, list) or len(raw) > 10000:
        raise InvalidCertificate('Polynomial is a bounded list of coefficient/exponents terms')
    merged: dict[tuple[int, ...], QP] = {}
    for term in raw:
        if not isinstance(term, dict):
            raise InvalidCertificate('Polynomial term must be an object')
        ex = term.get('exponents')
        if not isinstance(ex, list) or len(ex) != n or any(type(e) is not int or e < 0 for e in ex):
            raise InvalidCertificate('Exponents must be nonnegative integers, one per physical variable')
        if sum(ex) > 4096:
            raise ResourceLimit('Polynomial degree exceeds reference-checker budget')
        key = tuple(ex)
        merged[key] = field.plus(merged.get(key, ZERO), field.element(term.get('coefficient')))
    return [(v, ex) for ex, v in sorted(merged.items()) if field.sign(v)]

def compose(poly: MP, jets: list[TP], field: RealEmbedding, q: int) -> TP:
    out: TP = {}
    for c, ex in poly:
        term: TP = {0: c}
        for jet, e in zip(jets, ex):
            if e:
                term = tpmul(term, tppow(jet, e, field, q), field, q)
        out = tpadd(out, term, field)
    return out

def positive_order(poly: TP, field: RealEmbedding) -> int:
    for k in sorted(poly):
        s = field.sign(poly[k])
        if s:
            if s < 0:
                raise InvalidCertificate('A physical open-cube margin has negative leading coefficient')
            return k
    raise InvalidCertificate('A physical parameter remains identically on a forbidden boundary')

def verify(data: dict, max_order: int = 256) -> dict:
    if not isinstance(data, dict) or data.get('schema') != 'algebraic_margin_jet_v1':
        raise InvalidCertificate('Unsupported certificate schema')
    q = data.get('order')
    if type(q) is not int or q < 1:
        raise InvalidCertificate('order must be a positive integer')
    if q > max_order:
        raise ResourceLimit('Requested order exceeds configured reference-checker budget')
    field = RealEmbedding(data.get('embedding'))
    rawjets, rawbase = data.get('jets'), data.get('base')
    if not isinstance(rawjets, list) or not 1 <= len(rawjets) <= 64:
        raise InvalidCertificate('Supply 1..64 physical parameter jets')
    n = len(rawjets)
    if not isinstance(rawbase, list) or len(rawbase) != n:
        raise InvalidCertificate('Base tuple must have the same variable count')
    jets: list[TP] = []
    margins = []
    for raw, base in zip(rawjets, rawbase):
        if not isinstance(raw, dict):
            raise InvalidCertificate('Each jet is an object from t-degree strings to coefficient lists')
        jet: TP = {}
        for k, v in raw.items():
            if type(k) is not str or not k.isdigit() or str(int(k)) != k:
                raise InvalidCertificate('Jet degrees must be canonical nonnegative integer strings')
            k = int(k)
            if k >= q:
                raise InvalidCertificate('Jet entries must have degree strictly below certificate order')
            jet[k] = field.element(v)
        if field.sign(field.plus(jet.get(0, ZERO), neg(field.element(base)))):
            raise InvalidCertificate('Jet does not start at the declared fixed base tuple')
        r0 = positive_order(jet, field)
        upper = tpadd({0: ONE}, {k: neg(v) for k,v in jet.items()}, field)
        r1 = positive_order(upper, field)
        margins.append(max(r0, r1))
        jets.append(jet)
    rows = data.get('residuals')
    if not isinstance(rows, list) or not rows or len(rows) > 10000:
        raise InvalidCertificate('Supply the nonempty full residual vector')
    polys = [parse_mp(p, n, field) for p in rows]
    degree = max([2]+[sum(ex) for p in polys for _, ex in p])
    exponent = degree*(6*degree-3)**(n-1)
    r = max(margins)
    if q <= r*exponent:
        raise InvalidCertificate('Strict residual-to-positivity threshold q > r R is not met')
    for i, p in enumerate(polys):
        rem = compose(p, jets, field, q)
        if rem:
            raise InvalidCertificate(f'Residual row {i} has nonzero coefficient at t^{min(rem)}, below claimed order {q}')
    h = compose(parse_mp(data.get('distinguishing'), n, field), jets, field, q)
    if not h:
        raise InvalidCertificate('No nonzero distinguishing coefficient below the required order')
    s = min(h)
    if q <= exponent*max(r, s):
        raise InvalidCertificate('Strict residual-to-distinction threshold q > s R is not met')
    return {
        'verdict': 'VERIFIED_POLYNOMIAL_JET',
        'variables': n, 'residual_rows': len(polys), 'degree_bound': degree,
        'error_exponent': str(exponent), 'residual_order_at_least': q,
        'margin_order': r, 'distinction_order': s,
        'strict_threshold': str(exponent*max(r,s)),
        'physical_source_binding_verified': False,
        'legal_observation_binding_verified': False,
        'g4_master_established': False,
        'theorem_status': 'hand-derived, not Lean/Rust verified',
    }

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--max-order', type=int, default=256)
    args = ap.parse_args()
    raw = args.certificate.read_bytes()
    try:
        data = json.loads(raw)
        result = verify(data, args.max_order)
        status = 0
    except ResourceLimit as exc:
        result, status = {'verdict':'INCONCLUSIVE_RESOURCE', 'reason':str(exc)}, 2
    except (InvalidCertificate, json.JSONDecodeError, TypeError, KeyError, ZeroDivisionError) as exc:
        result, status = {'verdict':'CERTIFICATE_NOT_VERIFIED', 'reason':str(exc)}, 1
    result.update({'certificate_sha256':hashlib.sha256(raw).hexdigest(),
                   'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   'scope':'Polynomial certificate only; not an admitted-source or solver verdict'})
    print(json.dumps(result, indent=2, sort_keys=True))
    return status

if __name__ == '__main__':
    raise SystemExit(main())
