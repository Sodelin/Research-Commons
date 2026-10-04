#!/usr/bin/env python3
"""Check stored universal certificates using only exact Python fractions.

No SymPy, Z3, QE output, expression evaluation or network is trusted here.
The source-image coverage/surjection is a separately pinned accepted provider.
"""
import argparse
import ast
import copy
from fractions import Fraction
import itertools
import json
from pathlib import Path

NAMES = ('sourceA0', 'sourceA1', 'sourceB0', 'sourceB1',
         'programmeWeight0', 'programmeWeight1')
ZERO = (0,) * len(NAMES)


def const(x):
    x = Fraction(x)
    return {ZERO: x} if x else {}


def add(a, b):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, Fraction(0)) + c
        if not out[m]:
            del out[m]
    return out


def scale(a, c):
    return {m: v * c for m, v in a.items() if v * c}


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            k = tuple(x + y for x, y in zip(m, n))
            out[k] = out.get(k, Fraction(0)) + c * d
    return {m: c for m, c in out.items() if c}


def variable(name):
    if name not in NAMES:
        raise ValueError('Unrecognized polynomial variable')
    m = list(ZERO)
    m[NAMES.index(name)] = 1
    return {tuple(m): Fraction(1)}


def parse(text):
    def go(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return const(node.value)
        if isinstance(node, ast.Name):
            return variable(node.id)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return scale(go(node.operand), -1)
        if isinstance(node, ast.BinOp):
            a, b = go(node.left), go(node.right)
            if isinstance(node.op, ast.Add):
                return add(a, b)
            if isinstance(node.op, ast.Sub):
                return add(a, scale(b, -1))
            if isinstance(node.op, ast.Mult):
                return mul(a, b)
            if isinstance(node.op, ast.Div) and set(b) == {ZERO}:
                return scale(a, 1 / b[ZERO])
        raise ValueError('Only rational polynomial arithmetic is permitted')
    return go(ast.parse(text, mode='eval').body)


def expected_response(image, source_names):
    out = [const(0) for _ in range(3)]
    for target, s_name, w_name in zip(image, source_names, NAMES[4:]):
        s, w = variable(s_name), variable(w_name)
        for k in range(3):
            row = add(const(1), scale(s, Fraction(-2, 3))) if k == target else scale(s, Fraction(1, 3))
            out[k] = add(out[k], mul(w, row))
    return out


def check(receipt):
    if receipt.get('schema') != 'source-admitted-last-call-33-pair-all-interior-experiment-v1':
        raise ValueError('Wrong receipt schema')
    if receipt.get('source_provider_manifest_sha256') != '3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1':
        raise ValueError('Source provider pin changed')
    if receipt.get('source_image_certificate_sha256') != '2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8':
        raise ValueError('Joint source image pin changed')
    if receipt.get('history_in_this_experiment') != []:
        raise ValueError('This certificate has no historical observations')
    if receipt.get('domain') != {'source_parameters': '0<sourceA0,sourceA1,sourceB0,sourceB1<1',
                                 'programme_weights': 'programmeWeight0>0,programmeWeight1>0,sum=1'}:
        raise ValueError('The certified strict domain changed')
    expected = {(a, b) for a, b in itertools.combinations(itertools.product(range(3), repeat=2), 2) if set(a) != set(b)}
    seen = set()
    for cert in receipt['exact_positive_identity_certificates']:
        a, b = tuple(cert['source_imageA']), tuple(cert['source_imageB'])
        if (a, b) not in expected or (a, b) in seen:
            raise ValueError('Unexpected or duplicate source pair')
        seen.add((a, b))
        left, right = expected_response(a, NAMES[:2]), expected_response(b, NAMES[2:4])
        equations = [add(p, scale(q, -1)) for p, q in zip(left, right)]
        if len(cert['equations']) != 3 or any(parse(t) != p for t, p in zip(cert['equations'], equations)):
            raise ValueError('Stored equation is not the actual joint response difference')
        indices = cert['coordinate_indices']
        if len(indices) != 2 or any(type(i) is not int or i not in range(3) for i in indices):
            raise ValueError('Invalid coordinate difference')
        sign = cert['orientation']
        if type(sign) is not int or sign not in (-1, 1):
            raise ValueError('Invalid orientation')
        terms = cert['positive_products']
        if not terms:
            raise ValueError('Strict contradiction requires a nonempty positive sum')
        positive_sum = const(0)
        for weight_text, bound_text in terms:
            w, bound = parse(weight_text), parse(bound_text)
            if w not in [variable(n) for n in NAMES[4:]]:
                raise ValueError('Weight is not strictly positive on this domain')
            if bound not in [add(const(1), scale(variable(n), -1)) for n in NAMES[:4]]:
                raise ValueError('Source factor is not strictly positive on this domain')
            positive_sum = add(positive_sum, mul(w, bound))
        difference = scale(add(equations[indices[0]], scale(equations[indices[1]], -1)), sign)
        if difference != positive_sum:
            raise ValueError('Exact rational polynomial identity failed')
    if seen != expected or len(seen) != 33:
        raise ValueError('Complete different-target source pair coverage failed')
    return {'status': 'PASS_EXACT_RATIONAL_IDENTITIES', 'covered_different_target_pairs': len(seen),
            'claim': 'Under the declared open source cube and positive action weights, no different-target pair has equal responses',
            'backend_trusted': False, 'source_coverage': 'separately pinned accepted joint source-image provider'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('receipt', nargs='?', default=str(Path(__file__).with_name('ALL-INTERIOR-EXPERIMENT-RECEIPT.json')))
    ap.add_argument('--tamper-controls', action='store_true')
    args = ap.parse_args()
    receipt = json.loads(Path(args.receipt).read_text())
    result = check(receipt)
    if args.tamper_controls:
        changed = []
        bad = copy.deepcopy(receipt); bad['exact_positive_identity_certificates'].pop(); changed.append(bad)
        bad = copy.deepcopy(receipt); bad['exact_positive_identity_certificates'][0]['orientation'] *= -1; changed.append(bad)
        bad = copy.deepcopy(receipt); bad['exact_positive_identity_certificates'][0]['positive_products'][0][1] = '1 + sourceB1'; changed.append(bad)
        bad = copy.deepcopy(receipt); bad['exact_positive_identity_certificates'][0]['equations'][0] = '0'; changed.append(bad)
        for bad in changed:
            try:
                check(bad)
            except (ValueError, KeyError):
                continue
            raise RuntimeError('Tampered certificate was accepted')
        result['tamper_rejections'] = len(changed)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
