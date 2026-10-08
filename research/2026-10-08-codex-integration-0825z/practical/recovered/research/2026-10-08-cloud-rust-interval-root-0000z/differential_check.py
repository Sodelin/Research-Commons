#!/usr/bin/env python3
"""Bounded exact differential evidence for Dot's Rust interval probe.

Uses the unchanged, hash-pinned Python reference buffers and exact Fraction
endpoints. Runs ONE release-probe subprocess, retaining every input/output and
refusal/call counter. No solver, confidence, Lean, or speedup claim is made.
Contributor: Codex, delegated Cloud G6 differential harness author, 2026-10-08.
"""
from __future__ import annotations

import argparse
import collections
import datetime
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
import traceback
from types import ModuleType
import unicodedata

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / 'reports/cloud-differential'
DEFAULT_BINARY = Path('/workspace/cloud-practical-runtime/rust-interval-root-target/release/interval-probe')
BINARY_SHA = '1927426e00f8b0fc736954ef0fd3f449511b8c3054085e5298341985a2e0c4d0'
PINNED = {
    'reference/certified_forward.py': 'c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace',
    'reference/signed_receiver.py': '61db9997db84b925c6eff405744726e01dcec14d0090192e834f33a75aeafc1f',
    'src/lib.rs': 'bfe48152cd63b8abd6bb7257e986b50dec741ec351770c58b19272543b46c1d1',
    'src/main.rs': '7ae7cc17ed3fc79a2be9c75fb3f54e6e663a7365bcb1ef31866bade4e79dad70',
    'src/parse.rs': '471dca6bd05291811aa07d6440e3c5d3a6aec58a742a37d08a2008de5b1cad4e',
    'Cargo.lock': '551be9605ca2258dd60dbbc49e10aa8d95759866523e754b10feb4b51a7510ca',
    'Cargo.toml': 'ad120771a9f79c7880ceb5e66eca4814c819773ea0b7330263ca04cef5ba93c2',
}
PROVIDER = 'research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py'
DECIMAL_ZEROES = [
    0x30,0x660,0x6f0,0x7c0,0x966,0x9e6,0xa66,0xae6,0xb66,0xbe6,
    0xc66,0xce6,0xd66,0xde6,0xe50,0xed0,0xf20,0x1040,0x1090,0x17e0,
    0x1810,0x1946,0x19d0,0x1a80,0x1a90,0x1b50,0x1bb0,0x1c40,0x1c50,
    0xa620,0xa8d0,0xa900,0xa9d0,0xa9f0,0xaa50,0xabf0,0xff10,0x104a0,
    0x10d30,0x11066,0x110f0,0x11136,0x111d0,0x112f0,0x11450,0x114d0,
    0x11650,0x116c0,0x11730,0x118e0,0x11950,0x11c50,0x11d50,0x11da0,
    0x11f50,0x16a60,0x16ac0,0x16b50,0x1d7ce,0x1d7d8,0x1d7e2,0x1d7ec,
    0x1d7f6,0x1e140,0x1e2f0,0x1e4f0,0x1e950,0x1fbf0,
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


class ProbeError(Exception):
    """An adapter guard, distinct from a reference arithmetic refusal."""


def ascii_bigint(text: str) -> int:
    # Mirror num-bigint 0.4.6 BigInt::parse_bytes(base10): one optional sign,
    # a leading ASCII digit, then ASCII digits/ignored underscores. Rust's
    # probe q() permits this syntax; the separate kernel parsers do not.
    if re.fullmatch(r'[+-]?[0-9][0-9_]*', text) is None:
        raise ProbeError('PROBE_RATIONAL')
    neg = text.startswith('-')
    digits = text.lstrip('+-').replace('_', '')
    value = 0
    for i in range(0, len(digits), 9):
        part = digits[i:i+9]
        value = value * (10 ** len(part)) + int(part)
    return -value if neg else value


def probe_q(text: str) -> Fraction:
    parts = text.split('/')
    if len(parts) > 2 or len(text.encode('utf-8')) > 8192:
        raise ProbeError('PROBE_RATIONAL')
    n = ascii_bigint(parts[0])
    d = ascii_bigint(parts[1]) if len(parts) == 2 else 1
    if d == 0:
        raise ProbeError('PROBE_RATIONAL')
    return Fraction(n, d)


def probe_i(text: str) -> int:
    if re.fullmatch(r'[+-]?[0-9]+', text) is None:
        raise ProbeError('PROBE_INTEGER')
    value = int(text)
    if not -(1 << 31) <= value < (1 << 31):
        raise ProbeError('PROBE_INTEGER')
    return value


def load_exact(name: str, data: bytes, filename: Path) -> ModuleType:
    module = ModuleType(name)
    module.__file__ = str(filename)
    sys.modules[name] = module  # Required by the unchanged forward dataclass.
    exec(compile(data, str(filename), 'exec', dont_inherit=True), module.__dict__)
    return module


def pin_snapshot(binary: Path, staged: Path, frozen) -> dict:
    rows = {}
    for name, expected in PINNED.items():
        path = ROOT / name
        if path.is_symlink():
            raise RuntimeError('source symlink: ' + name)
        data = path.read_bytes()
        digest = sha(data)
        if digest != expected:
            raise RuntimeError('source identity mismatch: ' + name)
        rows[name] = {'sha256': digest, 'bytes': len(data)}
    for name in ('tests/core.rs', 'differential_check.py'):
        data = (ROOT / name).read_bytes()
        digest = sha(data)
        if digest != frozen['inputs'][name]['sha256']:
            raise RuntimeError('frozen identity mismatch: ' + name)
        rows[name] = {'sha256': digest, 'bytes': len(data)}
    if binary.is_symlink():
        raise RuntimeError('binary symlink')
    data = binary.read_bytes()
    if sha(data) != BINARY_SHA:
        raise RuntimeError('binary identity mismatch')
    rows['release_binary'] = {'sha256': sha(data), 'bytes': len(data), 'path': str(binary)}
    if staged.is_symlink():
        raise RuntimeError('staged provider symlink')
    data = staged.read_bytes()
    if sha(data) != PINNED['reference/certified_forward.py']:
        raise RuntimeError('staged provider identity mismatch')
    rows['staged_provider'] = {'sha256': sha(data), 'bytes': len(data), 'path': str(staged)}
    return rows


def corpus() -> list[dict]:
    cases = []

    def add(category: str, fields, label=''):
        line = '\t'.join(map(str, fields)) if not isinstance(fields, str) else fields
        cases.append({'id': f'{len(cases)+1:05d}', 'category': category,
                      'label': label, 'input_line': line})

    def f(op, a=('0', '0'), b=('0', '0'), scalar='0', bits=64, label=''):
        add('forward_' + op, ['f', op, *a, *b, scalar, bits], label)

    def r(op, a=('0', '0'), b=('0', '0'), scalar='0', precision=64,
          max_bits=256, budget=32, label=''):
        add('receiver_' + op, ['r', precision, max_bits, budget, op, *a, *b, scalar], label)

    small = [('-7/3', '-1/3'), ('-5/3', '2/3'), ('-1/7', '1/11'),
             ('0', '0'), ('1/3', '1/3'), ('1/3', '2/3'), ('1', '2'), ('2', '3')]
    wider = small + [('-1', '-1'), ('0', '1'), ('-2', '-1'),
                     ('-1/' + str(1 << 128), '1/' + str(1 << 128))]
    for a in wider:
        for b in wider:
            for op in ('add', 'sub', 'mul', 'intersects'):
                f(op, a, b)
        for op in ('new', 'neg', 'unit'):
            f(op, a)
        for bits in (0, 1, 2, 8, 64, 128, 192):
            f('dyadic', a, bits=bits)
        for scalar in ('-7/3', '-1', '0', '1/3', '2'):
            f('div', a, scalar=scalar)
        for scalar in ('-3', '-1/3', '0', '1/3', '1', '2', '3'):
            f('contains', a, scalar=scalar)
    for precision in (64, 128):
        for a in small:
            for b in small:
                for op in ('add', 'sub', 'mul', 'div', 'meet'):
                    r(op, a, b, precision=precision)
            for op in ('new', 'neg', 'abs', 'mixed'):
                r(op, a, precision=precision)
            for scalar in ('-7/3', '0', '1/3', '2'):
                for op in ('add_scalar', 'sub_scalar', 'mul_scalar', 'div_scalar',
                           'scalar_sub', 'scalar_div'):
                    r(op, a, scalar=scalar, precision=precision)
    # EXACT constructor order and pre-rounding/reduced-endpoint growth gates.
    for precision in (64, 128):
        for max_bits in (256, 257, 512, 4096, 16384):
            huge = str(1 << 255) + '/3'
            for op in ('new', 'neg', 'abs', 'add', 'sub', 'mul', 'div'):
                r(op, (huge, huge), ('1/3', '1/3'), precision=precision,
                  max_bits=max_bits, label='256-bit non-dyadic input; rounding may grow')
            raw = str(1 << 256)
            r('new', (raw, raw), precision=precision, max_bits=max_bits,
              label='257-bit reduced endpoint')
            r('new', (raw, '0'), precision=precision, max_bits=max_bits,
              label='EMPTY_INTERVAL precedes arithmetic-bit refusal')
    for precision in (63, 64, 128, 129):
        for max_bits in (255, 256, 16384, 16385):
            for budget in (-1, 0, 32, 33):
                r('new', precision=precision, max_bits=max_bits, budget=budget,
                  label='context configuration refusal ordering')
    for family in ('f', 'r'):
        def unary(op, a, b, scalar='garbage', bits='garbage'):
            if family == 'f':
                f(op, a, b, scalar=scalar, bits=bits, label='unused arguments still follow probe parsing')
            else:
                r(op, a, b, scalar=scalar, label='unused second interval parsed before unary operation')
        for op in ('new', 'neg'):
            for b in (('2', '1'), ('bad', '0'), ('1/0', '0'),
                      ('0', str(1 << 256)), ('0', '0')):
                unary(op, ('0', '1'), b)
    # Scalar exponential exact domains and range-reduction/shortcut edges.
    eps = Fraction(1, 1 << 12)
    for bits in (8, 64, 128, 192):
        values = [Fraction(0), Fraction(1, 1 << 256),
                  Fraction(1) - eps, Fraction(1), Fraction(1) + eps,
                  Fraction(2) - eps, Fraction(2), Fraction(2) + eps,
                  Fraction(4) - eps, Fraction(4), Fraction(4) + eps,
                  Fraction(8) - eps, Fraction(8), Fraction(8) + eps,
                  Fraction(bits) - eps, Fraction(bits), Fraction(bits) + eps,
                  Fraction(1 << 255)]
        for x in values:
            add('scalar_exp', ['exp', bits, str(x)])
    for bits in (-2147483648, -1, 0, 7, 193, 2147483647):
        for x in ('0', '1/3', '-1'):
            add('scalar_exp_domain', ['exp', bits, x])
    for bits in (8, 192):
        add('scalar_exp_domain', ['exp', bits, '-1/' + str(1 << 256)])
    for precision in (64, 128):
        for a in (('0', '0'), ('1/3', '1/3'), ('0', '1'), ('1', '2'),
                  ('-1/' + str(1 << 128), '0'), ('68', '132')):
            for budget in (0, 1, 2, 3, 4, 31, 32):
                r('exp', a, precision=precision, budget=budget)
        for a in (('0', '0'), ('1/3', '1/3'), ('0', '1')):
            for repetitions in (1, 2, 3, 15, 16, 17, 18):
                for budget in (0, 1, 2, 3, 4, 31, 32):
                    r('exp_repeat', a, scalar=repetitions,
                      precision=precision, budget=budget,
                      label='repeated same input; two calls per success, no cache discount')
        for repetitions in ('0', '-1', '19', 'bad', '2147483648'):
            r('exp_repeat', scalar=repetitions, precision=precision)
    # Distinct forward reduced-value / receiver RAW ASCII input policies.
    raw_strings = ['0', '-0', '1', '-1', '1/2', '-1/2', '1/01', '0/01',
                   '1/0', '0/0', '1/-2', '1/+2', '+1', '1_0', '1/2/3',
                   '', '-', ' 1', '1 ', '1.0', '1e0', '\x00', '²', 'Ⅻ',
                   '−1', '١/2', '1/1٢', '1/١٢', '１２/3', '0/1',
                   str((1 << 256) - 1), str(1 << 256),
                   str((1 << 256) - 1) + '/' + str((1 << 256) - 1),
                   str(1 << 256) + '/' + str(1 << 256),
                   '9' * 78 + '/' + '9' * 78,
                   '0/' + '9' * 78, '9' * 78, '0' * 78, '0' * 79,
                   '0' * 158, '0' * 159, '0' * 160, '0' * 161,
                   '-' + '0' * 77 + '/' + '0' * 77 + '1',
                   '-' + '0' * 78 + '/' + '0' * 77 + '1']
    for text in raw_strings:
        for mode in ('parse-r', 'parse-f'):
            add(mode, [mode, text], 'raw vs reduced contract and boundary grammar')
    for zero in DECIMAL_ZEROES:
        one, two = chr(zero+1), chr(zero+2)
        for mode, text in [('parse-f', one+two), ('parse-f', one+'/2'),
                           ('parse-f', '1/1'+two), ('parse-f', '1/'+one+two),
                           ('parse-r', one+two)]:
            add('unicode_' + mode, [mode, text], f'Unicode Nd zero U+{zero:04X}')
    # Probe transport is distinct from either kernel rational parser.
    for text in ('+001', '-001', '1_0', '1__0_', '-1_0/+2', '1/-2',
                 '1/0', '1/2/3', '-+1', '++1', '_1', '1 ', '١', '\x00',
                 '0' * 8192, '0' * 8193):
        f('new', (text, text), label='num-bigint transport grammar, not kernel parse-f')
    for bits in ('-1', '16384', '16385', '2147483647', '2147483648', '+00064', '1_0', 'bad'):
        f('dyadic', bits=bits, label='bounded zero avoids huge dyadic intermediate')
    for line in ('', 'unknown', 'f\tnew', 'r\t64', 'exp\t8', 'parse-f',
                 'f\tnope\t0\t0\t0\t0\t0\t64',
                 'r\t64\t256\t32\tnope\t0\t0\t0\t0\t0',
                 'exp\tx\t1', 'exp\t8\t1/0', 'x' * 131073,
                 'parse-f\t0\r'):
        add('protocol', line)
    assert len(cases) < 3500
    return cases


def expected(case, forward, receiver, receiver_root):
    line = case['input_line']
    math = None
    try:
        if line.endswith('\r'):
            line = line[:-1]  # std::io::Lines strips CR when the wire ends CRLF.
        if len(line.encode('utf-8')) > 131072:
            raise ProbeError('PROBE_LINE')
        v = line.split('\t')
        if len(v) == 2 and v[0] in ('parse-r', 'parse-f'):
            result = receiver.rational(v[1]) if v[0] == 'parse-r' else forward.rational(v[1])
            payload = [str(result)]
        elif len(v) == 3 and v[0] == 'exp':
            # Rust evaluates &q(v[2]) before i(v[1]) in this call expression.
            x = probe_q(v[2])
            bits = probe_i(v[1])
            result = forward.exp_neg(x, bits)
            payload = [str(result.lo), str(result.hi)]
        elif len(v) == 8 and v[0] == 'f':
            a = forward.Interval(probe_q(v[2]), probe_q(v[3]))
            b = forward.Interval(probe_q(v[4]), probe_q(v[5]))
            op = v[1]
            if op == 'new': result = a
            elif op == 'add': result = a + b
            elif op == 'sub': result = a - b
            elif op == 'neg': result = -a
            elif op == 'mul': result = a * b
            elif op == 'div': result = a / probe_q(v[6])
            elif op == 'unit': result = a.unit_intersection()
            elif op == 'dyadic':
                bits = probe_i(v[7])
                if bits < 0: raise ProbeError('negative shift count')
                if bits > 16384: raise ProbeError('PROBE_BITS')
                result = a.dyadic(bits)
            elif op == 'contains':
                result = a.contains(probe_q(v[6]))
            elif op == 'intersects':
                result = a.intersects(b)
            else: raise ProbeError('PROBE_OPERATION')
            payload = [('true' if result else 'false')] if isinstance(result, bool) else [str(result.lo), str(result.hi)]
        elif len(v) == 10 and v[0] == 'r':
            precision, max_bits, budget = probe_i(v[1]), probe_i(v[2]), probe_i(v[3])
            math = receiver.Arithmetic(receiver_root, precision, max_bits, budget)
            a = math.interval(probe_q(v[5]), probe_q(v[6]))
            b = math.interval(probe_q(v[7]), probe_q(v[8]))
            op = v[4]
            if op == 'new': result = a
            elif op == 'add': result = a + b
            elif op == 'sub': result = a - b
            elif op == 'neg': result = -a
            elif op == 'mul': result = a * b
            elif op == 'div': result = a / b
            elif op == 'meet': result = a.meet(b)
            elif op == 'add_scalar': result = a + probe_q(v[9])
            elif op == 'sub_scalar': result = a - probe_q(v[9])
            elif op == 'mul_scalar': result = a * probe_q(v[9])
            elif op == 'div_scalar': result = a / probe_q(v[9])
            elif op == 'scalar_sub': result = probe_q(v[9]) - a
            elif op == 'scalar_div': result = probe_q(v[9]) / a
            elif op == 'abs': result = a.abs_bound()
            elif op == 'exp': result = math.exp_neg(a)
            elif op == 'exp_repeat':
                n = probe_i(v[9])
                if not 1 <= n <= 18: raise ProbeError('PROBE_REPETITIONS')
                result = a
                for _ in range(n): result = math.exp_neg(a)
            elif op == 'mixed':
                other = receiver.Arithmetic(receiver_root, precision, max_bits, budget)
                result = a + other.interval(0)
            else: raise ProbeError('PROBE_OPERATION')
            payload = [str(result)] if isinstance(result, Fraction) else [str(result.lo), str(result.hi)]
        else:
            raise ProbeError('PROBE_SHAPE')
        calls = math.exp_calls if math is not None else 0
        return {'wire': '\t'.join(['OK', *payload, str(calls)]), 'status': 'OK',
                'classification': 'kernel_success', 'payload': payload, 'exp_calls': calls}
    except ProbeError as error:
        calls = math.exp_calls if math is not None else 0
        return {'wire': f'ERR\t{error}\t{calls}', 'status': 'ERR',
                'classification': 'protocol_guard', 'error': str(error), 'exp_calls': calls,
                'reference_exception': {'type': type(error).__name__, 'message': str(error)}}
    except (receiver.Refusal, forward.DomainError, forward.ResourceBound,
            ValueError, ZeroDivisionError, ArithmeticError) as error:
        calls = math.exp_calls if math is not None else 0
        message = 'ZERO_DIVISION' if isinstance(error, ZeroDivisionError) else str(error)
        return {'wire': f'ERR\t{message}\t{calls}', 'status': 'ERR',
                'classification': 'kernel_refusal', 'error': message, 'exp_calls': calls,
                'reference_exception': {'type': type(error).__name__, 'message': str(error)},
                'adapter_mapping': 'ZeroDivisionError->ZERO_DIVISION' if isinstance(error, ZeroDivisionError) else None}
    except Exception as error:
        return {'wire': None, 'status': 'REFERENCE_ADAPTER_ERROR',
                'classification': 'reference_adapter_error',
                'reference_exception': {'type': type(error).__name__, 'message': str(error),
                                        'traceback': traceback.format_exc()}}


def parse_actual(line):
    parts = line.split('\t')
    if len(parts) < 3 or parts[0] not in ('OK', 'ERR'):
        return {'status': 'OUTPUT_PROTOCOL_ERROR', 'wire': line}
    try:
        calls = int(parts[-1])
    except ValueError:
        return {'status': 'OUTPUT_PROTOCOL_ERROR', 'wire': line}
    if not 0 <= calls <= 32 or (parts[0] == 'ERR' and len(parts) != 3):
        return {'status': 'OUTPUT_PROTOCOL_ERROR', 'wire': line}
    return {'status': parts[0], 'wire': line, 'exp_calls': calls,
            'classification': ('kernel_success' if parts[0] == 'OK' else
              'protocol_guard' if parts[1].startswith('PROBE_') or parts[1] == 'negative shift count' else 'kernel_refusal'),
            ('error' if parts[0] == 'ERR' else 'payload'): parts[1] if parts[0] == 'ERR' else parts[1:-1]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=DEFAULT_BINARY)
    args = parser.parse_args()
    frozen = json.loads((REPORT / 'source-freeze.json').read_text())
    run = REPORT / 'run-once'
    run.mkdir(parents=True, exist_ok=True)
    # No repeated native execution or quiet overwrite of a previous result.
    with (run / 'EXECUTION-STARTED.json').open('x', encoding='utf-8') as f:
        json.dump({'started_utc': now(), 'command': [str(args.binary)],
                   'harness_sha256': sha(Path(__file__).read_bytes())}, f, indent=2)
        f.write('\n')
    receiver_root = REPORT / 'reference-root'
    staged = receiver_root / PROVIDER
    try:
        before = pin_snapshot(args.binary, staged, frozen)
    except Exception as error:
        dump(run / 'AUTHENTICATION-FAILURE.json', {'phase': 'before_native_execution',
             'type': type(error).__name__, 'message': str(error), 'native_executions': 0})
        return 2
    dump(run / 'inputs-before.json', before)
    forward = load_exact('_cloud_frozen_forward_reference',
                         (ROOT / 'reference/certified_forward.py').read_bytes(),
                         ROOT / 'reference/certified_forward.py')
    receiver = load_exact('_cloud_frozen_signed_receiver_reference',
                          (ROOT / 'reference/signed_receiver.py').read_bytes(),
                          ROOT / 'reference/signed_receiver.py')
    cases = corpus()
    expected_rows = [expected(case, forward, receiver, receiver_root) for case in cases]
    stdin = ''.join(case['input_line'] + '\n' for case in cases).encode('utf-8')
    (run / 'probe.stdin.tsv').write_bytes(stdin)
    dump(run / 'corpus-and-expected.json', [{'case': case, 'expected': row}
                                         for case, row in zip(cases, expected_rows)])
    # One bounded batch process. Every line has one corresponding result.
    timed_out = False
    try:
        result = subprocess.run([str(args.binary)], input=stdin, capture_output=True,
                                cwd=ROOT, timeout=120, check=False)
    except subprocess.TimeoutExpired as error:
        timed_out = True
        result = subprocess.CompletedProcess([str(args.binary)], None,
                                             error.stdout or b'', error.stderr or b'')
    (run / 'probe.stdout.tsv').write_bytes(result.stdout)
    (run / 'probe.stderr').write_bytes(result.stderr)
    actual_lines = result.stdout.decode('utf-8', errors='strict').splitlines()
    stderr_hash = sha(result.stderr)
    outputs = []
    for index, (case, want) in enumerate(zip(cases, expected_rows)):
        actual = parse_actual(actual_lines[index]) if index < len(actual_lines) else {'status': 'MISSING_OUTPUT', 'wire': None}
        matched = want['wire'] is not None and want['wire'] == actual['wire']
        outputs.append({'case': case, 'command': [str(args.binary)],
                        'stdin_exact': case['input_line'] + '\n',
                        'expected': want, 'actual': actual, 'exact_match': matched,
                        'process_exit': result.returncode, 'stderr_sha256': stderr_hash,
                        'binary_sha256': before['release_binary']['sha256']})
    dump(run / 'case-results.json', outputs)
    try:
        after = pin_snapshot(args.binary, staged, frozen)
    except Exception as error:
        after = {'authentication_error': {'type': type(error).__name__, 'message': str(error)}}
    dump(run / 'inputs-after.json', after)
    mismatches = [row for row in outputs if not row['exact_match']]
    dump(run / 'differences.json', mismatches)
    reference_errors = sum(row['expected']['classification'] == 'reference_adapter_error' for row in outputs)
    exact = len(outputs) - len(mismatches)
    status = 'EXACT_PASS' if (not mismatches and len(actual_lines) == len(cases)
                              and result.returncode == 0 and before == after) else 'DIFFERENCES_OR_EXECUTION_FAILURE'
    summary = {'schema': 'cloud-dot-exact-rust-interval-differential-v1',
               'status': status, 'finished_utc': now(), 'case_count': len(cases),
               'exact_matches': exact, 'differences': len(mismatches),
               'reference_adapter_errors': reference_errors,
               'output_line_count': len(actual_lines), 'extra_output_lines': actual_lines[len(cases):],
               'kernel_success_expected': sum(row['classification'] == 'kernel_success' for row in expected_rows),
               'kernel_refusal_expected': sum(row['classification'] == 'kernel_refusal' for row in expected_rows),
               'protocol_guards_expected': sum(row['classification'] == 'protocol_guard' for row in expected_rows),
               'categories': dict(sorted(collections.Counter(case['category'] for case in cases).items())),
               'process': {'command': [str(args.binary)], 'cwd': str(ROOT),
                           'exit_code': result.returncode, 'timed_out': timed_out, 'stdin_sha256': sha(stdin),
                           'stdout_sha256': sha(result.stdout), 'stderr_sha256': stderr_hash,
                           'stderr_bytes': len(result.stderr)},
               'binary_sha256': before['release_binary']['sha256'],
               'harness_invocation': [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
               'input_hashes_unchanged': before == after,
               'harness_sha256': before['differential_check.py']['sha256'],
               'python': sys.version, 'platform': platform.platform(),
               'unicode_version': unicodedata.unidata_version,
               'reference_execution': 'compile_exec_exact_hash_pinned_buffers; original Arithmetic authenticates staged provider',
               'reference_original_exp_cache_preserved': True,
               'extra_trust_or_cache_shortcut_added': False,
               'scalar_zero_division_adapter': 'original Python ZeroDivisionError maps to probe ZERO_DIVISION; raw exception preserved',
               'comparison': 'complete exact tab-separated endpoint/refusal/call-count output; no decimal tolerance',
               'limitations': ['Finite deterministic arithmetic/protocol corpus only',
                               'No full solver, model/source proof, confidence or Lean verification',
                               'No speedup or timing claim', 'No provider/control replay beyond this bounded kernel reference corpus']}
    dump(run / 'summary.json', summary)
    files = {}
    for path in sorted(run.iterdir()):
        if path.is_file() and path.name != 'SHA256SUMS.json':
            data = path.read_bytes()
            files[path.name] = {'sha256': sha(data), 'bytes': len(data)}
    dump(run / 'SHA256SUMS.json', files)
    print(json.dumps({key: summary[key] for key in ('status', 'case_count', 'exact_matches',
                                                  'differences', 'reference_adapter_errors',
                                                  'input_hashes_unchanged')}, sort_keys=True))
    return 0 if status == 'EXACT_PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
