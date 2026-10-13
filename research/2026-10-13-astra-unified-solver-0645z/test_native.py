#!/usr/bin/env python3
"""Deterministic process-level exact Python/Rust comparisons.

Run under guard.py with --binary PATH. This is finite differential evidence,
not a refinement theorem. The binary only receives the narrow certificate wire;
JSON IDs, joint configurations and source admission remain Python responsibilities.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess

from certificates import checked, wire
from test_certificates import valid_cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve()
    results = []

    def run(name, raw, expected_cap=None):
        payload = raw.encode() if isinstance(raw, str) else raw
        result = subprocess.run([str(binary)], input=payload, capture_output=True, timeout=5)
        if expected_cap is None:
            okay = (result.returncode == 1 and not result.stdout and
                    result.stderr.startswith(b'REFUSED '))
        else:
            expected = (f'CHECKED_RATIONAL_CERTIFICATE support_cap={expected_cap} '
                        'source_existence=false\n').encode()
            okay = result.returncode == 0 and result.stdout == expected and not result.stderr
        row = dict(name=name, input_sha256=hashlib.sha256(payload).hexdigest(),
                   expected_cap=expected_cap, exit_code=result.returncode,
                   stdout=result.stdout.decode(errors='replace'),
                   stderr=result.stderr.decode(errors='replace'), passed=okay)
        results.append(row)
        if not okay:
            print(json.dumps(row, sort_keys=True))
            raise AssertionError('differential or malformed-input mismatch: '+name)

    valid = 0
    for name, certificate in valid_cases():
        expected = checked(certificate)
        cap = expected['positive_support_cardinality_at_most']
        submitted = wire(certificate)
        run(name, submitted, cap)
        valid += 1
        tokens = submitted.split()
        # Increment only the sparse constant: the supplied square identity then
        # fails exactly, independently of whether these moments admit a source.
        tokens[2] = str(Fraction(tokens[2])+1)
        run(name+'/false-identity', ' '.join(tokens)+'\n')
        run(name+'/trailing-token', submitted+'extra\n')
    base = wire(next(iter(valid_cases()))[1])
    for i, raw in enumerate([
        '', 'COMMON_CERT_V0 1', base.replace('COMMON_CERT_V1', 'COMMON_CERT_V2'),
        base.replace(' 2 ', ' 0 ', 1), base.replace(' 2 ', ' 9 ', 1),
        base.replace(' 2 ', ' 02 ', 1), base.replace(' 2 ', ' +2 ', 1),
        base.replace(' 2 ', ' 184467440737095516160 ', 1),
        base.replace(' 1 ', ' 01 ', 1), base.replace(' 1 ', ' 1.0 ', 1),
        base.replace(' 1 ', ' 1/0 ', 1), base.replace(' 1 ', ' 1/+2 ', 1),
        base.replace(' 1 ', ' 1/02 ', 1), base.replace(' 1 ', ' ١ ', 1),
        base.replace(' 1 ', ' '+str(1 << 128)+' ', 1),
        base.replace(' 1 ', ' '+'1'*81+' ', 1),
        base.rsplit(' ', 1)[0], base.encode()+b'\xff', b' '*262145,
        base.replace(' ', '\x00', 1),
    ]):
        run(f'malformed-wire-{i}', raw)
    # Rational-equivalent noncanonical *fraction reduction* is accepted in both
    # implementations; signs/leading-zero grammar remain restricted.
    run('reduced-fraction-over-raw-bit-cap',
        base.replace(' 1 ', f' {1 << 128}/{1 << 128} ', 1), 1)
    run('ascii-whitespace', '\t\r\n'.join(base.split())+'\n', 1)
    report = dict(schema='common_certificate_differential_v1',
                  binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  valid_generated_cases=valid, accepted=sum(r['expected_cap'] is not None for r in results),
                  refused=sum(r['expected_cap'] is None for r in results),
                  total=len(results), all_passed=all(r['passed'] for r in results),
                  exact_arithmetic=True, source_existence_certified=False,
                  universal_native_correctness_proved=False,
                  corpus_and_results_sha256=hashlib.sha256(json.dumps(results, sort_keys=True).encode()).hexdigest())
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
