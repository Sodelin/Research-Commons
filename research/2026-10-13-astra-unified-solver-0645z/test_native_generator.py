#!/usr/bin/env python3
"""Bounded exact Python/native singleton acquisition and checker compatibility.

No numerical fitting or target source is supplied. A certificate is emitted only
from exactly three observed moments and is checked by both old and new native
checkers, plus the existing Python arithmetic checker and exact wire comparison.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess

from certificates import Refused, checked, generate_singleton, wire

MODE = 'COMMON_GENERATE_SINGLETON_V1'
OLD_BINARY_SHA = '1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805'


def cases():
    values = sorted({Fraction(p, q) for q in range(1, 20) for p in range(1, q+1)})
    values += [Fraction(1, 1 << 42), Fraction((1 << 42)-1, 1 << 42),
               Fraction((1 << 42)+1, (1 << 42)+2), Fraction(6000000000000, 6000000000001)]
    for a in values:
        yield 'exact-'+str(a), ['1', str(a), str(a**3)]
    yield 'equivalent-tokens-retained', ['2/2', '2/4', '3/24']
    yield 'reduced-before-bit-cap', [f'{1 << 128}/{1 << 128}', '1/2', '1/8']
    for name, moments in [
        ('zero-survival', ['1', '0', '0']), ('negative-zero-survival', ['1', '-0', '-0']),
        ('negative-survival', ['1', '-1/2', '-1/8']), ('outside-survival', ['1', '2', '8']),
        ('unnormalized', ['0', '1/2', '1/8']), ('unsupported-cubic', ['1', '1/2', '1/7']),
        ('input-cube-bit-cap', ['1', str(Fraction(1, 1 << 43)), str(Fraction(1, 1 << 129))]),
        ('input-numerator-cap', ['1', str(1 << 128), '1']),
        ('unsupported-negative-moment', ['1', '1/2', '-1/8']),
    ]:
        yield name, moments
    for token in ['0.5', '1e-1', '+1', '01', '1/02', '1/-2', '1/+2', '1/0',
                  '1/2/3', '--1', '-', 'nan', 'inf', '١', '1'*81]:
        yield 'malformed-'+token, ['1', token, '1/8']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--previous-binary', type=Path, required=True)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve()
    previous = args.previous_binary.resolve()
    if args.report.exists():
        raise ValueError('report path must be absent')
    if hashlib.sha256(previous.read_bytes()).hexdigest() != OLD_BINARY_SHA:
        raise ValueError('prior checker binary changed; preserve the accepted baseline')
    records = []

    def execute(path, raw):
        return subprocess.run([str(path)], input=raw, capture_output=True, timeout=5)

    def retain(row):
        records.append(row)
        # Preserve exact inputs/outputs incrementally even if a later case fails.
        args.report.write_text(json.dumps(records, indent=2, sort_keys=True)+'\n')
        if not row['passed']:
            raise AssertionError(json.dumps(row, sort_keys=True))

    for name, moments in cases():
        raw = (MODE+' '+' '.join(moments)+'\n').encode()
        try:
            expected = generate_singleton(moments)
        except Refused:
            expected = {'status': 'REFUSED'}
        native = execute(binary, raw)
        row = dict(name=name, raw_utf8=raw.decode(), python_status=expected['status'],
                   native_exit_code=native.returncode, native_stdout=native.stdout.decode(errors='replace'),
                   native_stderr=native.stderr.decode(errors='replace'))
        if expected['status'] == 'GENERATED_AND_CHECKED':
            checked(expected['certificate'])
            expected_wire = wire(expected['certificate'])
            expected_output = ('GENERATED_AND_CHECKED support_cap=2 source_existence=false\n'+expected_wire).encode()
            emitted = native.stdout.split(b'\n', 1)[1] if b'\n' in native.stdout else b''
            new_check = execute(binary, emitted)
            old_check = execute(previous, emitted)
            check_output = b'CHECKED_RATIONAL_CERTIFICATE support_cap=2 source_existence=false\n'
            row.update(new_checker_exit=new_check.returncode, old_checker_exit=old_check.returncode,
                       new_checker_stdout=new_check.stdout.decode(errors='replace'),
                       old_checker_stdout=old_check.stdout.decode(errors='replace'),
                       emitted_wire_sha256=hashlib.sha256(emitted).hexdigest(),
                       passed=(native.returncode == 0 and native.stdout == expected_output and not native.stderr
                               and new_check.returncode == old_check.returncode == 0
                               and new_check.stdout == old_check.stdout == check_output
                               and not new_check.stderr and not old_check.stderr))
        elif expected['status'] == 'UNKNOWN':
            reason = ('generated_certificate_exceeds_supported_exact_language'
                      if expected['reason'] == 'generated certificate exceeds supported exact language'
                      else 'supplied_moments_do_not_fit_singleton_generator')
            row['passed'] = (native.returncode == 2 and not native.stderr and native.stdout ==
                             ('UNKNOWN '+reason+' source_existence=false\n').encode())
        else:
            row['passed'] = native.returncode == 1 and not native.stdout and native.stderr.startswith(b'REFUSED ')
        retain(row)
    for i, raw in enumerate([
        (MODE+'\n').encode(), (MODE+' 1 1/2\n').encode(),
        (MODE+' 1 1/2 1/8 extra\n').encode(), (MODE+' 1 1 / 2 1/8\n').encode(),
        b'COMMON_GENERATE_SINGLETON_V2 1 1/2 1/8\n',
        (MODE+' 1 1/2 1/8\x00\n').encode(),
        (MODE+' 1 1/2 1/8\n').encode()+b'\xff',
        (MODE+' '+' '*(262145-len(MODE)-1)).encode(),
    ]):
        native = execute(binary, raw)
        retain(dict(name='malformed-frame-'+str(i), input_bytes=len(raw),
                    input_sha256=hashlib.sha256(raw).hexdigest(), python_status='REFUSED_FRAME',
                    native_exit_code=native.returncode,
                    native_stdout=native.stdout.decode(errors='replace'),
                    native_stderr=native.stderr.decode(errors='replace'),
                    passed=native.returncode == 1 and not native.stdout and native.stderr.startswith(b'REFUSED ')))
    counts = {status: sum(row['python_status'] == status for row in records)
              for status in ['GENERATED_AND_CHECKED', 'UNKNOWN', 'REFUSED', 'REFUSED_FRAME']}
    print(json.dumps(dict(schema='native_singleton_generator_differential_v1',
                          binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                          preserved_previous_binary_sha256=OLD_BINARY_SHA, cases=len(records), counts=counts,
                          records_sha256=hashlib.sha256(args.report.read_bytes()).hexdigest(),
                          all_passed=all(row['passed'] for row in records),
                          source_existence_certified=False, universal_native_refinement_proved=False), sort_keys=True))


if __name__ == '__main__':
    main()
