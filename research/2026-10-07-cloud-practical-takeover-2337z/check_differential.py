"""New bounded language-port fixtures; no JC provider or archived-data replay."""
import argparse
import hashlib
import json
import subprocess
from fractions import Fraction
from pathlib import Path
from types import ModuleType

REFERENCE = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py'
REFERENCE_SHA = '4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4'


def controls(root, binary):
    raw = (root / REFERENCE).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == REFERENCE_SHA
    reference = ModuleType('frozen_count_reference')
    exec(compile(raw, REFERENCE, 'exec', dont_inherit=True), reference.__dict__)
    results = []
    # Different fixtures from the historical 24 controls, with complete output.
    cases = [('2/3', '3/7'), ('7/3', '1/37'), ('13/4', '3/256'),
             ('17/5', '1/1024'), ('3/2', '1/37'), ('0002/0003', '2/14'),
             ('-0', '1/9'), ('1', '2/3'), ('2', '4/11')]
    for a, eps in cases:
        expected = reference.certify(Fraction(a), Fraction(eps), max_steps=128)
        assert expected['status'] == 'CERTIFIED'
        for limit, weights in [(128, False), (128, True),
                               (expected['K'], True), (expected['K'] + 1, True)]:
            want = reference.certify(Fraction(a), Fraction(eps), max_steps=limit)
            if weights and want['status'] == 'CERTIFIED':
                want['weights'] = [str(q) for q in reference.weights(Fraction(a), want['K'])]
            arguments = [a, eps, '--max-steps', str(limit)] + (['--weights'] if weights else [])
            run = subprocess.run([str(binary), *arguments], capture_output=True, text=True, timeout=3)
            assert run.returncode == 0 and not run.stderr, (arguments, run.returncode, run.stderr)
            got = json.loads(run.stdout)
            assert got == want, (arguments, got, want)
            results.append({'arguments': arguments, 'exit': run.returncode, 'expected': want, 'actual': got})
    # Zero inspection, uint64 endpoint at a zero-cost immediately certified case,
    # unlimited-zero case, invalid syntax/domain and malformed CLI controls.
    extras = [('0', '1/3', '--max-steps', '0'),
              ('0', '1/3', '--max-steps', str(2**64 - 1)), ('0', '1/3', '--weights')]
    for arguments in extras:
        limit = None if '--max-steps' not in arguments else int(arguments[-1])
        want = reference.certify(Fraction(arguments[0]), Fraction(arguments[1]), max_steps=limit)
        if '--weights' in arguments:
            want['weights'] = [str(q) for q in reference.weights(Fraction(arguments[0]), want['K'])]
        run = subprocess.run([str(binary), *arguments], capture_output=True, text=True, timeout=3)
        assert run.returncode == 0 and not run.stderr and json.loads(run.stdout) == want
        results.append({'arguments': list(arguments), 'exit': 0, 'expected': want, 'actual': json.loads(run.stdout)})
    invalid = [('-1', '1/2'), ('1', '0'), ('1', '1'), ('1', '-1/2'),
               ('1/0', '1/2'), ('1/-2', '1/2'), ('+1', '1/2'), (' 1', '1/2'),
               ('1 ', '1/2'), ('1.0', '1/2'), ('1e-1000000000', '1/2'),
               ('1/2/3', '1/2'), ('', '1/2'), ('1\u00b2', '1/2'),
               ('9'*159, '1/2'), (str(2**256), '1/2'), ('1/'+str(2**256), '1/2'),
               ('1', '1/2', '--max-steps', str(2**64)),
               ('1', '1/2', '--max-steps', '-1'), ('1', '1/2', '--max-steps', ' 1'),
               ('1', '1/2', '--weights', '--weights'), ('1', '1/2', '--unknown')]
    for arguments in invalid:
        run = subprocess.run([str(binary), *arguments], capture_output=True, text=True, timeout=3)
        got = json.loads(run.stdout)
        assert run.returncode == 2 and not run.stderr and got['status'] == 'INVALID_INPUT'
        results.append({'arguments': list(arguments), 'exit': 2, 'actual': got})
    return {'status': 'PASS', 'reference_sha256': REFERENCE_SHA,
            'complete_output_differentials': 39, 'invalid_inputs': len(invalid),
            'results': results, 'scope': 'scalar count ABI/CLI only; no JC/source/statistical inference'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--binary', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(controls(args.root, args.binary), indent=2, sort_keys=True))
