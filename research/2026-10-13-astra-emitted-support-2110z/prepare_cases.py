#!/usr/bin/env python3
"""Preserve a bounded literal proof corpus, without invoking Lean."""
from fractions import Fraction
import json
from pathlib import Path

import emit_support

HERE = Path(__file__).resolve().parent


def examples():
    api, _ = emit_support.dependencies()
    cases = {}
    for name, a in [('quarter', Fraction(1, 4)), ('half', Fraction(1, 2)), ('one', Fraction(1))]:
        cases[name] = api.generate_singleton(list(map(str, [Fraction(1), a, a**3])))['certificate']
    cases['endpoint-linear'] = dict(schema='common_sparse_certificate_v1', level=2,
        coefficients=['1', '-1'], moments=['1', '1'],
        nonnegative_terms=[dict(weight='1', left=0, right=1, square=['1'])])
    cases['zero-constant'] = dict(schema='common_sparse_certificate_v1', level=3,
        coefficients=['0', '1', '-1'], moments=['1', '1', '1'],
        nonnegative_terms=[dict(weight='1', left=1, right=1, square=['1']),
                           dict(weight='1', left=0, right=1, square=['0', '1'])])
    cases['level-four-square'] = dict(schema='common_sparse_certificate_v1', level=4,
        coefficients=['1/64', '0', '-1/4', '1'], moments=['1', '1/2', '1/8', '1/64'],
        nonnegative_terms=[dict(weight='1', left=0, right=0, square=['-1/8', '0', '0', '1'])])
    cases['level-eight-padding'] = dict(schema='common_sparse_certificate_v1', level=8,
        coefficients=['1/4', '-3/4', '1', '0', '0', '0', '0', '0'],
        moments=[str(Fraction(1, 2) ** (k * (k - 1) // 2)) for k in range(1, 9)],
        nonnegative_terms=cases['half']['nonnegative_terms'])
    return cases


def main():
    out = HERE / 'cases'
    out.mkdir(exist_ok=False)
    ledger = []
    for name, certificate in examples().items():
        certificate_path = out / (name + '.json')
        certificate_path.write_text(json.dumps(certificate, indent=2) + '\n')
        manifest = emit_support.emit(certificate, out / name)
        ledger.append(dict(name=name, certificate_path=certificate_path.name,
                           certificate_file_sha256=emit_support.sha(certificate_path),
                           emission=manifest))
    (out / 'CASE-LEDGER.json').write_text(json.dumps(dict(cases=ledger,
        compiled=False, source_existence_certified=False), indent=2) + '\n')
    print(json.dumps(dict(status='PREPARED_LITERAL_PROOFS', cases=len(ledger), compiled=False)))


if __name__ == '__main__':
    main()
