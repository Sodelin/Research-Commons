#!/usr/bin/env python3
"""Check this literal corpus against the previously built exact native checker."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

import emit_support

BINARY_SHA = '1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve()
    if emit_support.sha(binary) != BINARY_SHA:
        raise ValueError('previously executed native checker identity differs')
    api, _ = emit_support.dependencies()
    cases = emit_support.HERE / 'cases'
    ledger_path = cases / 'CASE-LEDGER.json'
    ledger = json.loads(ledger_path.read_text())
    results = []
    for row in ledger['cases']:
        certificate_path = cases / row['certificate_path']
        if emit_support.sha(certificate_path) != row['certificate_file_sha256']:
            raise ValueError('literal input changed')
        certificate = api.loads(certificate_path.read_bytes())
        ident, base, support, interface = emit_support.render(certificate)
        emission = json.loads((cases / row['name'] / 'EMISSION.json').read_text())
        if emission != row['emission'] or emission['mathematical_interface'] != interface:
            raise ValueError('literal interface or emission changed')
        for filename, expected in [('Certificate_' + ident + '.lean', base),
                                   ('Support_' + ident + '.lean', support)]:
            path = cases / row['name'] / filename
            file_record = emission['files'][filename]
            if (path.read_text() != expected or emit_support.sha(path) != file_record['sha256']
                    or path.stat().st_size != file_record['bytes']):
                raise ValueError('generated source bytes changed')
        wire = api.wire(certificate).encode()
        completed = subprocess.run([str(binary)], input=wire, capture_output=True, timeout=2)
        expected = ('CHECKED_RATIONAL_CERTIFICATE support_cap=' + str(interface['support_cap']) +
                    ' source_existence=false\n').encode()
        result = dict(name=row['name'], certificate_sha256=ident,
                      wire_sha256=hashlib.sha256(wire).hexdigest(),
                      source_files=emission['files'], support_cap=interface['support_cap'],
                      exit_code=completed.returncode, stdout=completed.stdout.decode(),
                      stderr=completed.stderr.decode(),
                      passed=completed.returncode == 0 and completed.stdout == expected and not completed.stderr,
                      compiled=False)
        results.append(result)
        if not result['passed']:
            raise AssertionError(json.dumps(result))
    print(json.dumps(dict(schema='astra_literal_support_native_corpus_v1',
        binary_sha256=BINARY_SHA, case_ledger_sha256=emit_support.sha(ledger_path),
        checker_source='2026-10-13-astra-unified-solver-0645z/rust',
        checker_execution='authenticated existing executable; no native compilation in this increment',
        cases=results, all_passed=all(row['passed'] for row in results),
        lean_compiled=False, physical_representative_certified=False,
        universal_native_correctness_proved=False), indent=2))


if __name__ == '__main__':
    main()
