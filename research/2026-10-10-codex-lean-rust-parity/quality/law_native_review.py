#!/usr/bin/env python3
"""Check native LAW parity against direct three-sample formulas and cap cases."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sympy as sp
from law_analytic_oracle import no_bc_merger

PACKET = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def request(edges, leaves, hybrid, samples, mode, caps):
    ns, nt, nh = caps
    lines = [f'RC1 LAW 5 {len(edges)} {len(leaves)} {len(hybrid)} {len(samples)} {ns} {nt} {nh}',
             f'MECHANISM {mode}', 'ROOT 0']
    lines += [f'EDGE {i} {s} {t}' for i, (s, t) in enumerate(edges)]
    lines += [f'LEAF {i} {v}' for i, v in enumerate(leaves)]
    lines += [f'HYBRID {i} {v} {a} {b}' for i, (v, a, b) in enumerate(hybrid)]
    lines += [f'SAMPLE {i} {taxon}' for i, taxon in enumerate(samples)]
    return ('\n'.join(lines) + '\n').encode('ascii')


def polynomial(expression, variables):
    return {tuple(exponents): Fraction(int(coefficient.p), int(coefficient.q))
            for exponents, coefficient in sp.Poly(sp.expand(expression), *variables).terms()
            if coefficient != 0}


def fixtures():
    ordinary = ([(0, 1), (0, 2), (2, 3), (2, 4)], [1, 3, 4], [])
    parallel = ([(0, 1), (0, 2), (2, 3), (2, 3), (3, 4)], [1, 4], [(3, 2, 3)])
    caps = (4096, 65536, 4096)
    cases = []
    for name, graph in [('ordinary', ordinary), ('parallel', parallel),
                        ('parallel-reversed', (parallel[0], parallel[1], [(3, 3, 2)]))]:
        edges, leaves, hybrids = graph
        variables = list(sp.symbols(f'x0:{len(edges)}')) + list(sp.symbols(f'g0:{len(hybrids)}'))
        for mode in ('COMMON', 'INDEPENDENT'):
            samples = [0, 1, 2] if name == 'ordinary' else [0, 1, 1]
            if name == 'ordinary':
                d = variables[1]
            else:
                x1, x2, x3, x4, g = variables[1], variables[2], variables[3], variables[4], variables[5]
                if name.endswith('reversed'):
                    x2, x3 = x3, x2
                d = no_bc_merger(mode.lower(), x1, x2, x3, x4, g)
            expected = {'(0,(1,2))': polynomial(1 - sp.Rational(2, 3) * d, variables),
                        '((0,1),2)': polynomial(d / 3, variables),
                        '((0,2),1)': polynomial(d / 3, variables)}
            cases.append((name + '-' + mode, request(*graph, samples, mode, caps), expected, len(variables), None))
    for name, graph in [('ordinary-single', ordinary), ('parallel-unsampled-hybrid', parallel)]:
        dimension = len(graph[0]) + len(graph[2])
        for mode in ('COMMON', 'INDEPENDENT'):
            cases.append((name + '-' + mode, request(*graph, [0], mode, caps),
                          {'0': {(0,) * dimension: Fraction(1)}}, dimension, None))
    for label, cap in [('STATE', (0, 65536, 4096)), ('TERM', (4096, 0, 4096)), ('HISTORY', (4096, 65536, 0))]:
        cases.append(('zero-' + label, request(*ordinary, [0, 1, 2], 'COMMON', cap), None, 4, label))
    cases.append(('empty-COMMON-raw-state-cap', request(*parallel, [0], 'COMMON', (1, 65536, 4096)), None, 6, 'STATE'))
    cases.append(('empty-INDEPENDENT-one-route', request(*parallel, [0], 'INDEPENDENT', (1, 65536, 4096)),
                  {'0': {(0,) * 6: Fraction(1)}}, 6, None))
    return cases


def parse_table(lines, position, tag, entry_tag, dimension):
    header = lines[position].split(' ')
    if len(header) != 2 or header[0] != tag:
        raise ValueError('Missing ' + tag)
    count = int(header[1])
    position += 1
    table, keys = {}, []
    for _ in range(count):
        fields = lines[position].split(' ')
        if len(fields) != 3 or fields[0] != entry_tag:
            raise ValueError('Missing ' + entry_tag)
        key, terms = fields[1], int(fields[2])
        keys.append(key)
        position += 1
        coefficients, monomials = {}, []
        for _ in range(terms):
            fields = lines[position].split(' ')
            if len(fields) != dimension + 2 or fields[0] != 'TERM':
                raise ValueError('Bad term dimension')
            coefficient = Fraction(fields[1])
            if fields[1] != f'{coefficient.numerator}/{coefficient.denominator}' or not coefficient:
                raise ValueError('Noncanonical or zero coefficient')
            exponents = tuple(int(value) for value in fields[2:])
            if any(str(value) != token or value < 0 for value, token in zip(exponents, fields[2:])):
                raise ValueError('Noncanonical exponent')
            if exponents in coefficients:
                raise ValueError('Duplicate monomial')
            monomials.append(exponents)
            coefficients[exponents] = coefficient
            position += 1
        if not coefficients or monomials != sorted(monomials) or key in table:
            raise ValueError('Noncanonical sparse polynomial')
        table[key] = coefficients
    if keys != sorted(keys):
        raise ValueError('Noncanonical table order')
    return table, position


def verify(raw, output, code, expected, dimension, limit):
    prefix = b'RC1 RESULT LAW\nBEGIN_REQUEST\n' + raw + b'END_REQUEST\n'
    if not output.startswith(prefix) or not output.endswith(b'\n'):
        raise ValueError('Bad full request framing')
    lines = output[len(prefix):].decode('ascii').splitlines()
    edge_count, hybrid_count = int(raw.splitlines()[0].split()[3]), int(raw.splitlines()[0].split()[5])
    keys = [f'X:{i}' for i in range(edge_count)] + [f'G:{i}' for i in range(hybrid_count)]
    if lines[0] != 'VARIABLES ' + str(dimension) + ' ' + ' '.join(keys):
        raise ValueError('Wrong original variable registry')
    if lines[1] != 'GATE SOURCE_ADMISSION_NOT_ESTABLISHED':
        raise ValueError('Missing source gate')
    if limit:
        if code != 2 or len(lines) != 5 or lines[2] != 'STATUS UNKNOWN' or lines[4] != 'END':
            raise ValueError('Bad UNKNOWN frame')
        fields = lines[3].split(' ')
        if len(fields) != 5 or fields[:2] != ['LIMIT', limit] or int(fields[3]) <= int(fields[4]):
            raise ValueError('Wrong budget branch')
        return {'status': 'UNKNOWN', 'limit': lines[3]}
    if code != 0 or lines[2] != 'STATUS TABLE':
        raise ValueError('Expected complete table')
    rooted, at = parse_table(lines, 3, 'ROOTED', 'TREE', dimension)
    unrooted, at = parse_table(lines, at, 'UNROOTED', 'SPLIT', dimension)
    if lines[at:] != ['END'] or rooted != expected:
        raise ValueError('Closed-form rooted polynomial disagreement')
    # Every tested table has at most three copied labels, hence no nontrivial
    # unrooted cut; exact normalization must yield its single constant entry.
    if unrooted != {'[]': {(0,) * dimension: Fraction(1)}}:
        raise ValueError('Wrong full unrooted pushforward')
    return {'status': 'TABLE', 'rooted_entries': len(rooted), 'unrooted_entries': len(unrooted)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--rust', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    identities = {name: {'path': str(path.resolve()), 'sha256': sha(path)} for name, path in [('lean', args.lean), ('rust', args.rust)]}
    (args.output / 'REVIEWER.py').write_bytes(Path(__file__).read_bytes())
    (args.output / 'FORMULAS.py').write_bytes((PACKET / 'quality/law_analytic_oracle.py').read_bytes())
    rows = []
    for name, raw, expected, dimension, limit in fixtures():
        folder = args.output / name
        folder.mkdir()
        (folder / 'REQUEST.rc1').write_bytes(raw)
        outputs, codes, errors = [], [], []
        for language, binary in [('lean', args.lean), ('rust', args.rust)]:
            result = subprocess.run([str(binary.resolve())], input=raw, capture_output=True, timeout=45)
            (folder / (language + '.stdout')).write_bytes(result.stdout)
            (folder / (language + '.stderr')).write_bytes(result.stderr)
            outputs.append(result.stdout)
            codes.append(result.returncode)
        if outputs[0] != outputs[1] or codes[0] != codes[1]:
            errors.append('Native byte/exit disagreement')
        try:
            detail = verify(raw, outputs[0], codes[0], expected, dimension, limit)
        except (ValueError, IndexError, UnicodeError) as error:
            errors.append(str(error))
            detail = {}
        rows.append({'name': name, 'pass': not errors, 'errors': errors, 'return_codes': codes, 'checked': detail})
    stable = all(sha(Path(row['path'])) == row['sha256'] for row in identities.values())
    receipt = {'status': 'PASS' if stable and all(row['pass'] for row in rows) else 'FAIL',
               'cases_total': len(rows), 'cases_passed': sum(row['pass'] for row in rows),
               'identities': identities, 'identities_stable': stable, 'cases': rows,
               'scope': 'Finite native byte agreement, independent full symbolic three-sample topology formulas and canonical budget controls. No universal source-program refinement, physical/observation admission or biological accuracy.'}
    (args.output / 'RECEIPT.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in ('status', 'cases_passed', 'cases_total')}))
    return receipt['status'] != 'PASS'


if __name__ == '__main__':
    raise SystemExit(main())
