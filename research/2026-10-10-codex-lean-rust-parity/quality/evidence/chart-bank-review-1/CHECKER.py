#!/usr/bin/env python3
"""Compare native charts; check SAT against direct physical-bank conditions.

This oracle does not compile affine rows or perform Fourier--Motzkin elimination.
Its generated chart records are evaluated directly as ages, inverse rates,
chronology, exposure durations and inheritance intervals. Exclusion certificates
remain the responsibility of the independent original-row checker.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import subprocess
from datetime import datetime, timezone


def q(value):
    value = Q(value)
    return f"{value.numerator}/{value.denominator}"


def atom(value):
    kind, value = value
    return f"V:{value}" if kind == "V" else f"Q:{q(value)}"


def bound(value):
    return "NONE" if value is None else value[0] + ":" + q(value[1])


def request(chart):
    lines = [f"RC1 CHART {chart['v']} {len(chart['edges'])} {len(chart['leaves'])} "
             f"{len(chart['hybrids'])} {len(chart['ages'])} {len(chart['exposures'])} {chart['cap']}",
             "ROOT 0"]
    lines += [f"EDGE {i} {s} {t}" for i, (s, t) in enumerate(chart['edges'])]
    lines += [f"LEAF {i} {v}" for i, v in enumerate(chart['leaves'])]
    lines += [f"HYBRID {i} {v} {a} {b}" for i, (v, a, b) in enumerate(chart['hybrids'])]
    lines += [f"AGE {cmp} {atom(left)} {atom(right)}" for cmp, left, right in chart['ages']]
    lines += [f"EXPOSURE {i} {population} {atom(young)} {atom(old)} {bound(lo)} {bound(hi)}"
              for i, (population, young, old, lo, hi) in enumerate(chart['exposures'])]
    lines += [f"COIN {i} {bound(lo)} {bound(hi)}" for i, (lo, hi) in enumerate(chart['coins'])]
    return ("\n".join(lines) + "\n").encode("ascii")


def direct_bank_check(chart, vector):
    """Inherited BankConditions, evaluated without affine-row construction."""
    nv, ne, nh = chart['v'], len(chart['edges']), len(chart['hybrids'])
    if len(vector) != nv + ne + 1 + nh:
        raise ValueError("Wrong physical bank dimension")
    ages = vector[:nv]
    inverse = vector[nv:nv + ne + 1]
    coins = vector[nv + ne + 1:]
    def value(a):
        return ages[a[1]] if a[0] == "V" else Q(a[1])
    def compare(tag, left, right):
        return left < right if tag == "LT" else left == right if tag == "EQ" else left <= right
    def interval(coordinate, lo, hi):
        return ((lo is None or compare(lo[0], Q(lo[1]), coordinate)) and
                (hi is None or compare(hi[0], coordinate, Q(hi[1]))))
    checks = {
        "edge_calendar": all(ages[t] < ages[s] for s, t in chart['edges']),
        "leaf_zero": all(ages[v] == 0 for v in chart['leaves']),
        "inverse_positive": all(u > 0 for u in inverse),
        "coin_interior": all(0 < g < 1 for g in coins),
        "chronology": all(compare(cmp, value(left), value(right))
                          for cmp, left, right in chart['ages']),
        "coin_intervals": all(interval(g, lo, hi)
                              for g, (lo, hi) in zip(coins, chart['coins']))}
    checks["exposure_intervals"] = True
    if checks['inverse_positive']:
        for pop, young, old, lo, hi in chart['exposures']:
            u = inverse[ne] if pop == "A" else inverse[int(pop[2:])]
            # Physical rate = 1/u. This is the direct original rate-duration
            # coordinate, rather than the compiler's multiplied inequality.
            exposure = (value(old) - value(young)) / u
            checks['exposure_intervals'] &= interval(exposure, lo, hi)
    else:
        checks['exposure_intervals'] = False
    return checks


def fixtures(seed, count):
    rng = random.Random(seed)
    ordinary = dict(v=3, edges=[(0, 1), (0, 2)], leaves=[1, 2], hybrids=[],
                    ages=[], exposures=[], coins=[], cap=4096)
    hybrid = dict(v=7, edges=[(0, 1), (0, 2), (1, 3), (1, 5), (2, 4), (2, 5), (5, 6)],
                  leaves=[3, 4, 6], hybrids=[(5, 3, 5)], ages=[], exposures=[],
                  coins=[(None, None)], cap=4096)
    cases = [('ordinary-bare', ordinary, "SAT"), ('hybrid-bare', hybrid, "SAT")]
    parallel = dict(v=5, edges=[(0, 1), (0, 2), (2, 3), (2, 3), (3, 4)],
                    leaves=[1, 4], hybrids=[(3, 2, 3)], ages=[], exposures=[],
                    coins=[(('LT', Q(1, 3)), ('LE', Q(2, 3)))], cap=4096)
    cases.append(('parallel-original-occurrences', parallel, "SAT"))
    fixed = deepcopy(ordinary)
    fixed['ages'] = [('EQ', ('V', 0), ('Q', Q(3, 2)))]
    fixed['exposures'] = [('E:0', ('V', 1), ('V', 0), ('LE', Q(1, 2)), ('LE', 3)),
                          ('E:1', ('Q', 0), ('V', 0), ('LT', 0), None),
                          ('A', ('V', 0), ('Q', 4), ('LE', 1), ('LE', 5)),
                          ('A', ('Q', -2), ('Q', -1), ('LT', 0), ('LT', 3))]
    cases.append(('literal-fixed-shared-ancestral', fixed, "SAT"))
    impossible = deepcopy(ordinary)
    impossible['ages'] = [('LE', ('V', 0), ('Q', 0))]
    cases.append(('ordinary-calendar-contradiction', impossible, "UNSAT"))
    bad_coin = deepcopy(hybrid)
    bad_coin['coins'] = [(('LE', 1), None)]
    cases.append(('hybrid-coin-contradiction', bad_coin, "UNSAT"))
    for i in range(count):
        chart = deepcopy(ordinary)
        root_age = Q(rng.randint(1, 8), rng.randint(1, 6))
        chart['ages'] = [('EQ', ('V', 0), ('Q', root_age))]
        for edge in range(2):
            lower = Q(rng.randint(0, 4), rng.randint(1, 5))
            upper = lower + Q(rng.randint(1, 5), rng.randint(1, 5))
            chart['exposures'].append((f'E:{edge}', ('V', edge + 1), ('V', 0),
                                       (rng.choice(['LE', 'LT']), lower),
                                       (rng.choice(['LE', 'LT']), upper)))
        chart['exposures'].append(('A', ('V', 0), ('Q', root_age + 2), ('LT', 0), None))
        cases.append((f'ordinary-random-{i:03d}', chart, "SAT"))
    return cases


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--rust', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=10102026)
    parser.add_argument('--random-cases', type=int, default=36)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'CHECKER.py').write_bytes(Path(__file__).read_bytes())
    identities = {name: {'path': str(path.resolve()), 'sha256': digest(path)}
                  for name, path in [('lean', args.lean), ('rust', args.rust)]}
    results = []
    for name, chart, expected in fixtures(args.seed, args.random_cases):
        folder = args.output / name
        folder.mkdir()
        raw = request(chart)
        (folder / 'REQUEST.rc1').write_bytes(raw)
        (folder / 'CHART-MODEL.json').write_text(json.dumps(chart, default=str, sort_keys=True, indent=2) + '\n')
        outputs, codes, failures, checks = [], [], [], {}
        for language, binary in [('lean', args.lean), ('rust', args.rust)]:
            process = subprocess.run([str(binary.resolve())], input=raw, capture_output=True, timeout=30)
            (folder / f'{language}.stdout').write_bytes(process.stdout)
            (folder / f'{language}.stderr').write_bytes(process.stderr)
            outputs.append(process.stdout)
            codes.append(process.returncode)
        if outputs[0] != outputs[1] or codes[0] != codes[1]:
            failures.append('Native byte/exit disagreement')
        text = outputs[0].decode('ascii')
        lines = text.splitlines()
        if f'STATUS {expected}' not in lines or codes[0] != 0:
            failures.append(f'Expected checked constructive case {expected}')
        if 'GATE SOURCE_ADMISSION_NOT_ESTABLISHED' not in lines:
            failures.append('Missing admission gate')
        if expected == 'SAT' and 'STATUS SAT' in lines:
            witness_line = next(line for line in lines if line.startswith('WITNESS '))
            parts = witness_line.split(' ')
            vector = [Q(item) for item in parts[2:]]
            if int(parts[1]) != len(vector):
                failures.append('Witness dimensions')
            checks = direct_bank_check(chart, vector)
            failures += [key for key, passed in checks.items() if not passed]
        results.append({'name': name, 'expected': expected, 'pass': not failures,
                        'physical_bank_checks': checks, 'failures': failures,
                        'return_codes': codes})
    controls = deepcopy(fixtures(args.seed, 0)[0][1])
    good = list(map(Q, [1, 0, 0, 1, 1, 1]))
    assert all(direct_bank_check(controls, good).values())
    bad = good.copy()
    bad[3] = 0
    assert not all(direct_bank_check(controls, bad).values())
    stable = all(digest(Path(row['path'])) == row['sha256'] for row in identities.values())
    receipt = dict(status='PASS' if stable and all(row['pass'] for row in results) else 'FAIL',
                   executed_at_utc=datetime.now(timezone.utc).isoformat(),
                   cases_passed=sum(row['pass'] for row in results), cases_total=len(results),
                   identities=identities, binary_identities_stable=stable,
                   direct_oracle_zero_inverse_control_rejected=True,
                   checker_source_sha256=digest(Path(__file__)), cases=results,
                   scope='Finite native byte agreement and direct physical-bank SAT checks; UNSAT expected controls only. No universal compiler, source-admission, Rust refinement or scientific closure claim.')
    (args.output / 'RECEIPT.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: receipt[key] for key in ('status', 'cases_passed', 'cases_total')}))
    return receipt['status'] != 'PASS'


if __name__ == '__main__':
    raise SystemExit(main())
