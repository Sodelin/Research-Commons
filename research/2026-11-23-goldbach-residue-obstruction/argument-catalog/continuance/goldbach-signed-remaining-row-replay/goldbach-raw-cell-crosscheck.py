import csv
import math
from array import array
from pathlib import Path


def direct_cells(exponent):
    target = 1 << exponent
    root = 1 << (exponent // 2)
    q_min = math.isqrt(root)
    if q_min**4 < target:
        q_min += 1
    assert root * q_min / math.log(target)**5 < 1

    prime = bytearray(b'\1') * target
    prime[0:2] = b'\0\0'
    for p in range(2, root + 1):
        if prime[p]:
            prime[p*p::p] = b'\0' * ((target - 1 - p*p) // p + 1)
    mobius = array('b', [1]) * target
    von_mangoldt = array('d', [0.0]) * target
    for p in range(2, target):
        if not prime[p]:
            continue
        for m in range(p, target, p):
            mobius[m] = -mobius[m]
        for m in range(p*p, target, p*p):
            mobius[m] = 0
        m = p
        while m < target:
            von_mangoldt[m] = math.log(p)
            m *= p

    def interval_index(x):
        return int(x > root // 2) + int(x > root)

    direct = {f'A{i}{j}': [0.0, 0.0, 0] for i in range(3) for j in range(3)}
    first_q = q_min | 1
    for h in range(2, (target - 1) // q_min + 1):
        if not mobius[h]:
            continue
        j = interval_index(h)
        coefficient = -mobius[h] * math.log(h)
        for q in range(first_q, (target - 1) // h + 1, 2):
            m = q * h
            if not mobius[m] or not von_mangoldt[target - m]:
                continue
            weight = coefficient * von_mangoldt[target - m]
            subtotal = direct[f'A{interval_index(q)}{j}']
            subtotal[0] += weight
            subtotal[1] += abs(weight)
            subtotal[2] += 1
    return {row: (signed / target, absolute / target, count)
            for row, (signed, absolute, count) in direct.items()}


if __name__ == '__main__':
    cxx_output = Path(__file__).with_name('goldbach-raw-cell-replay.csv')
    with cxx_output.open() as file:
        rows = {(int(r['k']), r['row']): r for r in csv.DictReader(file)}
    for exponent in (20, 22):
        for cell, (signed, absolute, count) in direct_cells(exponent).items():
            r = rows[exponent, cell]
            assert count == int(r['nonzero_terms']), (exponent, cell, count, r)
            assert abs(signed - float(r['signed_per_N'])) < 1e-10, (exponent, cell, signed, r)
            assert abs(absolute - float(r['absolute_per_N'])) < 1e-10, (exponent, cell, absolute, r)
        print(f'2^{exponent}: all raw-cell counts and both weights agree')
