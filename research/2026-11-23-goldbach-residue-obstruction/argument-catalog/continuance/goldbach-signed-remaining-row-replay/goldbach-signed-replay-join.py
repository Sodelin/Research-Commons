import csv
import json
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent
OUTER = ['A00', 'A01', 'A02', 'A10', 'A12', 'A20', 'A21']


def inputs():
    cells = defaultdict(dict)
    with (ROOT / 'goldbach-raw-cell-replay.csv').open() as file:
        for row in csv.DictReader(file):
            cells[int(row['k'])][row['row']] = float(row['signed_per_N'])
    low = {}
    for line in (ROOT / 'goldbach-low-raw-replay.tsv').read_text().splitlines():
        if line.startswith('#'):
            continue
        k, _, corr, m0lo, m0hi, actual, _, centered, *_ = line.split()
        low[int(k)] = tuple(map(float, (corr, m0lo, m0hi, actual, centered)))
    with (ROOT / 'goldbach-center-evaluator-results.jsonl').open() as file:
        center = {row['k']: row for row in map(json.loads, file)}
    return cells, low, center


def main():
    cells, low, center = inputs()
    output = csv.writer(sys.stdout, lineterminator='\n')
    output.writerow(['k', *OUTER, 'E_lo', '2S_even_sp', '2C_rest', 'R', 'R_minus_A20',
                     'A20_h_below_64', 'R_minus_A20_h_below_64', 'M0_mid',
                     'A11', 'A11_minus_2C_all'])
    for k, cell in sorted(cells.items()):
        corr, m0lo, m0hi, actual, centered = low[k]
        c = center[k]
        raw_center = c['rows']['Z1']['raw']
        sign_value = 'doubled_signed_over_N'
        assert abs(corr - cell['mobius_correlation']) < 1e-11
        assert abs(actual - cell['actual_low']) < 1e-11
        a11 = sum(row[sign_value] for row in c['raw_actual_A11'].values()) / 2
        assert abs(a11 - cell['A11']) < 1e-11
        semiprime = raw_center['even']['semiprime'][sign_value]
        higher = sum(row['higher_remainder'][sign_value] for row in raw_center.values())
        c_all = sum(piece[sign_value] for row in raw_center.values() for piece in row.values())
        r = centered + sum(cell[name] for name in OUTER) + semiprime + higher
        short_h = sum(weight for name, weight in cell.items() if name.startswith('A20_h'))
        data = [*[cell[name] for name in OUTER], centered, semiprime, higher, r,
                r - cell['A20'], short_h, r - short_h, (m0lo + m0hi) / 2, a11, a11 - c_all]
        output.writerow([k, *[f'{value:.10f}' for value in data]])


if __name__ == '__main__':
    main()
