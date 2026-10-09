"""Two exact scalar identities only; not a source or flow solver."""
from fractions import Fraction as Q
from pathlib import Path
import json

z = [Q(1, 2), Q(1, 8)]
w = [Q(44, 45), Q(64, 45)]
a = Q(1, 4)
checks = []
for degree in (1, 2):
    lhs = sum(weight * ((a * value) ** degree - value ** degree)
              for value, weight in zip(z, w))
    rhs = -Q(1, 2) ** degree
    assert lhs == rhs
    checks.append({'degree': degree, 'lhs': str(lhs),
                   'rhs': str(rhs), 'pass': True})
receipt = {'kind': 'exact scalar balance check only',
           'python': 'standard-library fractions', 'checks': checks}
Path(__file__).with_name('RATIONAL-CHECK.json').write_text(
    json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
