#!/usr/bin/env python3
"""One bounded rational gate only; not a cutoff or radius evaluation."""
from fractions import Fraction as F
from pathlib import Path
import json
data=json.loads(Path(__file__).with_name('baseline-certificate.json').read_text())
b=list(map(F,data['b'])); exponents=data['Lambda']; eps=F(1,1024)
error=sum((abs(b[i])+1)*F(l*(l-1),3)*eps**(l-3)
          for i,l in enumerate(exponents) if l>=6)
assert error < -b[1]/4
print('PASS: epsilon=1/1024 satisfies the exact Jensen dominance inequality.')
print('No extraction tolerance, killing cutoff or local recognition radius evaluated.')
