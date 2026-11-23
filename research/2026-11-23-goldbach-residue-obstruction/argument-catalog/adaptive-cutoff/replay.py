from fractions import Fraction as F
from random import Random

rng = Random(2923)
checks = 0
for A in map(F, (1, 2, 3, 5, 8)):
    for _ in range(100):
        data = [(F(rng.randrange(1, 180), rng.randrange(1, 30)),
                 rng.randrange(-9, 10)) for i in range(28)]
        breaks = sorted({A, 2*A} | {t for t, w in data if A < t < 2*A})
        values = [sum(w for t, w in data if (lo+hi)/2 < t)
                  for lo, hi in zip(breaks, breaks[1:])]
        exact = sum((hi-lo)*value for lo, hi, value in
                    zip(breaks, breaks[1:], values)) / A
        smooth = sum(w*min(1, max(0, (t-A)/A)) for t,w in data)
        assert exact == smooth
        assert min(values) <= exact <= max(values)
        checks += 1
print(f"{checks} exact signed cutoff identities and selection checks")
