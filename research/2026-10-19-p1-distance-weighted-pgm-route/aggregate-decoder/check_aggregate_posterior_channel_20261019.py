"""Exact rational controls for the posterior-channel identities only.

This finite check does not prove hypercontractivity, the arbitrary-N theorem,
the physical net transfer, or any P1 sample-complexity improvement.
"""
from fractions import Fraction as F
from itertools import product


def coord(r, n):
    rows = []
    for y in product((-1, 1), repeat=n):
        pp = pm = F(1)
        for x in y:
            pp *= (1+r*x)/2
            pm *= (1-r*x)/2
        rows.append((pp, pm))
    gamma = sum((pp-pm)**2/(2*(pp+pm)) for pp, pm in rows)
    harmonic = sum(2*pp*pm/(pp+pm) for pp, pm in rows)
    assert gamma + harmonic == 1
    assert harmonic >= (1-r*r)**n
    K = [[sum(row[s]*row[t]/sum(row) for row in rows)
          for t in range(2)] for s in range(2)]
    for s in range(2):
        for t in range(2):
            assert K[s][t] == (1+(gamma if s==t else -gamma))/2
    return rows, gamma, K

single = tensor = 0
for r in (F(1,4), F(1,3), F(1,2)):
    for n in range(1,9):
        rows, gamma, K = coord(r,n)
        single += 1
        if n > 4:
            continue
        states = list(product(range(2), repeat=2))
        KN = [[F(0) for _ in states] for _ in states]
        for row1 in rows:
            for row2 in rows:
                ps = [row1[s[0]]*row2[s[1]] for s in states]
                denom = sum(ps)
                for i in range(4):
                    for j in range(4):
                        KN[i][j] += ps[i]*ps[j]/denom
        for i,s in enumerate(states):
            for j,t in enumerate(states):
                assert KN[i][j] == K[s[0]][t[0]]*K[s[1]][t[1]]
        # Direct posterior second moment of one genuinely fractional function.
        q = [F(1,7), F(3,7), F(5,7), F(6,7)]
        direct = F(0)
        for row1 in rows:
            for row2 in rows:
                ps = [row1[s[0]]*row2[s[1]] for s in states]
                total = sum(ps)
                direct += sum(ps[i]*q[i] for i in range(4))**2/(4*total)
        gram = sum(q[i]*KN[i][j]*q[j] for i in range(4) for j in range(4))/4
        assert direct == gram
        tensor += 1
print(f'PASS: {single} exact one-coordinate posterior/noise/Hellinger controls')
print(f'PASS: {tensor} exact two-coordinate tensor-channel and fractional-function identities')
print('Scope: finite rational identities only; no numerical approximation or full-theorem execution.')
