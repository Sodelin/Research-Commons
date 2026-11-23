#!/usr/bin/env python3
from fractions import Fraction

LIMIT = 16000
START = 1000

def main():
    spf = list(range(LIMIT + 1))
    for p in range(2, LIMIT + 1):
        if spf[p] == p:
            for n in range(p*p, LIMIT + 1, p):
                if spf[n] == n:
                    spf[n] = p
    isprime = [n >= 2 and spf[n] == n for n in range(LIMIT + 1)]
    primes = [n for n in range(2, LIMIT + 1) if isprime[n]]
    factors = [(1, n) if isprime[n] else (spf[n], n//spf[n]) if n >= 2 and isprime[n//spf[n]] else None for n in range(LIMIT + 1)]
    exponents = [(1,1),(9,10),(2,5),(1,10),(0,1)]
    records = [(Fraction(1),0,0,0) for _ in exponents]
    survivors = [0]*len(exponents)
    for N in range(START, LIMIT + 1, 2):
        p0 = 0
        b = [0]*len(exponents)
        for p in primes:
            if p > N-2:
                break
            f = factors[N-p]
            if f is None: continue
            r,q = f
            if r == 1:
                p0 += 1
            else:
                for i,(k,j) in enumerate(exponents):
                    b[i] += r**j <= q**k
        assert p0 == sum(isprime[N-p] for p in primes if p <= N-2)
        assert p0 > 0 and b[-1] == 0
        assert all(b[i] >= b[i+1] for i in range(len(b)-1))
        for i,x in enumerate(b):
            survivors[i] += bool(x)
            ratio = Fraction(p0,p0+x)
            if records[i][1] == 0 or ratio < records[i][0]:
                records[i] = (ratio,N,p0,x)
    print(f"Even N: {START}..{LIMIT} ({(LIMIT-START)//2+1} targets)")
    for (k,j), (ratio,N,p0,b), s in zip(exponents, records, survivors):
        print(f"beta={Fraction(k,j)}: targets with semiprimes={s}; min prime share={ratio}; first N={N}, prime={p0}, semiprime={b}")
if __name__ == "__main__":
    main()
