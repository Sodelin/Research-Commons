from math import gcd
M = 25 * 49
units = [p for p in range(M) if gcd(p, M) == 1]
assert len(units) == 840
seen = 0
for N in range(192 % 35, M, 35):
    A = {p for p in units if (N - p) % 25 == 0}
    B = {p for p in units if (N - p) % 49 == 0}
    assert (len(A), len(B), len(A & B), len(A | B)) == (42, 20, 1, 61)
    seen += 1
print(f"{seen} target classes mod {M}; {len(units)} reduced source classes each")
print("25-divisible: 42; 49-divisible: 20; both: 1; either: 61")
